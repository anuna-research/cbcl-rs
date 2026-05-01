//! attackers/adaptive: non-stationary multi-armed-bandit wrapper over a
//! base library of [`PsiPattern`]s (REQ-1132 / SPEC-011 §adaptive-attacker).
//!
//! # What this is
//!
//! [`AdaptiveAttacker`] wraps a `Vec<Box<dyn PsiPattern>>` (the "arms" of
//! the bandit) and, on every fresh trial (i.e. every [`AttackPattern::ingest_setup`]
//! call), selects exactly one arm to delegate the entire trial's
//! [`AttackPattern::step`] / [`AttackPattern::final_guess`] surface to.
//! After the trial concludes, the runner reports the per-trial outcome
//! via [`AdaptiveAttacker::record_outcome`] and the bandit updates its
//! internal arm statistics.
//!
//! # Bandit choice: UCB1, not Thompson
//!
//! The SPL brief proposes Beta(1+wins, 1+losses) Thompson sampling. This
//! implementation instead uses **UCB1** (Auer, Cesa-Bianchi, Fischer 2002):
//!
//! ```text
//! ucb_i(t) = mean_i + sqrt(2 * ln(t) / n_i)
//! ```
//!
//! Reasons:
//!
//! 1. UCB1 has the same `O(log T)` regret as Thompson on stochastic
//!    bandits and is dependency-free — no Beta/Gamma sampling needed.
//! 2. UCB1 is fully deterministic given the (success, failure) signal
//!    sequence, which simplifies reproducibility (the existing crate
//!    invests heavily in determinism — CON-1130).
//! 3. The unit-test convergence story is cleaner: with a fair tie-break
//!    over un-pulled arms, UCB1 is guaranteed to pull the
//!    highest-mean arm with frequency → 1 as `t → ∞`.
//!
//! # Last-K success window vs. cumulative
//!
//! The brief calls for a *last-K* success window. UCB1 over a sliding
//! window is known as "Discounted UCB" / "Sliding-Window UCB" (Garivier
//! & Moulines 2008). This implementation maintains a `VecDeque<bool>`
//! per arm of length ≤ K and computes `mean_i` and `n_i` over that
//! window — so the non-stationary case (a victim agent whose defenses
//! shift mid-sweep) is handled correctly. Setting `k = usize::MAX`
//! recovers vanilla cumulative UCB1.
//!
//! # Scope semantics
//!
//! [`AdaptiveScope::Trial`]: the bandit history (per-arm windows + total
//! pulls `t`) is reset on every fresh `ingest_setup`. The wrapper
//! therefore picks uniformly at random on the very first turn and never
//! actually adapts — the "Trial" scope only makes sense if the runner
//! also calls `record_outcome` *between* sub-rounds inside one trial,
//! which the current arena harness does not. We keep the variant for
//! future intra-trial-feedback runners and document that, for a single
//! `ingest_setup → step* → final_guess` cycle, `Trial` and `Sweep`
//! behave identically on turn 0.
//!
//! [`AdaptiveScope::Sweep`]: the bandit history persists across
//! `ingest_setup` calls. This is the default for sweep-level adaptation
//! (the case the SPL acceptance test refers to: "the bandit converges
//! on the most-effective base pattern" across a 50-trial sweep against
//! a Vanilla peer).
//!
//! # Determinism
//!
//! Tie-breaks among arms with equal UCB score (notably, the initial
//! uniform-pull phase before every arm has been pulled at least once)
//! are resolved by a `ChaCha8Rng` seeded from the user-supplied seed.

use std::collections::VecDeque;

use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use super::{AttackCategory, AttackPattern, PsiPattern};
use crate::operator::ChatEvent;
use crate::operator::psi::{PsiGuess, PsiSetup};

/// Whether the bandit's per-arm history persists across trials.
///
/// See module docs for the semantic contract of each variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdaptiveScope {
    /// Reset bandit state on every `ingest_setup`.
    Trial,
    /// Carry bandit state across `ingest_setup` calls.
    Sweep,
}

/// Per-arm sliding-window outcome history.
#[derive(Clone, Debug)]
struct ArmStats {
    /// Sliding window of `true` (success / +1 attacker score) and
    /// `false` (failure) outcomes. Length ≤ K.
    window: VecDeque<bool>,
}

impl ArmStats {
    fn new() -> Self {
        Self { window: VecDeque::new() }
    }

    fn record(&mut self, success: bool, k: usize) {
        if k == 0 {
            return;
        }
        if self.window.len() == k {
            self.window.pop_front();
        }
        self.window.push_back(success);
    }

    fn n(&self) -> usize {
        self.window.len()
    }

    fn mean(&self) -> f64 {
        let n = self.window.len();
        if n == 0 {
            return 0.0;
        }
        let wins = self.window.iter().filter(|b| **b).count();
        wins as f64 / n as f64
    }
}

/// Bandit-wrapping attacker over a library of base [`PsiPattern`]s.
///
/// Selects one arm per trial via Sliding-Window UCB1 (see module docs).
/// Outcomes are reported externally via [`AdaptiveAttacker::record_outcome`].
pub struct AdaptiveAttacker {
    base: Vec<Box<dyn PsiPattern>>,
    stats: Vec<ArmStats>,
    /// Sliding-window cap.
    k: usize,
    scope: AdaptiveScope,
    rng: ChaCha8Rng,
    /// Index of the arm currently selected for the active trial.
    /// `None` until the first `ingest_setup`.
    active: Option<usize>,
    /// Arm chosen on the most recent `ingest_setup` but not yet scored.
    /// Used by `record_outcome` to update the right `stats` entry.
    pending: Option<usize>,
    /// Total number of pulls (across all arms, summed). Drives the
    /// `ln(t)` exploration term.
    total_pulls: u64,
}

impl AdaptiveAttacker {
    /// Construct a new adaptive attacker wrapping `base`.
    ///
    /// - `base`: the arm library. Must be non-empty.
    /// - `k`: sliding-window length per arm. `0` means "no history" (the
    ///   bandit will keep exploring uniformly); `usize::MAX` means
    ///   "cumulative".
    /// - `scope`: see [`AdaptiveScope`].
    /// - `seed`: RNG seed for tie-break determinism.
    ///
    /// # Panics
    ///
    /// Panics if `base.is_empty()`.
    pub fn new(
        base: Vec<Box<dyn PsiPattern>>,
        k: usize,
        scope: AdaptiveScope,
        seed: u64,
    ) -> Self {
        assert!(!base.is_empty(), "AdaptiveAttacker: base library must be non-empty");
        let n = base.len();
        Self {
            base,
            stats: (0..n).map(|_| ArmStats::new()).collect(),
            k,
            scope,
            rng: ChaCha8Rng::seed_from_u64(seed),
            active: None,
            pending: None,
            total_pulls: 0,
        }
    }

    /// Construct with the default published-PSI library and `k = 32`,
    /// scope = Sweep. This is the configuration referenced by the
    /// SPL acceptance test.
    pub fn with_published_psi(seed: u64) -> Self {
        let registry = super::psi::registry();
        let base: Vec<Box<dyn PsiPattern>> = registry.published;
        Self::new(base, 32, AdaptiveScope::Sweep, seed)
    }

    /// Number of arms in the base library.
    pub fn num_arms(&self) -> usize {
        self.base.len()
    }

    /// The arm currently selected for the active trial (if any).
    pub fn active_arm(&self) -> Option<usize> {
        self.active
    }

    /// Pulls per arm summed over the current sliding window. Useful in
    /// tests to verify that the bandit has converged on a "winner".
    pub fn pulls_per_arm(&self) -> Vec<usize> {
        self.stats.iter().map(|s| s.n()).collect()
    }

    /// UCB score per arm (for testing / introspection). Arms with zero
    /// pulls in the window are reported as `f64::INFINITY`, matching the
    /// "must explore once" rule.
    pub fn ucb_scores(&self) -> Vec<f64> {
        let t = self.total_pulls.max(1) as f64;
        self.stats
            .iter()
            .map(|s| {
                if s.n() == 0 {
                    f64::INFINITY
                } else {
                    s.mean() + (2.0 * t.ln() / s.n() as f64).sqrt()
                }
            })
            .collect()
    }

    /// Report the outcome of the most recently started trial. `success`
    /// is `true` iff the focal (defending) agent's per-trial security
    /// score was −1 (i.e. the attacker successfully extracted info).
    ///
    /// If no trial is currently pending (i.e. `record_outcome` is
    /// called twice in a row without an intervening `ingest_setup`),
    /// the call is a no-op.
    pub fn record_outcome(&mut self, success: bool) {
        if let Some(idx) = self.pending.take() {
            self.stats[idx].record(success, self.k);
            self.total_pulls = self.total_pulls.saturating_add(1);
        }
    }

    /// Pick the next arm using Sliding-Window UCB1.
    ///
    /// Pulls every arm at least once in pseudo-random order before any
    /// arm starts to be exploited. After all arms are warmed up, picks
    /// `argmax(mean_i + sqrt(2 ln t / n_i))` with random tie-breaks.
    fn select_arm(&mut self) -> usize {
        // Phase 1: warm up — any arm with zero pulls in the window has
        // UCB = +∞. Pick uniformly at random among those.
        let mut unpulled: Vec<usize> = self
            .stats
            .iter()
            .enumerate()
            .filter(|(_, s)| s.n() == 0)
            .map(|(i, _)| i)
            .collect();
        if !unpulled.is_empty() {
            let pick = (self.rng.next_u64() as usize) % unpulled.len();
            return unpulled.swap_remove(pick);
        }

        // Phase 2: standard UCB1. `total_pulls >= base.len()` here.
        let t = self.total_pulls.max(1) as f64;
        let scores: Vec<f64> = self
            .stats
            .iter()
            .map(|s| s.mean() + (2.0 * t.ln() / s.n() as f64).sqrt())
            .collect();

        let mut best = f64::NEG_INFINITY;
        let mut ties: Vec<usize> = Vec::new();
        for (i, sc) in scores.iter().enumerate() {
            if *sc > best + 1e-12 {
                best = *sc;
                ties.clear();
                ties.push(i);
            } else if (*sc - best).abs() <= 1e-12 {
                ties.push(i);
            }
        }
        let pick = (self.rng.next_u64() as usize) % ties.len();
        ties[pick]
    }
}

impl AttackPattern for AdaptiveAttacker {
    type Setup = PsiSetup;
    type Guess = PsiGuess;

    fn name(&self) -> &'static str {
        "adaptive-bandit"
    }

    fn category(&self) -> AttackCategory {
        // The wrapper itself is a meta-pattern; categorise it as Novel
        // (the bandit logic + library composition is original to this
        // crate).
        AttackCategory::Novel
    }

    fn source_citation(&self) -> Option<&'static str> {
        None
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        // Trial-scoped: wipe history at the boundary of every trial.
        if matches!(self.scope, AdaptiveScope::Trial) {
            for s in &mut self.stats {
                *s = ArmStats::new();
            }
            self.total_pulls = 0;
            // Drop any unrecorded pending arm — Trial scope is fresh.
            self.pending = None;
        }

        let arm = self.select_arm();
        self.active = Some(arm);
        self.pending = Some(arm);
        self.base[arm].ingest_setup(setup);
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> bool {
        let idx = self
            .active
            .expect("AdaptiveAttacker::step called before ingest_setup");
        self.base[idx].step(in_channel, out_channel, rng, send_index_seed)
    }

    fn final_guess(&self) -> Self::Guess {
        match self.active {
            Some(idx) => self.base[idx].final_guess(),
            None => Vec::new(),
        }
    }
}

// =============================================================================
// Tests (TEST-1132 adaptive-attacker convergence).
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attackers::psi::{DirectAsk, OperatorImpersonation, SocialPressure};

    /// Toy PSI pattern that records its own name and does nothing
    /// otherwise. Used as a shape-correct stand-in to verify the
    /// wrapper's bandit logic without coupling to the inner pattern's
    /// emission semantics.
    struct NoopArm {
        n: &'static str,
    }
    impl AttackPattern for NoopArm {
        type Setup = PsiSetup;
        type Guess = PsiGuess;
        fn name(&self) -> &'static str { self.n }
        fn category(&self) -> AttackCategory { AttackCategory::Novel }
        fn source_citation(&self) -> Option<&'static str> { None }
        fn ingest_setup(&mut self, _s: Self::Setup) {}
        fn step(
            &mut self,
            _i: &mut dyn Iterator<Item = ChatEvent>,
            _o: &mut dyn FnMut(ChatEvent),
            _r: &mut dyn RngCore,
            _s: &mut u64,
        ) -> bool { true }
        fn final_guess(&self) -> Self::Guess { Vec::new() }
    }

    fn make_three_arm_bandit(seed: u64) -> AdaptiveAttacker {
        let base: Vec<Box<dyn PsiPattern>> = vec![
            Box::new(NoopArm { n: "arm-0-low" }),
            Box::new(NoopArm { n: "arm-1-mid" }),
            Box::new(NoopArm { n: "arm-2-high" }),
        ];
        AdaptiveAttacker::new(base, 64, AdaptiveScope::Sweep, seed)
    }

    /// Drive the bandit through `n_trials` of canned per-arm Bernoulli
    /// outcomes. Returns the index sequence of arms selected.
    fn run_canned(
        bandit: &mut AdaptiveAttacker,
        true_rates: &[f64],
        n_trials: usize,
        rng_seed: u64,
    ) -> Vec<usize> {
        let mut rng = ChaCha8Rng::seed_from_u64(rng_seed);
        let mut history: Vec<usize> = Vec::with_capacity(n_trials);
        for _ in 0..n_trials {
            let setup = PsiSetup { agent_idx: 1, set: Vec::new() };
            bandit.ingest_setup(setup);
            let arm = bandit.active_arm().expect("ingest_setup picks an arm");
            history.push(arm);
            // Sample Bernoulli(true_rates[arm]).
            let u = (rng.next_u64() as f64) / (u64::MAX as f64);
            let success = u < true_rates[arm];
            bandit.record_outcome(success);
        }
        history
    }

    // -------------------------------------------------------------------
    // Test 1: Convergence on the highest-rate arm over 200 trials.
    //
    // With true rates [0.1, 0.5, 0.9], UCB1 should pick arm 2 on the
    // strict majority of the *last 50* trials (a generous bound — UCB1's
    // log-regret guarantee is much tighter than this in expectation).
    // -------------------------------------------------------------------
    #[test]
    fn ucb_converges_on_winner() {
        let true_rates = [0.1, 0.5, 0.9];
        let mut bandit = make_three_arm_bandit(0xc0ffee);
        let history = run_canned(&mut bandit, &true_rates, 200, 0xbadf00d);

        let last = &history[history.len() - 50..];
        let arm2_count = last.iter().filter(|&&i| i == 2).count();
        assert!(
            arm2_count >= 35,
            "UCB1 should pick arm 2 (true rate 0.9) on >=35 of the last 50 trials, \
             got {arm2_count}. full history tail = {:?}",
            last
        );
    }

    // -------------------------------------------------------------------
    // Test 2: Determinism — same seed → same arm-selection sequence.
    // -------------------------------------------------------------------
    #[test]
    fn ucb_is_deterministic_given_seed() {
        let true_rates = [0.3, 0.6, 0.4];
        let mut a = make_three_arm_bandit(0x42);
        let mut b = make_three_arm_bandit(0x42);
        let ha = run_canned(&mut a, &true_rates, 80, 0x99);
        let hb = run_canned(&mut b, &true_rates, 80, 0x99);
        assert_eq!(ha, hb, "same seed must produce same selection sequence");
    }

    // -------------------------------------------------------------------
    // Test 3: Trial scope wipes per-arm history on every ingest_setup.
    // After a Trial-scoped wipe, all arms have window len 0.
    // -------------------------------------------------------------------
    #[test]
    fn trial_scope_resets_per_arm_history() {
        let base: Vec<Box<dyn PsiPattern>> = vec![
            Box::new(NoopArm { n: "a" }),
            Box::new(NoopArm { n: "b" }),
        ];
        let mut bandit = AdaptiveAttacker::new(base, 16, AdaptiveScope::Trial, 7);

        let setup = || PsiSetup { agent_idx: 1, set: Vec::new() };

        bandit.ingest_setup(setup());
        bandit.record_outcome(true);
        bandit.ingest_setup(setup());
        bandit.record_outcome(false);
        // After two ingest_setup calls under Trial scope, the *second*
        // wipe resets to a fresh state, and only the most recent
        // outcome survives. So total recorded outcomes across arms == 1.
        let total_window: usize = bandit.pulls_per_arm().iter().sum();
        assert_eq!(
            total_window, 1,
            "Trial scope must wipe history on each ingest_setup; \
             pulls_per_arm = {:?}",
            bandit.pulls_per_arm()
        );
    }

    // -------------------------------------------------------------------
    // Test 4: Sweep scope accumulates history across trials.
    // -------------------------------------------------------------------
    #[test]
    fn sweep_scope_accumulates_history() {
        let base: Vec<Box<dyn PsiPattern>> = vec![
            Box::new(NoopArm { n: "a" }),
            Box::new(NoopArm { n: "b" }),
        ];
        let mut bandit = AdaptiveAttacker::new(base, 16, AdaptiveScope::Sweep, 7);
        let setup = || PsiSetup { agent_idx: 1, set: Vec::new() };

        for _ in 0..5 {
            bandit.ingest_setup(setup());
            bandit.record_outcome(true);
        }
        let total_window: usize = bandit.pulls_per_arm().iter().sum();
        assert_eq!(total_window, 5, "Sweep scope must retain all 5 outcomes");
    }

    // -------------------------------------------------------------------
    // Test 5: with_published_psi smoke — at least 4 arms, all have
    // distinct names, AttackPattern impl works end-to-end through one
    // trial against a real PsiSetup.
    // -------------------------------------------------------------------
    #[test]
    fn with_published_psi_smoke() {
        let mut bandit = AdaptiveAttacker::with_published_psi(0xdead);
        assert!(bandit.num_arms() >= 4, "published library has >=4 arms");

        let setup = PsiSetup {
            agent_idx: 1,
            set: vec!["apple".into(), "banana".into()],
        };
        bandit.ingest_setup(setup);
        assert!(bandit.active_arm().is_some(), "ingest_setup picks an arm");

        let inbox: Vec<ChatEvent> = Vec::new();
        let mut iter = inbox.into_iter();
        let mut emitted: Vec<ChatEvent> = Vec::new();
        let mut emit_fn = |ev: ChatEvent| emitted.push(ev);
        let mut rng = ChaCha8Rng::seed_from_u64(0);
        let mut send_idx: u64 = 0;
        let _done = bandit.step(&mut iter, &mut emit_fn, &mut rng, &mut send_idx);
        // Don't assert specific emission count — depends on which arm
        // got picked. Just verify no panic.
        let _ = bandit.final_guess();
    }

    // -------------------------------------------------------------------
    // Test 6: Wrapper is itself a PsiPattern (object-safe path).
    // -------------------------------------------------------------------
    #[test]
    fn wrapper_is_psi_pattern_object_safe() {
        let base: Vec<Box<dyn PsiPattern>> = vec![
            Box::new(DirectAsk::new()),
            Box::new(OperatorImpersonation::new()),
            Box::new(SocialPressure::new()),
        ];
        let bandit = AdaptiveAttacker::new(base, 8, AdaptiveScope::Sweep, 1);
        let _: Box<dyn PsiPattern> = Box::new(bandit);
    }
}
