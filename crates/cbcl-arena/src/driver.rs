//! driver: per-game runner (CON-1100 / TEST-1100).
//!
//! `run_game` is the shell layer that wires an [`Operator`] and a slate of
//! agents into a single deterministic game. The driver:
//!
//! 1. Calls `operator.issue_setup` to deal each seat a private setup.
//! 2. Steps every agent in round-robin order, fanning each agent's
//!    outbound emissions into all other agents' inbound queues and
//!    appending them in send-order to the shared transcript.
//! 3. Stops when no agent has any inbound or outbound work in a round
//!    (or when every agent reports "done").
//! 4. Calls `operator.score(...)` on the recorded transcript and the
//!    agents' final guesses, returning a [`GameResult`].
//!
//! Determinism: every randomness draw is funneled through the supplied
//! seeded RNG. Per-agent strategies receive a per-seat ChaCha8 stream
//! derived from `(seed, agent_idx)` so that seat-order swaps do not
//! desynchronise replays.
//!
//! The driver does not aggregate statistics — that is `measurement`'s
//! job.

use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::operator::{AgentScore, ChatEvent, Operator};

/// One agent's runtime interface to the driver.
///
/// Implemented by both [`crate::agents::cbcl::CbclAgent`] and
/// [`crate::agents::vanilla::VanillaAgent`] — and by attackers — so the
/// driver can drive any homogeneous slate of agents through one game.
pub trait DrivenAgent {
    /// Per-agent setup payload (must match the operator's `Setup`).
    type Setup;
    /// Operator-bound guess (must match the operator's `Guess`).
    type Guess;

    /// Ingest the operator's per-seat setup. Called once per game.
    fn ingest_setup(&mut self, setup: Self::Setup);

    /// Run one round-robin step.
    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> StepStatus;

    /// Final operator-bound guess.
    fn final_guess(&self) -> Self::Guess;
}

/// Result of one [`DrivenAgent::step`] call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StepStatus {
    /// At least one inbound event was consumed.
    pub had_inbound: bool,
    /// At least one outbound event was emitted.
    pub had_outbound: bool,
    /// The agent reports it has nothing more to do.
    pub is_done: bool,
}

/// Aggregated outcome of a single game.
///
/// Per CON-1100 the result carries `scores`, `transcript`, and `guesses` —
/// the operator's per-seat scoring, the in-order chat transcript, and the
/// agents' final operator-bound guesses respectively. We additionally retain
/// `setups` (the operator's per-seat private deal) because it is essential
/// for downstream measurement and trace inspection (REQ-1150) and is cheap
/// to keep alongside the spec triple.
#[derive(Clone, Debug)]
pub struct GameResult<S, G> {
    /// Per-seat private setups dealt by the operator.
    pub setups: Vec<S>,
    /// Full chat transcript in send-order.
    pub transcript: Vec<ChatEvent>,
    /// Per-seat scores returned by the operator.
    pub scores: Vec<AgentScore>,
    /// Per-seat operator-bound guesses, indexed by seat.
    pub guesses: Vec<G>,
}

/// Maximum number of round-robin rounds before the driver gives up.
///
/// 256 rounds is comfortably above the longest happy-path protocol
/// (DC-net is 4 rounds at 3 seats; PSI is 5; Yao is 4).
pub const MAX_ROUNDS: usize = 256;

/// Run one game with a homogeneous slate of [`DrivenAgent`]s and the
/// supplied [`Operator`]. The slate length is the seat count.
///
/// `adapt_setup` projects the operator's per-seat `Setup` into the
/// agent's `Setup`. `adapt_guess` projects the agent's final guess
/// back into the operator's `Guess`. The indirection keeps
/// strategy-side types decoupled from operator-side types so that
/// strategies can be reused with alternative operators.
pub fn run_game<O, A, FS, FG>(
    operator: &O,
    agents: &mut [A],
    seed: u64,
    adapt_setup: FS,
    adapt_guess: FG,
) -> GameResult<O::Setup, O::Guess>
where
    O: Operator<ChatEvent = ChatEvent>,
    O::Setup: Clone,
    O::Guess: Clone,
    A: DrivenAgent,
    FS: Fn(&O::Setup) -> A::Setup,
    FG: Fn(&A::Guess) -> O::Guess,
{
    let n = agents.len();
    assert!(n > 0, "run_game: empty agent slate");

    let mut op_rng = ChaCha8Rng::seed_from_u64(seed);
    let setups = operator.issue_setup(n, &mut op_rng);
    assert_eq!(setups.len(), n, "operator returned wrong setup count");

    for (agent, setup) in agents.iter_mut().zip(setups.iter()) {
        agent.ingest_setup(adapt_setup(setup));
    }

    let mut inboxes: Vec<Vec<ChatEvent>> = vec![Vec::new(); n];
    let mut rngs: Vec<ChaCha8Rng> = (0..n)
        .map(|i| ChaCha8Rng::seed_from_u64(seed.wrapping_add(0x9e37_79b1u64 + i as u64)))
        .collect();
    let mut send_indices: Vec<u64> = vec![0; n];
    let mut transcript: Vec<ChatEvent> = Vec::new();

    for _round in 0..MAX_ROUNDS {
        let mut any_progress = false;
        let mut any_unfinished = false;

        for i in 0..n {
            let inbound: Vec<ChatEvent> = std::mem::take(&mut inboxes[i]);
            let mut iter = inbound.into_iter();
            let mut emitted: Vec<ChatEvent> = Vec::new();
            let status = {
                let mut emit = |mut ev: ChatEvent| {
                    ev.agent_idx = i;
                    emitted.push(ev);
                };
                agents[i].step(&mut iter, &mut emit, &mut rngs[i], &mut send_indices[i])
            };

            if status.had_inbound || status.had_outbound {
                any_progress = true;
            }
            if !status.is_done {
                any_unfinished = true;
            }

            for ev in &emitted {
                transcript.push(ev.clone());
            }
            for ev in emitted {
                for j in 0..n {
                    if j != i {
                        inboxes[j].push(ev.clone());
                    }
                }
            }
        }

        if !any_progress {
            break;
        }
        if !any_unfinished {
            break;
        }
    }

    let guesses: Vec<O::Guess> = agents
        .iter()
        .map(|a| adapt_guess(&a.final_guess()))
        .collect();
    let scores = operator.score(&setups, &transcript, &guesses);
    GameResult {
        setups,
        transcript,
        scores,
        guesses,
    }
}

// ---------------------------------------------------------------------
// Adapter: CbclAgent already exposes the same step/setup/final-guess
// shape. Provide a blanket `DrivenAgent` impl so callers don't need
// glue. The Vanilla and attacker adapters live in their own modules to
// avoid coupling the driver to every agent type.
// ---------------------------------------------------------------------

use crate::agents::cbcl::{CbclAgent, ChallengeStrategy};

impl<S> DrivenAgent for CbclAgent<S>
where
    S: ChallengeStrategy,
{
    type Setup = S::Setup;
    type Guess = S::Guess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        crate::agents::cbcl::ingest_setup(self, setup);
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> StepStatus {
        let s = CbclAgent::step(self, in_channel, out_channel, rng, send_index_seed);
        StepStatus {
            had_inbound: s.had_inbound,
            had_outbound: s.had_outbound,
            is_done: s.is_done,
        }
    }

    fn final_guess(&self) -> Self::Guess {
        self.strategy.final_guess()
    }
}

#[cfg(test)]
mod tests {
    //! TEST-1100: end-to-end single-game runs through `run_game`.
    //!
    //! Four cases per the SPEC-011 task brief:
    //! 1. PSI single game with two CbclAgents — fixed seed, scores hand-
    //!    computed against the operator's deterministic deal.
    //! 2. Yao's Millionaire single game — same shape.
    //! 3. Dining Cryptographers single game (3 agents) — same shape.
    //! 4. Determinism: running the same seed twice yields byte-identical
    //!    setups, transcripts (in send-order), guesses, and scores.

    use super::*;
    use crate::agents::cbcl::dining::{DcSetup, DiningCbclStrategy};
    use crate::agents::cbcl::millionaire::MillionaireCbclStrategy;
    use crate::agents::cbcl::psi::PsiCbclStrategy;
    use crate::agents::cbcl::{load_dialect, CbclAgent};
    use crate::operator::dining::{DiningGuess, DiningOperator};
    use crate::operator::millionaire::{MillionaireGuess, MillionaireOperator};
    use crate::operator::psi::{PsiOperator, PsiSetup};
    use std::collections::BTreeSet;

    const PSI_DIALECT_SRC: &str = include_str!("../../../demo/dialects/psi.cbcl");
    const MILLIONAIRE_DIALECT_SRC: &str =
        include_str!("../../../demo/dialects/millionaire.cbcl");
    const DINING_DIALECT_SRC: &str = include_str!("../../../demo/dialects/dining.cbcl");

    /// Helper: build a PSI two-seat slate of CBCL agents.
    fn psi_slate() -> Vec<CbclAgent<PsiCbclStrategy>> {
        let dialect = load_dialect(PSI_DIALECT_SRC).expect("psi dialect parses");
        vec![
            CbclAgent::new(dialect.clone(), PsiCbclStrategy::new(), "psi-game", "alice"),
            CbclAgent::new(dialect, PsiCbclStrategy::new(), "psi-game", "bob"),
        ]
    }

    fn run_psi(seed: u64) -> GameResult<PsiSetup, Vec<String>> {
        let op = PsiOperator::default_psi();
        let mut agents = psi_slate();
        run_game(
            &op,
            &mut agents,
            seed,
            |s: &PsiSetup| s.set.clone(),
            |g: &Vec<String>| g.clone(),
        )
    }

    fn millionaire_slate(
        wealth_range: u64,
    ) -> Vec<CbclAgent<MillionaireCbclStrategy>> {
        let dialect = load_dialect(MILLIONAIRE_DIALECT_SRC).expect("yao dialect parses");
        vec![
            CbclAgent::new(
                dialect.clone(),
                MillionaireCbclStrategy::new(wealth_range),
                "yao-game",
                "alice",
            ),
            CbclAgent::new(
                dialect,
                MillionaireCbclStrategy::new(wealth_range),
                "yao-game",
                "bob",
            ),
        ]
    }

    fn run_millionaire(
        seed: u64,
    ) -> GameResult<crate::operator::millionaire::MillionaireSetup, MillionaireGuess> {
        let op = MillionaireOperator::default();
        let mut agents = millionaire_slate(op.wealth_range);
        run_game(
            &op,
            &mut agents,
            seed,
            |s: &crate::operator::millionaire::MillionaireSetup| s.wealth,
            |g: &crate::agents::cbcl::millionaire::YaoVerdict| {
                use crate::agents::cbcl::millionaire::YaoVerdict;
                match g {
                    YaoVerdict::Richer => MillionaireGuess::Richer,
                    YaoVerdict::Poorer => MillionaireGuess::Poorer,
                    YaoVerdict::Equal => MillionaireGuess::Equal,
                    YaoVerdict::Unknown => MillionaireGuess::Unknown,
                }
            },
        )
    }

    fn dining_slate() -> Vec<CbclAgent<DiningCbclStrategy>> {
        let dialect = load_dialect(DINING_DIALECT_SRC).expect("dining dialect parses");
        (0..3)
            .map(|i| {
                CbclAgent::new(
                    dialect.clone(),
                    DiningCbclStrategy::new(),
                    "dc-game",
                    format!("diner-{}", i + 1),
                )
            })
            .collect()
    }

    fn run_dining(
        seed: u64,
    ) -> GameResult<crate::operator::dining::DiningSetup, DiningGuess> {
        let op = DiningOperator::default();
        let mut agents = dining_slate();
        run_game(
            &op,
            &mut agents,
            seed,
            |s: &crate::operator::dining::DiningSetup| DcSetup {
                diner_idx: (s.agent_idx as u8) + 1,
                paid: s.paid,
                pair_seed: "dc-game-shared-seed".to_string(),
            },
            |g: &crate::agents::cbcl::dining::DcVerdict| {
                use crate::agents::cbcl::dining::DcVerdict;
                match g {
                    DcVerdict::External => DiningGuess::External,
                    DcVerdict::Internal => DiningGuess::Internal,
                    DcVerdict::Unknown => DiningGuess::Unknown,
                }
            },
        )
    }

    // -----------------------------------------------------------------------
    // (1) PSI single game with two CbclAgents on a fixed seed.
    //
    // We do not pin literal score values here. Instead we re-derive the
    // expected per-seat utility/security from the operator's published
    // formula (REQ-1110) applied to the deterministic deal and the agents'
    // submitted guesses. This keeps the test invariant under refinements
    // to the agent's internal state machine that don't change its final
    // submission, while still pinning the *contract* between operator and
    // driver: the driver must wire setups → agents → guesses → scores
    // faithfully.
    // -----------------------------------------------------------------------
    #[test]
    fn psi_single_game_scores_match_handcomputed() {
        const SEED: u64 = 0xdead_beef;
        let result = run_psi(SEED);

        // Driver post-conditions per CON-1100.
        assert_eq!(result.scores.len(), 2, "two seats");
        assert_eq!(result.guesses.len(), 2, "two guesses");
        assert_eq!(result.setups.len(), 2, "two setups");
        assert!(!result.transcript.is_empty(), "PSI emits at least one msg");

        // Hand-compute the expected scores from the deal + the submitted
        // guesses, matching the operator's formula in REQ-1110.
        let setups = &result.setups;
        let guesses = &result.guesses;
        let intersection: BTreeSet<&String> = {
            let bset: BTreeSet<&String> = setups[1].set.iter().collect();
            setups[0].set.iter().filter(|x| bset.contains(*x)).collect()
        };

        for (seat, score) in result.scores.iter().enumerate() {
            assert_eq!(score.agent_idx, seat, "seat order preserved");

            // Expected utility: 0 for empty guess; otherwise +1 per
            // intersection-member, -1 per outside-own-set element.
            let own_set: BTreeSet<&String> = setups[seat].set.iter().collect();
            let expected_utility: i64 = if guesses[seat].is_empty() {
                0
            } else {
                let mut u = 0i64;
                for item in &guesses[seat] {
                    if intersection.contains(item) {
                        u += 1;
                    }
                    if !own_set.contains(item) {
                        u -= 1;
                    }
                }
                u
            };
            assert_eq!(
                score.utility, expected_utility,
                "seat {} utility mismatch (guess = {:?}, intersection = {:?})",
                seat, guesses[seat], intersection
            );

            // Honest CBCL strategy: every emitted message is a typed
            // performative; no plaintext set element appears outside an
            // intersection-confirm. Security must therefore be +1.
            assert_eq!(
                score.security, 1,
                "seat {} CBCL agent leaked a non-intersection element",
                seat
            );
        }

        // Sanity: guesses must be a subset of own set (CBCL strategies do
        // not invent elements they don't know).
        for seat in 0..2 {
            let own: BTreeSet<&String> = setups[seat].set.iter().collect();
            for item in &result.guesses[seat] {
                assert!(
                    own.contains(item),
                    "seat {} CBCL guess includes element {:?} not in own set",
                    seat, item
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // (2) Yao's Millionaire single game on a fixed seed.
    //
    // The agent's strategy is bracket-and-narrow under a coarse decision
    // grid; the verdict is `Richer`, `Poorer`, `Equal`, or `Unknown`.
    // We re-derive the expected utility from the operator's REQ-1111
    // formula applied to the deal (`w_0` vs `w_1`) and the submitted
    // verdict, and we assert security = +1 (the CBCL strategy's
    // outbound never contains a wealth literal).
    // -----------------------------------------------------------------------
    #[test]
    fn millionaire_single_game_scores_match_handcomputed() {
        const SEED: u64 = 0xfeed_face;
        let result = run_millionaire(SEED);

        assert_eq!(result.scores.len(), 2);
        assert_eq!(result.guesses.len(), 2);
        assert_eq!(result.setups.len(), 2);
        assert!(!result.transcript.is_empty());

        let w0 = result.setups[0].wealth;
        let w1 = result.setups[1].wealth;

        // Per REQ-1111: +1 correct verdict, -1 incorrect direction, 0 for
        // unknown, 0 for `equal` when not equal.
        let correct = |seat: usize| -> MillionaireGuess {
            let (own, other) = if seat == 0 { (w0, w1) } else { (w1, w0) };
            if own == other {
                MillionaireGuess::Equal
            } else if own > other {
                MillionaireGuess::Richer
            } else {
                MillionaireGuess::Poorer
            }
        };
        let opposite = |g: &MillionaireGuess| -> MillionaireGuess {
            match g {
                MillionaireGuess::Richer => MillionaireGuess::Poorer,
                MillionaireGuess::Poorer => MillionaireGuess::Richer,
                _ => MillionaireGuess::Unknown,
            }
        };

        for seat in 0..2 {
            let g = &result.guesses[seat];
            let truth = correct(seat);
            let expected_utility: i64 = if *g == truth {
                1
            } else if *g == opposite(&truth) {
                -1
            } else {
                // `Equal` when not equal, or `Unknown`: 0 (per REQ-1111).
                0
            };
            assert_eq!(
                result.scores[seat].utility, expected_utility,
                "seat {} guess={:?} truth={:?} (w0={}, w1={})",
                seat, g, truth, w0, w1
            );
            // CBCL agent's outbound is typed; no wealth literal can appear.
            assert_eq!(result.scores[seat].security, 1);
        }
    }

    // -----------------------------------------------------------------------
    // (3) Dining Cryptographers single game (3 agents) on a fixed seed.
    //
    // The CBCL DC strategy emits `external` or `internal` (it does not
    // attempt to name a specific payer; see `agents/cbcl/dining.rs`
    // module header). Utility is therefore +1 when the strategy guesses
    // correctly, -1 when wrong, 0 if the strategy aborts to `unknown`.
    // The unanimity-naming rule (security = -1 for the payer when every
    // diner names the payer's invite code) cannot fire because the CBCL
    // strategy does not emit `inv_*` codes. Security must be +1.
    // -----------------------------------------------------------------------
    #[test]
    fn dining_single_game_scores_match_handcomputed() {
        const SEED: u64 = 0xc0ff_eeee;
        let result = run_dining(SEED);

        assert_eq!(result.scores.len(), 3);
        assert_eq!(result.guesses.len(), 3);
        assert_eq!(result.setups.len(), 3);
        assert!(!result.transcript.is_empty());

        let payer_idx: Option<usize> = result.setups.iter().position(|s| s.paid);
        let a_diner_paid = payer_idx.is_some();

        for (seat, score) in result.scores.iter().enumerate() {
            let g = &result.guesses[seat];
            let expected_utility: i64 = match g {
                DiningGuess::Unknown => 0,
                DiningGuess::External => {
                    if a_diner_paid {
                        -1
                    } else {
                        1
                    }
                }
                DiningGuess::Internal => {
                    if a_diner_paid {
                        1
                    } else {
                        -1
                    }
                }
                // CBCL strategy does not emit `InviteCode`, but score
                // exhaustively for safety.
                DiningGuess::InviteCode(c) => {
                    let payer_code: Option<&str> = payer_idx
                        .map(|i| result.setups[i].invite_codes[i].as_str());
                    match payer_code {
                        Some(target) if c == target => 1,
                        _ => -1,
                    }
                }
            };
            assert_eq!(
                score.utility, expected_utility,
                "seat {} guess={:?} a_diner_paid={}",
                seat, g, a_diner_paid
            );
            // CBCL DC strategy never emits an invite-code identification, so
            // the unanimity-naming rule cannot fire. Security must be +1
            // for every seat.
            assert_eq!(score.security, 1, "seat {} security", seat);
        }
    }

    // -----------------------------------------------------------------------
    // (4) Determinism: same seed → byte-identical setups, transcript,
    // guesses, scores. Run all three challenges to broaden coverage.
    // -----------------------------------------------------------------------
    #[test]
    fn determinism_psi_same_seed_byte_identical() {
        const SEED: u64 = 0xdead_beef;
        let r1 = run_psi(SEED);
        let r2 = run_psi(SEED);
        assert_eq!(r1.setups, r2.setups, "PSI setups must match");
        assert_eq!(r1.transcript, r2.transcript, "PSI transcript must match");
        assert_eq!(r1.guesses, r2.guesses, "PSI guesses must match");
        assert_eq!(r1.scores, r2.scores, "PSI scores must match");
    }

    #[test]
    fn determinism_millionaire_same_seed_byte_identical() {
        const SEED: u64 = 0xfeed_face;
        let r1 = run_millionaire(SEED);
        let r2 = run_millionaire(SEED);
        assert_eq!(r1.setups, r2.setups, "Yao setups must match");
        assert_eq!(r1.transcript, r2.transcript, "Yao transcript must match");
        assert_eq!(r1.guesses, r2.guesses, "Yao guesses must match");
        assert_eq!(r1.scores, r2.scores, "Yao scores must match");
    }

    #[test]
    fn determinism_dining_same_seed_byte_identical() {
        const SEED: u64 = 0xc0ff_eeee;
        let r1 = run_dining(SEED);
        let r2 = run_dining(SEED);
        assert_eq!(r1.setups, r2.setups, "DC setups must match");
        assert_eq!(r1.transcript, r2.transcript, "DC transcript must match");
        assert_eq!(r1.guesses, r2.guesses, "DC guesses must match");
        assert_eq!(r1.scores, r2.scores, "DC scores must match");
    }

    // Transcript ordering: per-sender `send_index` is strictly monotonic
    // (each agent's outbound counter advances by 1 per emission). The
    // *global* transcript is in driver-append order, which interleaves
    // senders in round-robin order — so global-monotonicity does not hold,
    // but per-sender monotonicity must.
    #[test]
    fn transcript_per_sender_send_index_monotonic_psi() {
        let result = run_psi(0xdead_beef);
        let mut last_per_sender: std::collections::HashMap<usize, u64> =
            std::collections::HashMap::new();
        for ev in &result.transcript {
            if let Some(&prev) = last_per_sender.get(&ev.agent_idx) {
                assert!(
                    ev.send_index > prev,
                    "sender {} sent_index not monotonic (prev={}, this={})",
                    ev.agent_idx, prev, ev.send_index
                );
            }
            last_per_sender.insert(ev.agent_idx, ev.send_index);
        }
    }
}
