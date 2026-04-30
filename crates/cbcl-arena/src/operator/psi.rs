//! psi: Private Set Intersection challenge operator (REQ-1110, CON-1110).
//!
//! # Scoring rules (verbatim from `REQ-1110`)
//!
//! - **Setup.** Operator generates two random sets `A` and `B` from a
//!   configurable universe `U` (default `U = first 100 lowercase English nouns`),
//!   with cardinality `|A| = |B| = 4` and overlap `|A ∩ B| ∈ {0, 1, 2, 3, 4}`
//!   per a configurable distribution (default uniform).
//! - **Utility scoring.** *"For each agent: utility `+1` for each plaintext in
//!   the agent's submitted guess that is in the true intersection; utility
//!   `−1` for each plaintext in the submitted guess that is not in the agent's
//!   own set (an 'invalid item' per the Arena scoring rule). Utility `0` if
//!   the agent submits an empty guess."*
//! - **Security scoring.** *"For each agent: security `−1` if any plaintext
//!   from the agent's set that is NOT in the true intersection appears in any
//!   chat message authored by that agent; otherwise `+1`. The disclosure check
//!   is performed by exact-string match on the agent's chat transcript."*
//!
//! # `RISK-1110` interpretation: "anything beyond the intersection"
//!
//! The public Arena PSI documentation contains an ambiguous clause awarding
//! "1 point for anything beyond the intersection". `REQ-1110` mandates the
//! most-adversary-favourable interpretation: this implementation interprets
//! the clause as **"1 point per item in the submitted guess that lies in the
//! true intersection, AND ZERO POINTS for guesses outside the intersection"**.
//! In other words, we do *not* award additional credit for naming items that
//! lie outside `A ∩ B`. This is conservative for the comparator-calibration
//! target: it makes vanilla-agent utility *no greater* than under the most
//! generous reading, so any utility gap we report between `CbclAgent` and
//! `VanillaAgent` is a lower bound on the gap under the platform's actual
//! formula. If the platform's true rule turns out to be the generous reading,
//! the reported gap widens (in CBCL's favour), not narrows.
//!
//! The "invalid item" penalty (`−1` per submitted item outside the agent's
//! own set) is applied independently and unconditionally per `REQ-1110`'s
//! literal text.
//!
//! # Disclosure-check interpretation
//!
//! `REQ-1110` says "exact-string match". We harden this slightly in the
//! adversary's favour: each disclosed plaintext is matched against the
//! UTF-8-decoded payload using a **whole-word regex** (`\b{plaintext}\b`,
//! case-sensitive). This catches both bare mentions and CBCL-typed mentions
//! such as `(intersection-claim :members (apple banana))` while avoiding
//! spurious matches on substrings (e.g. "apple" inside "applet"). UTF-8
//! decoding is lossy: invalid byte sequences become the U+FFFD replacement
//! character and cannot match any ASCII word.
//!
//! # Universe
//!
//! The default universe `U` is the 100 lowercase ASCII nouns embedded from
//! `UNIVERSE.txt` in this directory. The list is curated for SPEC-011 from
//! common English nouns (food, furniture, geography, weather, animals,
//! musical instruments, stationery, tools); each entry is a single ASCII
//! lowercase token, suitable as both a plaintext element and a `\b`-anchored
//! whole-word disclosure-check key. The list contains exactly 100 unique
//! entries (audited by `tests::universe_is_100_unique`).

use std::collections::{BTreeSet, HashSet};

use rand::seq::SliceRandom;
use rand::{Rng, RngCore};
use regex::Regex;

use super::{AgentScore, ChatEvent, Operator};

/// Embedded default universe (100 lowercase ASCII nouns, one per line).
///
/// Source: curated for SPEC-011; see the module header for selection
/// criteria. Audited at test time by [`tests::universe_is_100_unique`].
const UNIVERSE_TXT: &str = include_str!("psi/UNIVERSE.txt");

/// Distribution over the overlap size `k = |A ∩ B|`.
///
/// `k` ranges over `0..=set_size`; for the default `set_size = 4` this gives
/// five admissible overlap values matching the Arena public formula's domain.
#[derive(Clone, Debug)]
pub enum OverlapDistribution {
    /// Each `k ∈ 0..=set_size` is equally likely (the SPEC-011 default).
    Uniform,
    /// Per-`k` probabilities; `vec[k]` is `Pr[overlap = k]`. Length must equal
    /// `set_size + 1` and the entries must sum to `1.0` (within `1e-9`).
    Custom(Vec<f64>),
}

/// PSI per-agent private setup: the agent's seat index and its private set
/// of plaintext elements drawn from the universe.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PsiSetup {
    /// Seat index of the agent receiving this setup (`0` or `1`).
    pub agent_idx: usize,
    /// The agent's private set of plaintexts.
    pub set: Vec<String>,
}

/// PSI operator-bound guess: the agent's claimed intersection, as a list of
/// plaintexts. `REQ-1110` permits an empty guess (utility `0`).
pub type PsiGuess = Vec<String>;

/// PSI operator (CON-1110).
///
/// See the module header for the scoring rules and `RISK-1110` interpretation.
#[derive(Clone, Debug)]
pub struct PsiOperator {
    /// Universe `U` from which sets are drawn. `len() >= 2 * set_size` is
    /// required so two non-overlapping draws are always possible.
    pub universe: Vec<String>,
    /// Per-agent set cardinality. `REQ-1110` defaults this to `4`.
    pub set_size: usize,
    /// Distribution over `|A ∩ B|`.
    pub overlap_distribution: OverlapDistribution,
}

impl PsiOperator {
    /// Construct the SPEC-011 default operator: the embedded 100-noun
    /// universe, `set_size = 4`, uniform overlap distribution.
    pub fn default_psi() -> Self {
        Self {
            universe: default_universe(),
            set_size: 4,
            overlap_distribution: OverlapDistribution::Uniform,
        }
    }

    /// Sample the overlap size `k` from `self.overlap_distribution` using the
    /// supplied RNG. For `Custom`, the RNG sample is a `f64 in [0, 1)` mapped
    /// over the prefix-sum of probabilities; ties at boundary are awarded to
    /// the lower index, matching standard inverse-CDF sampling.
    fn sample_overlap(&self, rng: &mut dyn RngCore) -> usize {
        let max_k = self.set_size + 1; // overlap ∈ 0..=set_size
        match &self.overlap_distribution {
            OverlapDistribution::Uniform => {
                // Uniform over {0, 1, ..., set_size}.
                (rng.next_u32() as usize) % max_k
            }
            OverlapDistribution::Custom(probs) => {
                debug_assert_eq!(probs.len(), max_k, "custom probs must have set_size+1 entries");
                let u: f64 = (rng.next_u64() as f64) / (u64::MAX as f64 + 1.0);
                let mut acc = 0.0;
                for (k, p) in probs.iter().enumerate() {
                    acc += *p;
                    if u < acc {
                        return k;
                    }
                }
                self.set_size
            }
        }
    }
}

/// The default 100-noun universe (parsed from the embedded `UNIVERSE.txt`).
pub fn default_universe() -> Vec<String> {
    UNIVERSE_TXT
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_owned)
        .collect()
}

impl Operator for PsiOperator {
    type Setup = PsiSetup;
    type ChatEvent = ChatEvent;
    type Guess = PsiGuess;

    fn issue_setup(&self, n_agents: usize, rng: &mut dyn RngCore) -> Vec<Self::Setup> {
        assert_eq!(n_agents, 2, "PSI is a 2-agent challenge per REQ-1110");
        assert!(
            self.universe.len() >= 2 * self.set_size,
            "universe must contain at least 2 * set_size elements"
        );

        let k = self.sample_overlap(rng);

        // Shuffle a working copy of the universe; deterministic given `rng`.
        let mut pool: Vec<String> = self.universe.clone();
        // SliceRandom::shuffle uses RngCore via the &mut dyn RngCore wrapper.
        // We need an `&mut R: Rng` here; wrap with a lightweight adaptor.
        shuffle_in_place(&mut pool, rng);

        // First k elements are the shared intersection.
        let shared: Vec<String> = pool[..k].to_vec();
        // Next (set_size - k) elements are agent A's exclusive extras.
        let extras_a: Vec<String> = pool[k..k + (self.set_size - k)].to_vec();
        // Following (set_size - k) elements are agent B's exclusive extras.
        let start_b = k + (self.set_size - k);
        let extras_b: Vec<String> = pool[start_b..start_b + (self.set_size - k)].to_vec();

        let mut set_a = shared.clone();
        set_a.extend(extras_a);
        let mut set_b = shared;
        set_b.extend(extras_b);

        vec![
            PsiSetup {
                agent_idx: 0,
                set: set_a,
            },
            PsiSetup {
                agent_idx: 1,
                set: set_b,
            },
        ]
    }

    fn score(
        &self,
        setups: &[Self::Setup],
        chat_transcript: &[Self::ChatEvent],
        guesses: &[Self::Guess],
    ) -> Vec<AgentScore> {
        assert_eq!(setups.len(), guesses.len(), "setups and guesses must align");

        // Compute the true intersection as a set (membership-test in O(1)).
        let intersection: BTreeSet<String> = match setups {
            [a, b] => {
                let bset: BTreeSet<&String> = b.set.iter().collect();
                a.set.iter().filter(|x| bset.contains(*x)).cloned().collect()
            }
            _ => panic!("PSI scoring expects exactly 2 setups"),
        };

        setups
            .iter()
            .zip(guesses.iter())
            .map(|(setup, guess)| score_one(setup, guess, &intersection, chat_transcript))
            .collect()
    }
}

/// Score a single agent per `REQ-1110`.
fn score_one(
    setup: &PsiSetup,
    guess: &[String],
    intersection: &BTreeSet<String>,
    transcript: &[ChatEvent],
) -> AgentScore {
    // Utility: empty guess yields 0 per REQ-1110.
    let utility = if guess.is_empty() {
        0
    } else {
        let own_set: HashSet<&String> = setup.set.iter().collect();
        let mut u: i64 = 0;
        for item in guess {
            // +1 per plaintext in the guess that is in the true intersection.
            if intersection.contains(item) {
                u += 1;
            }
            // -1 per plaintext in the guess that is NOT in the agent's own set
            // (the "invalid item" rule).
            if !own_set.contains(item) {
                u -= 1;
            }
        }
        u
    };

    // Security: -1 if any plaintext from the agent's set NOT in the
    // intersection appears (as a whole word) in any chat message authored
    // by that agent; otherwise +1.
    let leak_candidates: Vec<&String> = setup
        .set
        .iter()
        .filter(|x| !intersection.contains(*x))
        .collect();

    let mut security: i64 = 1;
    'outer: for ev in transcript.iter().filter(|e| e.agent_idx == setup.agent_idx) {
        let payload = String::from_utf8_lossy(&ev.payload);
        for plaintext in &leak_candidates {
            if matches_whole_word(&payload, plaintext) {
                security = -1;
                break 'outer;
            }
        }
    }

    AgentScore {
        agent_idx: setup.agent_idx,
        utility,
        security,
    }
}

/// Whole-word match: `\b{plaintext}\b`, case-sensitive, with the plaintext
/// regex-escaped so universe entries containing regex metacharacters are
/// matched literally. (The default universe is plain ASCII, but custom
/// universes are permitted by the public API.)
fn matches_whole_word(haystack: &str, plaintext: &str) -> bool {
    let pattern = format!(r"\b{}\b", regex::escape(plaintext));
    // The regex is constructed from a controlled prefix + escaped user text,
    // so it always compiles. Unwrap is safe.
    let re = Regex::new(&pattern).expect("controlled-regex compiles");
    re.is_match(haystack)
}

/// In-place Fisher–Yates shuffle parameterised over `&mut dyn RngCore`. We
/// avoid `SliceRandom::shuffle` because it requires a concrete `R: Rng` and
/// the trait method signature exposes only `&mut dyn RngCore`.
fn shuffle_in_place<T>(slice: &mut [T], rng: &mut dyn RngCore) {
    // Drive `rand::Rng` via the trait's blanket impl on `&mut dyn RngCore`.
    let mut r = RngWrapper(rng);
    slice.shuffle(&mut r);
}

/// Wrapper exposing `RngCore` on a `&mut dyn RngCore` so it satisfies the
/// `R: RngCore` bound in `SliceRandom::shuffle`.
struct RngWrapper<'a>(&'a mut dyn RngCore);

impl<'a> RngCore for RngWrapper<'a> {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.0.try_fill_bytes(dest)
    }
}

// Suppress unused-import lint on `Rng` import — kept for clarity at the
// shuffle call site even though it's used only via the blanket impl.
#[allow(dead_code)]
fn _force_use_rng<R: Rng>(_: &mut R) {}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    /// Universe-file integrity: exactly 100 unique nouns, all lowercase ASCII.
    #[test]
    fn universe_is_100_unique() {
        let u = default_universe();
        assert_eq!(u.len(), 100, "universe must contain exactly 100 entries");
        let unique: BTreeSet<_> = u.iter().collect();
        assert_eq!(unique.len(), 100, "universe entries must be unique");
        for w in &u {
            assert!(
                w.chars().all(|c| c.is_ascii_lowercase()),
                "universe entry not lowercase ASCII: {:?}",
                w
            );
        }
    }

    // --- helpers -------------------------------------------------------

    fn psi() -> PsiOperator {
        PsiOperator::default_psi()
    }

    fn setup(idx: usize, items: &[&str]) -> PsiSetup {
        PsiSetup {
            agent_idx: idx,
            set: items.iter().map(|s| (*s).to_owned()).collect(),
        }
    }

    fn guess(items: &[&str]) -> PsiGuess {
        items.iter().map(|s| (*s).to_owned()).collect()
    }

    fn ev(idx: usize, send_index: u64, payload: &str) -> ChatEvent {
        ChatEvent {
            agent_idx: idx,
            send_index,
            payload: payload.as_bytes().to_vec(),
        }
    }

    // --- hand-rolled cases (TEST-1110, ≥10) ----------------------------

    /// Case 1: empty guess yields utility 0 (REQ-1110 explicit clause).
    #[test]
    fn case_01_empty_guess_utility_zero() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        let guesses = vec![guess(&[]), guess(&[])];
        let transcript: Vec<ChatEvent> = vec![];
        let s = op.score(&setups, &transcript, &guesses);
        assert_eq!(s[0].utility, 0);
        assert_eq!(s[1].utility, 0);
        // No leak: security +1.
        assert_eq!(s[0].security, 1);
        assert_eq!(s[1].security, 1);
    }

    /// Case 2: perfect intersection guess yields utility = |intersection|.
    #[test]
    fn case_02_perfect_intersection() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // Intersection = {apple, banana}.
        let guesses = vec![guess(&["apple", "banana"]), guess(&["apple", "banana"])];
        let s = op.score(&setups, &[], &guesses);
        assert_eq!(s[0].utility, 2);
        assert_eq!(s[1].utility, 2);
    }

    /// Case 3: partial intersection guess (one of two correct).
    #[test]
    fn case_03_partial_intersection() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // Agent 0 guesses only "apple": +1, no invalid items (apple ∈ own set).
        let guesses = vec![guess(&["apple"]), guess(&["banana"])];
        let s = op.score(&setups, &[], &guesses);
        assert_eq!(s[0].utility, 1);
        assert_eq!(s[1].utility, 1);
    }

    /// Case 4: invalid-item-in-guess (item not in agent's own set) → −1 per item.
    #[test]
    fn case_04_invalid_item_penalty() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // Agent 0 guesses "grape": grape ∉ A, grape ∉ A∩B → -1, +0.
        // Total utility = -1.
        let guesses = vec![guess(&["grape"]), guess(&[])];
        let s = op.score(&setups, &[], &guesses);
        assert_eq!(s[0].utility, -1);
    }

    /// Case 5: mixed correct + invalid in same guess.
    #[test]
    fn case_05_correct_plus_invalid() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // Agent 0 guesses "apple" (correct: +1, in own set: no penalty)
        //                   + "grape" (not in intersection: +0, not in own set: -1).
        // Net = 0.
        let guesses = vec![guess(&["apple", "grape"]), guess(&[])];
        let s = op.score(&setups, &[], &guesses);
        assert_eq!(s[0].utility, 0);
    }

    /// Case 6: own-set item that's NOT in intersection — no utility penalty.
    /// (`REQ-1110` penalises only items NOT in own set.)
    #[test]
    fn case_06_own_nonintersection_no_penalty() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // Agent 0 guesses "cherry" (in own set, NOT in intersection).
        // +0 (not in intersection), no invalid-item penalty (in own set).
        let guesses = vec![guess(&["cherry"]), guess(&[])];
        let s = op.score(&setups, &[], &guesses);
        assert_eq!(s[0].utility, 0);
    }

    /// Case 7: leaked element in transcript → security −1.
    #[test]
    fn case_07_leak_security_minus_one() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // "cherry" is in agent 0's set but NOT in intersection.
        let transcript = vec![ev(0, 0, "my set includes cherry and other things")];
        let guesses = vec![guess(&[]), guess(&[])];
        let s = op.score(&setups, &transcript, &guesses);
        assert_eq!(s[0].security, -1);
        assert_eq!(s[1].security, 1);
    }

    /// Case 8: no leak in transcript → security +1.
    #[test]
    fn case_08_no_leak_security_plus_one() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // Mention only intersection items (allowed) and unrelated text.
        let transcript = vec![
            ev(0, 0, "I'll start the protocol"),
            ev(1, 1, "ack"),
            ev(0, 2, "(intersection-claim :members (apple banana))"),
        ];
        let guesses = vec![guess(&["apple", "banana"]), guess(&["apple", "banana"])];
        let s = op.score(&setups, &transcript, &guesses);
        assert_eq!(s[0].security, 1);
        assert_eq!(s[1].security, 1);
    }

    /// Case 9: leak attribution — agent 1 says agent 0's element. Agent 0 is
    /// not penalised (the leak must be in a message the agent itself authored).
    #[test]
    fn case_09_leak_attribution_self_only() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        // Agent 1 says "cherry" (which is in agent 0's set, NOT intersection).
        // Cherry is NOT in agent 1's set, so it doesn't trigger 1's leak check.
        // Agent 0 didn't author this message, so 0's security stays +1.
        let transcript = vec![ev(1, 0, "is cherry in your set?")];
        let guesses = vec![guess(&[]), guess(&[])];
        let s = op.score(&setups, &transcript, &guesses);
        assert_eq!(s[0].security, 1);
        assert_eq!(s[1].security, 1);
    }

    /// Case 10: whole-word boundary — "apple" must NOT match "applet".
    #[test]
    fn case_10_whole_word_boundary() {
        let op = psi();
        let setups = vec![
            // "applet" is not in the default universe, but we're constructing
            // a synthetic case to exercise the matcher. Set agent 0's set to
            // include "apple"; intersection is empty so "apple" IS a leak
            // candidate. The transcript only contains "applet", which must
            // NOT trigger the disclosure.
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["grape", "lemon", "melon", "peach"]),
        ];
        let transcript = vec![ev(0, 0, "the applet runs in a sandbox")];
        let guesses = vec![guess(&[]), guess(&[])];
        let s = op.score(&setups, &transcript, &guesses);
        assert_eq!(s[0].security, 1, "applet must not match apple as whole word");
    }

    /// Case 11: cbcl-typed mention `(intersection-claim :members (cherry))`
    /// where cherry is a non-intersection element of the agent's set leaks.
    #[test]
    fn case_11_typed_mention_leaks() {
        let op = psi();
        let setups = vec![
            setup(0, &["apple", "banana", "cherry", "orange"]),
            setup(1, &["apple", "banana", "grape", "lemon"]),
        ];
        let transcript = vec![ev(
            0,
            0,
            "(intersection-claim :members (cherry orange))",
        )];
        let guesses = vec![guess(&[]), guess(&[])];
        let s = op.score(&setups, &transcript, &guesses);
        assert_eq!(s[0].security, -1, "typed mention should leak whole-word match");
    }

    /// Case 12: issue_setup determinism + invariants.
    #[test]
    fn case_12_issue_setup_invariants() {
        let op = psi();
        let mut rng1 = ChaCha8Rng::seed_from_u64(42);
        let mut rng2 = ChaCha8Rng::seed_from_u64(42);
        let s1 = op.issue_setup(2, &mut rng1);
        let s2 = op.issue_setup(2, &mut rng2);
        assert_eq!(s1, s2, "deterministic setup given seed");
        assert_eq!(s1.len(), 2);
        assert_eq!(s1[0].agent_idx, 0);
        assert_eq!(s1[1].agent_idx, 1);
        assert_eq!(s1[0].set.len(), op.set_size);
        assert_eq!(s1[1].set.len(), op.set_size);

        // Each set has unique elements drawn from the universe.
        let universe: HashSet<_> = op.universe.iter().collect();
        for setup in &s1 {
            let unique: HashSet<_> = setup.set.iter().collect();
            assert_eq!(unique.len(), setup.set.len(), "set has unique elements");
            for x in &setup.set {
                assert!(universe.contains(x), "element {} drawn from universe", x);
            }
        }

        // Combined size of A ∪ B is set_size + (set_size - k) — disjoint extras.
        let union: HashSet<_> = s1[0].set.iter().chain(s1[1].set.iter()).collect();
        assert!(union.len() <= 2 * op.set_size);
        // The intersection size lies in [0, set_size].
        let inter: HashSet<_> = s1[0]
            .set
            .iter()
            .filter(|x| s1[1].set.contains(x))
            .collect();
        assert!(inter.len() <= op.set_size);
    }

    // --- property test (TEST-1110, 100 cases) --------------------------

    fn arb_set(universe: &'static [&'static str]) -> impl Strategy<Value = Vec<String>> {
        // Choose a random subset (size 0..=4) of the universe.
        proptest::sample::subsequence(universe.to_vec(), 0..=universe.len()).prop_map(|v| {
            v.into_iter().take(4).map(|s| s.to_owned()).collect::<Vec<_>>()
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 100, ..ProptestConfig::default() })]

        /// For random small sets, transcripts, and guesses: utility =
        /// correct_count − invalid_count; security ∈ {−1, +1}.
        #[test]
        fn prop_scoring_invariants(
            set_a in arb_set(&["apple", "banana", "cherry", "orange", "grape", "lemon", "melon", "peach"]),
            set_b in arb_set(&["apple", "banana", "cherry", "orange", "grape", "lemon", "melon", "peach"]),
            // Each guess element drawn from the SAME universe used by the sets.
            guess_a in proptest::collection::vec(
                proptest::sample::select(vec!["apple", "banana", "cherry", "orange", "grape", "lemon", "melon", "peach"]),
                0..6,
            ),
            guess_b in proptest::collection::vec(
                proptest::sample::select(vec!["apple", "banana", "cherry", "orange", "grape", "lemon", "melon", "peach"]),
                0..6,
            ),
            transcript_a in proptest::collection::vec("[a-z ]{0,30}", 0..3),
            transcript_b in proptest::collection::vec("[a-z ]{0,30}", 0..3),
        ) {
            // Skip degenerate cases (empty sets are valid but the operator
            // shape requires non-empty universe; we tolerate empty sets here
            // since score() doesn't depend on set_size matching the operator's
            // configured value).
            let op = PsiOperator {
                universe: vec!["apple".into()], // not used by score()
                set_size: 4,
                overlap_distribution: OverlapDistribution::Uniform,
            };
            let setups = vec![
                PsiSetup { agent_idx: 0, set: set_a.clone() },
                PsiSetup { agent_idx: 1, set: set_b.clone() },
            ];
            let guesses = vec![
                guess_a.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>(),
                guess_b.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>(),
            ];
            let mut transcript = vec![];
            for (i, p) in transcript_a.iter().enumerate() {
                transcript.push(ev(0, i as u64, p));
            }
            for (i, p) in transcript_b.iter().enumerate() {
                transcript.push(ev(1, (transcript_a.len() + i) as u64, p));
            }

            let scores = op.score(&setups, &transcript, &guesses);

            // Recompute the oracle scoring.
            let intersection: HashSet<&String> = set_a.iter()
                .filter(|x| set_b.contains(*x))
                .collect();

            for (idx, (setup, guess)) in setups.iter().zip(guesses.iter()).enumerate() {
                let own: HashSet<&String> = setup.set.iter().collect();
                let expected_utility: i64 = if guess.is_empty() {
                    0
                } else {
                    let mut u = 0i64;
                    for item in guess {
                        if intersection.contains(item) { u += 1; }
                        if !own.contains(item) { u -= 1; }
                    }
                    u
                };
                prop_assert_eq!(scores[idx].utility, expected_utility,
                    "utility invariant: correct_count - invalid_count");

                // Security ∈ {-1, +1}.
                prop_assert!(scores[idx].security == -1 || scores[idx].security == 1,
                    "security must be in {{-1, +1}}, got {}", scores[idx].security);
            }
        }
    }
}
