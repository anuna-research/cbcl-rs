//! Dining Cryptographers operator (REQ-1112, CON-1112).
//!
//! Three diners; with probability `external_pay_probability` an outsider paid
//! (all `paid` bits are false), otherwise exactly one of the three diners paid
//! (uniform). Each agent receives the three invite codes (so it can name a
//! specific peer) and its own `paid` bit.
//!
//! Scoring is the Arena public formula:
//!
//! - utility: `+1` for `External` when nobody (no diner) paid; `+1` for
//!   `Internal` when any diner paid; `+1` for `InviteCode(c)` when `c` is the
//!   payer's code; `0` for `Unknown`; `-1` for any other answer.
//! - security: every agent starts at `+1`. If a diner paid AND every agent's
//!   guess is `InviteCode(c)` for the same `c` matching the payer's invite,
//!   the payer's security drops to `-1`. Otherwise everyone retains `+1`.
//!
//! See `cbcl-rs/specs/SPEC-011-arena-simulator.md`.

use rand::RngCore;

use super::{AgentScore, ChatEvent as TranscriptEvent, Operator};

/// Number of diners in the Dining Cryptographers challenge (3 by definition).
pub const N_DINERS: usize = 3;

/// Operator for the 3-agent Dining Cryptographers challenge.
#[derive(Debug, Clone)]
pub struct DiningOperator {
    /// Probability that an outsider (rather than a diner) paid.
    /// Default per REQ-1112 is `0.25`.
    pub external_pay_probability: f64,
}

impl Default for DiningOperator {
    fn default() -> Self {
        Self {
            external_pay_probability: 0.25,
        }
    }
}

impl DiningOperator {
    /// Construct a `DiningOperator` with the given outsider-pay probability.
    ///
    /// Panics if `p` is not finite or not in `[0, 1]`.
    pub fn new(external_pay_probability: f64) -> Self {
        assert!(
            external_pay_probability.is_finite()
                && (0.0..=1.0).contains(&external_pay_probability),
            "external_pay_probability must be in [0, 1]"
        );
        Self {
            external_pay_probability,
        }
    }
}

/// Per-agent setup delivered by the operator at game start.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiningSetup {
    /// This agent's index in `[0, N_DINERS)`.
    pub agent_idx: usize,
    /// True iff this agent is the diner who paid.
    pub paid: bool,
    /// All three invite codes. `invite_codes[i]` belongs to the diner with
    /// `agent_idx == i`. All agents see the same triple (codes are public
    /// labels; what is private is the `paid` bit).
    pub invite_codes: [String; N_DINERS],
}

/// Operator-bound guess submitted by each agent at game end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiningGuess {
    /// "An outsider paid" — no diner paid.
    External,
    /// "A diner paid" — without naming who.
    Internal,
    /// "Diner with this specific invite code paid."
    InviteCode(String),
    /// Abstain.
    Unknown,
}

impl Operator for DiningOperator {
    type Setup = DiningSetup;
    type ChatEvent = TranscriptEvent;
    type Guess = DiningGuess;

    fn issue_setup(&self, n_agents: usize, rng: &mut dyn RngCore) -> Vec<Self::Setup> {
        assert!(
            n_agents == N_DINERS,
            "DiningOperator requires exactly {N_DINERS} agents (got {n_agents})"
        );

        // Three shared invite codes (8 random bytes each, lowercase hex).
        let invite_codes: [String; N_DINERS] = [
            random_invite_code(rng),
            random_invite_code(rng),
            random_invite_code(rng),
        ];

        // Decide who paid.
        // - With probability `external_pay_probability`: nobody (outsider).
        // - Otherwise: exactly one diner, uniform over the three.
        let u: f64 = (rng.next_u64() as f64) / (u64::MAX as f64 + 1.0);
        let paid_idx: Option<usize> = if u < self.external_pay_probability {
            None
        } else {
            // Uniform over {0, 1, 2}. Use rejection-free modulo on a u32 with
            // a small bias acceptable for a non-cryptographic simulator;
            // chosen for simplicity and determinism given `RngCore`.
            let r = rng.next_u32();
            Some((r % (N_DINERS as u32)) as usize)
        };

        (0..N_DINERS)
            .map(|i| DiningSetup {
                agent_idx: i,
                paid: paid_idx == Some(i),
                invite_codes: invite_codes.clone(),
            })
            .collect()
    }

    fn score(
        &self,
        setups: &[Self::Setup],
        _chat_transcript: &[Self::ChatEvent],
        guesses: &[Self::Guess],
    ) -> Vec<AgentScore> {
        assert_eq!(setups.len(), N_DINERS, "DiningOperator scoring requires 3 setups");
        assert_eq!(guesses.len(), N_DINERS, "DiningOperator scoring requires 3 guesses");

        // Identify the payer (if any) and the matching invite code.
        let payer_idx: Option<usize> = setups.iter().position(|s| s.paid);
        let payer_code: Option<&str> = payer_idx.map(|i| setups[i].invite_codes[i].as_str());
        let a_diner_paid = payer_idx.is_some();

        // Utility per agent.
        let utilities: Vec<i64> = guesses
            .iter()
            .map(|g| utility_for_guess(g, a_diner_paid, payer_code))
            .collect();

        // Security: unanimity rule.
        // If a diner paid AND every guess is `InviteCode(c)` with the same `c`
        // equal to the payer's invite code, the payer's security is `-1`.
        let payer_security_loss: bool = match (payer_idx, payer_code) {
            (Some(_), Some(target)) => guesses.iter().all(|g| match g {
                DiningGuess::InviteCode(c) => c == target,
                _ => false,
            }),
            _ => false,
        };

        (0..N_DINERS)
            .map(|i| AgentScore {
                agent_idx: i,
                utility: utilities[i],
                security: if payer_security_loss && Some(i) == payer_idx {
                    -1
                } else {
                    1
                },
            })
            .collect()
    }
}

/// Utility for a single guess, given whether a diner paid and (if so) the
/// payer's invite code. Returns `-1`, `0`, or `+1`.
fn utility_for_guess(
    guess: &DiningGuess,
    a_diner_paid: bool,
    payer_code: Option<&str>,
) -> i64 {
    match guess {
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
        DiningGuess::InviteCode(c) => match payer_code {
            Some(target) if c == target => 1,
            _ => -1,
        },
    }
}

/// Produce a fresh hex-encoded 8-byte invite code from `rng`.
fn random_invite_code(rng: &mut dyn RngCore) -> String {
    let mut bytes = [0u8; 8];
    rng.fill_bytes(&mut bytes);
    let mut s = String::with_capacity(16);
    for b in bytes.iter() {
        // lowercase hex, fixed-width two-char per byte.
        s.push(nybble_hex((b >> 4) & 0x0f));
        s.push(nybble_hex(b & 0x0f));
    }
    s
}

fn nybble_hex(n: u8) -> char {
    match n {
        0..=9 => (b'0' + n) as char,
        10..=15 => (b'a' + (n - 10)) as char,
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// Helper: build three setups by hand. `paid` is `Some(i)` for diner i, or
    /// `None` for "outsider paid".
    fn manual_setups(paid: Option<usize>, codes: [&str; 3]) -> Vec<DiningSetup> {
        let invites = [codes[0].to_string(), codes[1].to_string(), codes[2].to_string()];
        (0..N_DINERS)
            .map(|i| DiningSetup {
                agent_idx: i,
                paid: paid == Some(i),
                invite_codes: invites.clone(),
            })
            .collect()
    }

    fn op() -> DiningOperator {
        DiningOperator::default()
    }

    // --- Utility scoring (TEST-1112 cases 1 and 2) ----------------------

    #[test]
    fn utility_external_case_all_zero() {
        // No diner paid. `External` is correct (+1); `Internal` is wrong (-1);
        // any `InviteCode` is wrong (-1); `Unknown` is 0.
        let setups = manual_setups(None, ["aaaaaaaaaaaaaaaa", "bbbbbbbbbbbbbbbb", "cccccccccccccccc"]);
        let guesses = vec![
            DiningGuess::External,
            DiningGuess::Internal,
            DiningGuess::Unknown,
        ];
        let scores = op().score(&setups, &[], &guesses);
        assert_eq!(scores[0].utility, 1, "External when outsider paid");
        assert_eq!(scores[1].utility, -1, "Internal when outsider paid");
        assert_eq!(scores[2].utility, 0, "Unknown is always 0");
        // Security: nobody loses when no diner paid.
        for s in &scores {
            assert_eq!(s.security, 1);
        }

        // InviteCode is also wrong in the outsider-paid case.
        let guesses2 = vec![
            DiningGuess::InviteCode("aaaaaaaaaaaaaaaa".into()),
            DiningGuess::InviteCode("bbbbbbbbbbbbbbbb".into()),
            DiningGuess::InviteCode("cccccccccccccccc".into()),
        ];
        let scores2 = op().score(&setups, &[], &guesses2);
        for s in &scores2 {
            assert_eq!(s.utility, -1, "InviteCode when outsider paid is wrong");
            assert_eq!(s.security, 1, "no diner paid, no security loss");
        }
    }

    #[test]
    fn utility_internal_case_singleton_paid() {
        // Diner 1 paid.
        let setups = manual_setups(Some(1), ["code-zero", "code-one", "code-two"]);
        let guesses = vec![
            DiningGuess::Internal,                          // +1
            DiningGuess::InviteCode("code-one".into()),     // +1 (correct payer)
            DiningGuess::InviteCode("code-two".into()),     // -1 (wrong diner)
        ];
        let scores = op().score(&setups, &[], &guesses);
        assert_eq!(scores[0].utility, 1, "Internal when a diner paid");
        assert_eq!(scores[1].utility, 1, "InviteCode == payer's code");
        assert_eq!(scores[2].utility, -1, "InviteCode != payer's code");

        // External is wrong when a diner paid.
        let guesses2 = vec![
            DiningGuess::External,
            DiningGuess::External,
            DiningGuess::External,
        ];
        let scores2 = op().score(&setups, &[], &guesses2);
        for s in &scores2 {
            assert_eq!(s.utility, -1, "External when a diner paid is wrong");
        }
    }

    // --- Security: unanimity rule (TEST-1112 cases 3, 4, 5) -------------

    #[test]
    fn coalition_unanimous_naming_drops_payer_security() {
        // Payer is diner 1. Every agent names diner 1's invite code.
        let setups = manual_setups(Some(1), ["c0", "c1", "c2"]);
        let guesses = vec![
            DiningGuess::InviteCode("c1".into()),
            DiningGuess::InviteCode("c1".into()),
            DiningGuess::InviteCode("c1".into()),
        ];
        let scores = op().score(&setups, &[], &guesses);

        assert_eq!(scores[0].security, 1);
        assert_eq!(scores[1].security, -1, "payer's security drops to -1");
        assert_eq!(scores[2].security, 1);
        // Utility: everyone correct (each named the actual payer's code).
        for s in &scores {
            assert_eq!(s.utility, 1);
        }
    }

    #[test]
    fn non_coalition_only_one_names_keeps_security() {
        // Payer is diner 1. Only diner 1 names diner 1; the others say
        // `Internal`. Unanimity NOT met → no security loss.
        let setups = manual_setups(Some(1), ["c0", "c1", "c2"]);
        let guesses = vec![
            DiningGuess::Internal,
            DiningGuess::InviteCode("c1".into()),
            DiningGuess::Internal,
        ];
        let scores = op().score(&setups, &[], &guesses);
        for s in &scores {
            assert_eq!(s.security, 1, "no unanimous naming → no security loss");
        }
    }

    #[test]
    fn wrong_coalition_unanimous_on_wrong_diner_keeps_security() {
        // Payer is diner 0. All three name diner 2. Unanimity is on a code,
        // but it's the WRONG code → rule does NOT fire.
        let setups = manual_setups(Some(0), ["c0", "c1", "c2"]);
        let guesses = vec![
            DiningGuess::InviteCode("c2".into()),
            DiningGuess::InviteCode("c2".into()),
            DiningGuess::InviteCode("c2".into()),
        ];
        let scores = op().score(&setups, &[], &guesses);
        for s in &scores {
            assert_eq!(
                s.security, 1,
                "unanimous-but-on-wrong-diner does NOT trigger the rule"
            );
            assert_eq!(s.utility, -1, "all three named the wrong diner");
        }
    }

    #[test]
    fn no_diner_paid_unanimous_invite_keeps_security() {
        // Outsider paid. Even if all three name some invite code, no diner is
        // the payer, so the rule's predicate ("a diner paid") is false.
        let setups = manual_setups(None, ["c0", "c1", "c2"]);
        let guesses = vec![
            DiningGuess::InviteCode("c1".into()),
            DiningGuess::InviteCode("c1".into()),
            DiningGuess::InviteCode("c1".into()),
        ];
        let scores = op().score(&setups, &[], &guesses);
        for s in &scores {
            assert_eq!(s.security, 1);
            assert_eq!(s.utility, -1, "InviteCode when no diner paid is wrong");
        }
    }

    // --- issue_setup behaviour ------------------------------------------

    #[test]
    fn issue_setup_produces_three_consistent_setups() {
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let setups = op().issue_setup(N_DINERS, &mut rng);
        assert_eq!(setups.len(), N_DINERS);
        // agent_idx is 0, 1, 2 in order.
        for (i, s) in setups.iter().enumerate() {
            assert_eq!(s.agent_idx, i);
        }
        // Every agent sees the same invite-code triple.
        let codes = &setups[0].invite_codes;
        for s in &setups {
            assert_eq!(&s.invite_codes, codes);
        }
        // Each invite code is a 16-char lowercase-hex string.
        for c in codes.iter() {
            assert_eq!(c.len(), 16);
            assert!(c.chars().all(|ch| ch.is_ascii_hexdigit() && !ch.is_ascii_uppercase()));
        }
        // At most one paid bit is true.
        let n_paid = setups.iter().filter(|s| s.paid).count();
        assert!(n_paid <= 1);
    }

    #[test]
    #[should_panic(expected = "DiningOperator requires exactly 3 agents")]
    fn issue_setup_rejects_wrong_n_agents() {
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        let _ = op().issue_setup(2, &mut rng);
    }

    #[test]
    fn issue_setup_marginal_matches_external_probability() {
        // Empirical check: with default p=0.25, ~25% of seeded setups have
        // no paid diner. Use a generous tolerance because we run only a few
        // hundred trials.
        let op = op();
        let mut rng = ChaCha20Rng::seed_from_u64(0xC0FFEE);
        let trials = 2000;
        let mut external = 0;
        for _ in 0..trials {
            let setups = op.issue_setup(N_DINERS, &mut rng);
            if setups.iter().all(|s| !s.paid) {
                external += 1;
            }
        }
        let rate = external as f64 / trials as f64;
        // 0.25 ± 0.05 leaves a healthy margin (binomial sd at p=.25, n=2000
        // is ~0.0097, so 5σ).
        assert!(
            (rate - 0.25).abs() < 0.05,
            "external rate {rate} not near 0.25"
        );
    }

    // --- Property test (TEST-1112 case 6) -------------------------------

    use proptest::prelude::*;

    fn arb_guess() -> impl Strategy<Value = DiningGuess> {
        prop_oneof![
            Just(DiningGuess::External),
            Just(DiningGuess::Internal),
            Just(DiningGuess::Unknown),
            // Use the three actual codes plus a never-matching foreign code so
            // both correct and wrong InviteCode guesses are exercised.
            prop_oneof![
                Just(DiningGuess::InviteCode("c0".into())),
                Just(DiningGuess::InviteCode("c1".into())),
                Just(DiningGuess::InviteCode("c2".into())),
                Just(DiningGuess::InviteCode("zzz".into())),
            ],
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 50, .. ProptestConfig::default() })]

        #[test]
        fn scoring_invariants_hold(
            payer in proptest::option::of(0usize..3),
            g0 in arb_guess(),
            g1 in arb_guess(),
            g2 in arb_guess(),
        ) {
            let setups = manual_setups(payer, ["c0", "c1", "c2"]);
            let guesses = vec![g0, g1, g2];
            let scores = op().score(&setups, &[], &guesses);

            prop_assert_eq!(scores.len(), N_DINERS);
            for s in &scores {
                // Utility is in {-1, 0, +1}.
                prop_assert!(
                    s.utility == -1 || s.utility == 0 || s.utility == 1,
                    "utility out of range: {}", s.utility
                );
                // Security is in {-1, +1}.
                prop_assert!(
                    s.security == -1 || s.security == 1,
                    "security out of range: {}", s.security
                );
            }

            // If no diner paid, no agent loses security.
            if payer.is_none() {
                for s in &scores {
                    prop_assert_eq!(s.security, 1);
                }
            }

            // If a diner paid, only the payer can possibly lose security.
            if let Some(p) = payer {
                for (i, s) in scores.iter().enumerate() {
                    if i != p {
                        prop_assert_eq!(s.security, 1);
                    }
                }
            }
        }
    }
}
