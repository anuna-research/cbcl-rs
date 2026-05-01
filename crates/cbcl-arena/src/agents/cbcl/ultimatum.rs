//! ultimatum: CBCL-disciplined Ultimatum bargaining strategy
//! (`IMPL-arena-evals` E5, paired with `operator::ultimatum`).
//!
//! Implements one round of the Ultimatum game per
//! `demo/dialects/ultimatum.cbcl`:
//!
//! ```text
//! begin → ult-offer → (ult-accept | ult-reject | ult-pass) → ult-final
//! ```
//!
//! ## Role-aware phase machine
//!
//! - **Proposer**: `PostOffer → AwaitResponse → PostFinal → Done`. Emits
//!   `ult-offer` first; ingests the peer's accept / reject; emits
//!   `ult-final` carrying the joint outcome.
//! - **Responder**: `AwaitOffer → PostResponse → PostFinal → Done`. Waits
//!   for `ult-offer`; emits `ult-accept` or `ult-reject` based on whether
//!   the offered share is at or above its own reservation; emits
//!   `ult-final` carrying the joint outcome.
//!
//! ## Heuristic
//!
//! The proposer offers the responder a share equal to its own
//! reservation — the "fair-by-symmetric-prior" heuristic, which assumes
//! responders draw reservations from a similar distribution. This keeps
//! the strategy purely a function of one's own private setup (no
//! information leakage) while still being competitive under symmetric
//! priors.
//!
//! ## Quarantine invariant
//!
//! Under honest play (peer also CBCL-disciplined) every emitted message
//! parses, lies in the dialect's allowed performative set, and follows
//! the causal protocol. The quarantine buffer therefore stays empty —
//! tested in `tests::honest_proposer_responder_round` and
//! `tests::proposer_offers_above_reservation_gets_accepted`.

use cbcl_core::message::Message;
use cbcl_core::sexpr::{Atom, SExpr};
use rand::RngCore;

use super::content;
use super::CausedBySelector;
use super::ChallengeStrategy;
use super::OutboundDraft;
use crate::operator::ultimatum::{UltimatumGuess, UltimatumRole, UltimatumSetup};

/// Phase of the per-role state machine. Both roles converge on
/// `PostFinal` (operator-bound submission) before `Done`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    /// Proposer: about to emit `ult-offer`.
    PostOffer,
    /// Proposer: emitted offer, waiting for peer's accept/reject.
    AwaitResponse,
    /// Responder: waiting for the peer's `ult-offer`.
    AwaitOffer,
    /// Responder: offer received, about to emit accept/reject.
    PostResponse,
    /// Either role: peer's contribution received, emit `ult-final`.
    PostFinal,
    /// Done.
    Done,
}

/// Ultimatum-bargaining strategy state machine.
pub struct UltimatumCbclStrategy {
    /// Setup payload — populated on `ingest_setup`.
    setup: Option<UltimatumSetup>,
    /// Phase of the role-specific machine.
    phase: Phase,
    /// Responder share from the most-recently-ingested `ult-offer`. This
    /// is the proposer's view of "what the responder gets if accepted".
    offered_responder_share: Option<u64>,
    /// `Some(true)` if peer's `ult-accept` landed, `Some(false)` if
    /// `ult-reject` landed, `None` otherwise.
    peer_decision: Option<bool>,
    /// Own decision (responder only): mirrors `peer_decision` for the
    /// proposer view.
    own_decision: Option<bool>,
}

impl UltimatumCbclStrategy {
    /// Construct a fresh strategy. Setup is supplied via
    /// [`ChallengeStrategy::ingest_setup`].
    pub fn new() -> Self {
        Self {
            setup: None,
            phase: Phase::PostOffer, // overwritten in ingest_setup
            offered_responder_share: None,
            peer_decision: None,
            own_decision: None,
        }
    }

    fn role(&self) -> UltimatumRole {
        self.setup
            .as_ref()
            .map(|s| s.role)
            .unwrap_or(UltimatumRole::Proposer)
    }

    /// Compute the joint outcome from accumulated state. Used to populate
    /// `ult-final`'s `:action` symbol and the operator-bound guess.
    fn joint_outcome(&self) -> UltimatumGuess {
        let share = match self.offered_responder_share {
            Some(s) => s,
            None => return UltimatumGuess::NoAgreement,
        };
        // Accept signal can come from either own_decision (responder's
        // view) or peer_decision (proposer's view).
        let accepted = match self.role() {
            UltimatumRole::Proposer => self.peer_decision,
            UltimatumRole::Responder => self.own_decision,
        };
        match accepted {
            Some(true) => UltimatumGuess::Accepted {
                responder_share: share,
            },
            Some(false) => UltimatumGuess::Rejected,
            None => UltimatumGuess::NoAgreement,
        }
    }

    /// Symbol attached to `ult-final`'s `:action` keyword.
    fn final_action_symbol(outcome: UltimatumGuess) -> &'static str {
        match outcome {
            UltimatumGuess::Accepted { .. } => "accepted",
            UltimatumGuess::Rejected => "rejected",
            UltimatumGuess::NoAgreement | UltimatumGuess::Unknown => "no-agreement",
        }
    }
}

impl Default for UltimatumCbclStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl ChallengeStrategy for UltimatumCbclStrategy {
    type Setup = UltimatumSetup;
    type Guess = UltimatumGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.phase = match setup.role {
            UltimatumRole::Proposer => Phase::PostOffer,
            UltimatumRole::Responder => Phase::AwaitOffer,
        };
        self.setup = Some(setup);
    }

    fn ingest_inbound(&mut self, msg: &Message) {
        let inner = msg.innermost_simple().unwrap_or(msg);
        let Some(perf) = inner.performative() else {
            return;
        };
        match perf.name() {
            "ult-offer" => {
                // Content shape: `(offer :split (P R))`.
                if let Some(split_e) = content::get_kw(inner, "split") {
                    if let Some(share) = extract_responder_share(split_e) {
                        self.offered_responder_share = Some(share);
                        // Responder transitions to PostResponse on first
                        // valid offer.
                        if self.role() == UltimatumRole::Responder
                            && self.phase == Phase::AwaitOffer
                        {
                            self.phase = Phase::PostResponse;
                        }
                    }
                }
            }
            "ult-accept" => {
                self.peer_decision = Some(true);
                if self.role() == UltimatumRole::Proposer
                    && self.phase == Phase::AwaitResponse
                {
                    self.phase = Phase::PostFinal;
                }
            }
            "ult-reject" | "ult-pass" => {
                self.peer_decision = Some(false);
                if self.role() == UltimatumRole::Proposer
                    && self.phase == Phase::AwaitResponse
                {
                    self.phase = Phase::PostFinal;
                }
            }
            _ => {}
        }
    }

    fn next_outbound(&mut self, _rng: &mut dyn RngCore) -> Option<OutboundDraft> {
        let setup = self.setup?;
        match self.phase {
            Phase::PostOffer => {
                // Proposer-only: offer a fair 50/50 split. The earlier
                // "offer own_reservation" heuristic was rejected because
                // it puts the proposer's reservation in the wire bytes
                // — operator-side scoring (`crate::operator::ultimatum`)
                // flags any chat event from the proposer that contains
                // the proposer's own reservation as a security leak,
                // and a deterministic-equality offer is exactly that
                // leak. The 50/50 split is reservation-independent and
                // matches the Camerer (2003) modal proposer offer in
                // human UG behavioural data.
                let responder_share = setup.total / 2;
                let proposer_share = setup.total.saturating_sub(responder_share);
                self.offered_responder_share = Some(responder_share);
                let split = SExpr::List(vec![
                    SExpr::Atom(Atom::Num(proposer_share as i64)),
                    SExpr::Atom(Atom::Num(responder_share as i64)),
                ]);
                self.phase = Phase::AwaitResponse;
                Some(OutboundDraft {
                    performative: "ult-offer".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form("offer", &[("split", split)]),
                    caused_by: CausedBySelector::Begin,
                })
            }
            Phase::AwaitResponse | Phase::AwaitOffer => {
                // Nothing to emit until the peer's contribution lands.
                None
            }
            Phase::PostResponse => {
                // Responder-only: accept iff the offered responder share
                // is at or above our own reservation; else reject.
                let share = self.offered_responder_share?;
                let accept = share >= setup.reservation;
                self.own_decision = Some(accept);
                let perf = if accept { "ult-accept" } else { "ult-reject" };
                let content = if accept {
                    content::keyword_form("accept-offer", &[])
                } else {
                    content::keyword_form("reject-offer", &[])
                };
                self.phase = Phase::PostFinal;
                Some(OutboundDraft {
                    performative: perf.to_string(),
                    recipient: Some("@peer".to_string()),
                    content,
                    caused_by: CausedBySelector::LatestOfPerformative("ult-offer".to_string()),
                })
            }
            Phase::PostFinal => {
                // Proposer waits for peer_decision; responder already has
                // own_decision set on PostResponse.
                if self.role() == UltimatumRole::Proposer && self.peer_decision.is_none() {
                    return None;
                }
                let outcome = self.joint_outcome();
                let action = Self::final_action_symbol(outcome);
                // `:caused-by` references the most recent
                // accept/reject/pass message — which is whichever of the
                // peer's or our own response landed in the store.
                let predecessor = if self.role() == UltimatumRole::Proposer {
                    match self.peer_decision {
                        Some(true) => "ult-accept",
                        Some(false) => "ult-reject",
                        None => "ult-offer",
                    }
                } else {
                    match self.own_decision {
                        Some(true) => "ult-accept",
                        Some(false) => "ult-reject",
                        None => "ult-offer",
                    }
                };
                self.phase = Phase::Done;
                Some(OutboundDraft {
                    performative: "ult-final".to_string(),
                    recipient: Some("@operator".to_string()),
                    content: content::keyword_form(
                        "final-action",
                        &[("action", SExpr::Atom(Atom::Symbol(action.to_string())))],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative(predecessor.to_string()),
                })
            }
            Phase::Done => None,
        }
    }

    fn final_guess(&self) -> Self::Guess {
        if self.setup.is_none() {
            return UltimatumGuess::Unknown;
        }
        self.joint_outcome()
    }

    fn is_done(&self) -> bool {
        self.phase == Phase::Done
    }
}

/// Extract the responder's share from a `:split` payload of shape
/// `(proposer_share responder_share)` (a 2-element list of integers).
fn extract_responder_share(e: &SExpr) -> Option<u64> {
    let SExpr::List(items) = e else {
        return None;
    };
    if items.len() != 2 {
        return None;
    }
    match &items[1] {
        SExpr::Atom(Atom::Num(n)) if *n >= 0 => Some(*n as u64),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agents::cbcl::{load_dialect, CbclAgent, ChallengeStrategy, StepStatus};
    use crate::operator::ChatEvent;
    use crate::operator::ultimatum::{UltimatumRole, UltimatumSetup};
    use cbcl_core::dialect::Dialect;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    const ULTIMATUM_DIALECT_SRC: &str =
        include_str!("../../../../../demo/dialects/ultimatum.cbcl");

    fn ultimatum_dialect() -> Dialect {
        load_dialect(ULTIMATUM_DIALECT_SRC).expect("ultimatum dialect parses")
    }

    /// In-test harness — same shape as `cbcl/tests.rs::run_game`. Drives
    /// `n` agents through interleaved stepping, fanning each agent's
    /// outbound to the others' inboxes, until all report done.
    fn run_game(
        agents: &mut [CbclAgent<UltimatumCbclStrategy>],
        setups: Vec<UltimatumSetup>,
        rng_seed: u64,
    ) -> (Vec<ChatEvent>, Vec<UltimatumGuess>) {
        assert_eq!(agents.len(), setups.len());
        let n = agents.len();
        let mut inboxes: Vec<Vec<ChatEvent>> = vec![Vec::new(); n];
        let mut rngs: Vec<ChaCha8Rng> = (0..n)
            .map(|i| ChaCha8Rng::seed_from_u64(rng_seed.wrapping_add(i as u64)))
            .collect();
        let mut send_indices: Vec<u64> = vec![0; n];
        let mut transcript: Vec<ChatEvent> = Vec::new();

        for (agent, setup) in agents.iter_mut().zip(setups.into_iter()) {
            super::super::ingest_setup(agent, setup);
        }

        for _round in 0..64 {
            let mut any_progress = false;
            let mut any_unfinished = false;
            for i in 0..n {
                let inbound: Vec<ChatEvent> = std::mem::take(&mut inboxes[i]);
                let mut iter = inbound.into_iter();
                let mut emitted: Vec<ChatEvent> = Vec::new();
                let status: StepStatus = {
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
            if !any_progress || !any_unfinished {
                break;
            }
        }

        let guesses: Vec<UltimatumGuess> =
            agents.iter().map(|a| a.strategy.final_guess()).collect();
        (transcript, guesses)
    }

    /// Honest play, proposer reservation < responder reservation: the
    /// proposer offers (via the "fair-by-symmetric-prior" heuristic) its
    /// own reservation, which is below the responder's threshold; the
    /// responder rejects; both submit `Rejected`.
    #[test]
    fn honest_proposer_responder_round() {
        let dialect = ultimatum_dialect();
        let proposer = CbclAgent::new(
            dialect.clone(),
            UltimatumCbclStrategy::new(),
            "ult-game-rejected",
            "alice",
        );
        let responder = CbclAgent::new(
            dialect.clone(),
            UltimatumCbclStrategy::new(),
            "ult-game-rejected",
            "bob",
        );
        let mut agents = [proposer, responder];
        let setups = vec![
            UltimatumSetup {
                agent_idx: 0,
                role: UltimatumRole::Proposer,
                reservation: 30,
                total: 100,
            },
            // Responder reservation strictly above the strategy's
            // 50/50 fair-split offer, so the responder rejects.
            UltimatumSetup {
                agent_idx: 1,
                role: UltimatumRole::Responder,
                reservation: 60,
                total: 100,
            },
        ];
        let (transcript, guesses) = run_game(&mut agents, setups, 0xCAFE);

        assert_eq!(guesses[0], UltimatumGuess::Rejected);
        assert_eq!(guesses[1], UltimatumGuess::Rejected);
        assert!(
            agents[0].quarantine.is_empty(),
            "proposer quarantined honest message: {:?}",
            agents[0].quarantine
        );
        assert!(
            agents[1].quarantine.is_empty(),
            "responder quarantined honest message: {:?}",
            agents[1].quarantine
        );
        // Sanity: protocol produced an `ult-offer` and an `ult-reject`.
        let perfs: Vec<&str> = transcript
            .iter()
            .filter_map(|ev| std::str::from_utf8(&ev.payload).ok())
            .filter_map(|t| {
                // `(<perf> :recipient ...)` — first symbol after `(`.
                let trimmed = t.trim_start_matches(|c: char| !c.is_alphabetic());
                trimmed.split(|c: char| !c.is_ascii_alphanumeric() && c != '-').next()
            })
            .collect();
        assert!(perfs.iter().any(|p| *p == "ult-offer"));
        assert!(perfs.iter().any(|p| *p == "ult-reject"));
    }

    /// Honest play, proposer reservation >= responder reservation: the
    /// proposer offers its own reservation, which clears the responder's
    /// threshold; the responder accepts; both submit
    /// `Accepted { responder_share: 50 }`.
    #[test]
    fn proposer_offers_above_reservation_gets_accepted() {
        let dialect = ultimatum_dialect();
        let proposer = CbclAgent::new(
            dialect.clone(),
            UltimatumCbclStrategy::new(),
            "ult-game-accepted",
            "alice",
        );
        let responder = CbclAgent::new(
            dialect.clone(),
            UltimatumCbclStrategy::new(),
            "ult-game-accepted",
            "bob",
        );
        let mut agents = [proposer, responder];
        let setups = vec![
            UltimatumSetup {
                agent_idx: 0,
                role: UltimatumRole::Proposer,
                reservation: 50,
                total: 100,
            },
            UltimatumSetup {
                agent_idx: 1,
                role: UltimatumRole::Responder,
                reservation: 40,
                total: 100,
            },
        ];
        let (transcript, guesses) = run_game(&mut agents, setups, 0xBEEF);

        assert_eq!(
            guesses[0],
            UltimatumGuess::Accepted {
                responder_share: 50
            }
        );
        assert_eq!(
            guesses[1],
            UltimatumGuess::Accepted {
                responder_share: 50
            }
        );
        assert!(
            agents[0].quarantine.is_empty(),
            "proposer quarantined honest message: {:?}",
            agents[0].quarantine
        );
        assert!(
            agents[1].quarantine.is_empty(),
            "responder quarantined honest message: {:?}",
            agents[1].quarantine
        );
        // Both agents must have submitted ult-final.
        let final_count = transcript
            .iter()
            .filter(|ev| {
                std::str::from_utf8(&ev.payload)
                    .map(|s| s.contains("ult-final"))
                    .unwrap_or(false)
            })
            .count();
        assert_eq!(final_count, 2, "expected two ult-final emissions");
    }
}
