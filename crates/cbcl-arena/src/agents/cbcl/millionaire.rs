//! millionaire: Yao's Millionaire strategy for the CBCL-disciplined agent
//! (REQ-1111-paired).
//!
//! Implements one bracket round per `demo/dialects/millionaire.cbcl`:
//!
//! ```text
//! yao-bracket → yao-bracket-commit → yao-bracket-reveal → yao-final
//! ```
//!
//! ## Protocol shape
//!
//! Both sides do one bracket. The "asker" emits `yao-bracket` with
//! `threshold = wealth_range / 2`; the "answerer" replies with
//! `yao-bracket-commit` (a salted hash of its bit `wealth ≥ threshold`),
//! then `yao-bracket-reveal` (bit + salt). After both reveals are
//! exchanged, each agent submits `yao-final` with a verdict.
//!
//! Both sides simultaneously act as asker AND answerer (they each ask one
//! question at a fixed threshold and answer the peer's at the same fixed
//! threshold). This gives each side both bits and lets them deterministically
//! compute `richer | poorer | equal | unknown`.
//!
//! ## Verdict logic
//!
//! With `me_bit = own_wealth ≥ threshold` and `peer_bit = peer_wealth ≥ threshold`:
//! - `me_bit && !peer_bit` → I am richer.
//! - `!me_bit && peer_bit` → I am poorer.
//! - `me_bit == peer_bit`  → bracket is uninformative → `Unknown`.
//!
//! This gives one bit of comparison information; per the task brief that's
//! sufficient to demonstrate the discipline.

use cbcl_core::message::Message;
use cbcl_core::sexpr::{Atom, SExpr};
use rand::RngCore;

use super::content;
use super::CausedBySelector;
use super::ChallengeStrategy;
use super::OutboundDraft;

/// Operator-bound verdict for Yao's Millionaire.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum YaoVerdict {
    /// `own_wealth > peer_wealth`.
    Richer,
    /// `own_wealth < peer_wealth`.
    Poorer,
    /// `own_wealth == peer_wealth`.
    Equal,
    /// Bracket round was uninformative.
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    /// Initial — emit own bracket query.
    PostBracket,
    /// Awaiting peer's bracket query AND commit.
    AwaitPeerBracket,
    /// Peer bracket query in — emit own commit.
    PostCommit,
    /// Peer commit in — emit own reveal.
    PostReveal,
    /// Peer reveal in — emit operator-bound final.
    PostFinal,
    /// Done.
    Done,
}

/// Yao's Millionaire strategy state machine.
pub struct MillionaireCbclStrategy {
    own_wealth: u64,
    /// Half of the configured wealth range — the only bracket threshold
    /// we use in this simplified single-round protocol.
    threshold: u64,
    own_salt: String,
    own_bit: bool,
    /// Bit answered by the peer, set on receipt of the reveal.
    peer_bit: Option<bool>,
    phase: Phase,
}

impl MillionaireCbclStrategy {
    /// Construct with a configured wealth range. Setup will supply the
    /// own-wealth value.
    pub fn new(wealth_range: u64) -> Self {
        let threshold = wealth_range / 2;
        Self {
            own_wealth: 0,
            threshold,
            own_salt: String::new(),
            own_bit: false,
            peer_bit: None,
            phase: Phase::PostBracket,
        }
    }

    fn verdict(&self) -> YaoVerdict {
        let Some(peer) = self.peer_bit else {
            return YaoVerdict::Unknown;
        };
        match (self.own_bit, peer) {
            (true, false) => YaoVerdict::Richer,
            (false, true) => YaoVerdict::Poorer,
            (true, true) | (false, false) => YaoVerdict::Unknown,
        }
    }
}

impl ChallengeStrategy for MillionaireCbclStrategy {
    type Setup = u64;
    type Guess = YaoVerdict;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.own_wealth = setup;
        self.own_bit = setup >= self.threshold;
    }

    fn ingest_inbound(&mut self, msg: &Message) {
        let inner = msg.innermost_simple().unwrap_or(msg);
        let Some(perf) = inner.performative() else {
            return;
        };
        match perf.name() {
            "yao-bracket-reveal" => {
                if let Some(bit_e) = content::get_kw(inner, "bit") {
                    if let Some(b) = content::as_bool(bit_e) {
                        self.peer_bit = Some(b);
                    }
                }
            }
            "yao-bracket" | "yao-bracket-commit" => {
                // No state mutation needed beyond protocol acknowledgement.
            }
            _ => {}
        }
    }

    fn next_outbound(&mut self, rng: &mut dyn RngCore) -> Option<OutboundDraft> {
        match self.phase {
            Phase::PostBracket => {
                self.own_salt = format!("salt-{:016x}", rng.next_u64());
                self.phase = Phase::AwaitPeerBracket;
                Some(OutboundDraft {
                    performative: "yao-bracket".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form(
                        "threshold-query",
                        &[
                            ("round", SExpr::Atom(Atom::Num(0))),
                            ("threshold", SExpr::Atom(Atom::Num(self.threshold as i64))),
                        ],
                    ),
                    caused_by: CausedBySelector::Begin,
                })
            }
            Phase::AwaitPeerBracket => {
                // We don't need to gate on the peer's bracket arriving —
                // both agents post simultaneously and we treat each agent's
                // commit as causedby its own bracket.
                self.phase = Phase::PostCommit;
                self.next_outbound(rng)
            }
            Phase::PostCommit => {
                let bit_byte = if self.own_bit { 1u8 } else { 0u8 };
                let mut buf = self.own_salt.as_bytes().to_vec();
                buf.push(bit_byte);
                let commitment = super::strategy_hash(&buf);
                self.phase = Phase::PostReveal;
                Some(OutboundDraft {
                    performative: "yao-bracket-commit".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form(
                        "threshold-commitment",
                        &[
                            ("round", SExpr::Atom(Atom::Num(0))),
                            ("commitment", SExpr::Atom(Atom::Str(commitment))),
                        ],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative(
                        "yao-bracket".to_string(),
                    ),
                })
            }
            Phase::PostReveal => {
                self.phase = Phase::PostFinal;
                Some(OutboundDraft {
                    performative: "yao-bracket-reveal".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form(
                        "threshold-answer",
                        &[
                            ("round", SExpr::Atom(Atom::Num(0))),
                            ("bit", SExpr::Atom(Atom::Bool(self.own_bit))),
                            ("salt", SExpr::Atom(Atom::Str(self.own_salt.clone()))),
                        ],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative(
                        "yao-bracket-commit".to_string(),
                    ),
                })
            }
            Phase::PostFinal => {
                if self.peer_bit.is_none() {
                    // Peer hasn't revealed yet — yield and wait for next turn.
                    return None;
                }
                let v = self.verdict();
                let v_str = match v {
                    YaoVerdict::Richer => "richer",
                    YaoVerdict::Poorer => "poorer",
                    YaoVerdict::Equal => "equal",
                    YaoVerdict::Unknown => "unknown",
                };
                self.phase = Phase::Done;
                Some(OutboundDraft {
                    performative: "yao-final".to_string(),
                    recipient: Some("@operator".to_string()),
                    content: content::keyword_form(
                        "richer-verdict",
                        &[("verdict", SExpr::Atom(Atom::Symbol(v_str.to_string())))],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative(
                        "yao-bracket-reveal".to_string(),
                    ),
                })
            }
            Phase::Done => None,
        }
    }

    fn final_guess(&self) -> Self::Guess {
        self.verdict()
    }

    fn is_done(&self) -> bool {
        self.phase == Phase::Done
    }
}
