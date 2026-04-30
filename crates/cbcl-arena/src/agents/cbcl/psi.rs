//! psi: PSI strategy for the CBCL-disciplined agent (REQ-1110-paired).
//!
//! Implements the bracket-and-narrow-style PSI handshake described in
//! `demo/dialects/psi.cbcl`:
//!
//! ```text
//! psi-salt → psi-commit → psi-reveal → psi-claim → psi-final
//! ```
//!
//! - **Setup.** Receive own set `A` and pick a fresh 64-bit salt.
//! - **psi-salt.** Both sides post their proposed salt. Lex-min wins.
//! - **psi-commit.** After both salts land, compute the common salt,
//!   build `H(salt || elem)` for each elem in `A`, sort the digest list,
//!   take the head as the "Merkle root" surrogate, post root + count.
//! - **psi-reveal.** Post the full sorted digest list.
//! - **psi-claim.** Compute the intersection (digests that appear in both
//!   reveal lists, mapped back to plaintexts in `A`), post it.
//! - **psi-final.** Submit the same intersection to the operator.
//!
//! NOTE on commitments. The dialect comment refers to a Merkle root; a
//! single-bucket "root = first sorted hash" surrogate is sufficient for
//! the simulator's discipline-checking purpose. The strategy hashes leaves
//! using the same FNV-1a 128 we use for `:caused-by` content hashes — see
//! the parent module for the rationale (NFR-1112: no new deps).

use std::collections::BTreeSet;

use cbcl_core::message::Message;
use cbcl_core::sexpr::{Atom, SExpr};
use rand::RngCore;

use super::content;
use super::CausedBySelector;
use super::ChallengeStrategy;
use super::OutboundDraft;

/// PSI strategy phases.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    /// Initial state — emit own salt.
    PostSalt,
    /// Awaiting peer salt.
    AwaitPeerSalt,
    /// Both salts in — emit own commit.
    PostCommit,
    /// Awaiting peer commit.
    AwaitPeerCommit,
    /// Peer commit in — emit own reveal.
    PostReveal,
    /// Awaiting peer reveal.
    AwaitPeerReveal,
    /// Peer reveal in — emit own claim.
    PostClaim,
    /// Awaiting peer claim.
    AwaitPeerClaim,
    /// Peer claim in — emit operator-bound final.
    PostFinal,
    /// Strategy complete.
    Done,
}

/// PSI strategy state machine.
pub struct PsiCbclStrategy {
    /// Own private set.
    own_set: Vec<String>,
    /// Own fresh salt — chosen during `ingest_setup`.
    own_salt: String,
    /// Peer's salt, set on receipt.
    peer_salt: Option<String>,
    /// Common salt (lex-min of own and peer).
    common_salt: Option<String>,
    /// Own sorted digest list (post-common-salt).
    own_digests: Vec<String>,
    /// Peer's reveal-list of digests, set on receipt.
    peer_digests: Option<Vec<String>>,
    /// Peer's claimed intersection, set on receipt.
    peer_claim: Option<Vec<String>>,
    /// Computed intersection plaintexts.
    intersection: Vec<String>,
    /// Phase of the handshake.
    phase: Phase,
}

impl PsiCbclStrategy {
    /// Construct a new PSI strategy. The set is supplied here for
    /// convenience; if the operator's `Setup` carries the set the agent
    /// re-loads it via `ingest_setup`.
    pub fn new() -> Self {
        Self {
            own_set: Vec::new(),
            own_salt: String::new(),
            peer_salt: None,
            common_salt: None,
            own_digests: Vec::new(),
            peer_digests: None,
            peer_claim: None,
            intersection: Vec::new(),
            phase: Phase::PostSalt,
        }
    }

    fn rebuild_digests(&mut self) {
        let salt = match &self.common_salt {
            Some(s) => s.clone(),
            None => return,
        };
        let mut digests: Vec<String> = self
            .own_set
            .iter()
            .map(|e| salt_hash(&salt, e))
            .collect();
        digests.sort();
        self.own_digests = digests;
    }
}

impl Default for PsiCbclStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl ChallengeStrategy for PsiCbclStrategy {
    type Setup = Vec<String>;
    type Guess = Vec<String>;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.own_set = setup;
        // The salt is generated in next_outbound when we have access to rng.
    }

    fn ingest_inbound(&mut self, msg: &Message) {
        let inner = msg.innermost_simple().unwrap_or(msg);
        let perf = match inner.performative() {
            Some(p) => p.name().to_string(),
            None => return,
        };
        match perf.as_str() {
            "psi-salt" => {
                if self.peer_salt.is_some() {
                    return;
                }
                if let Some(salt_e) = content::get_kw(inner, "salt") {
                    if let Some(salt) = content::as_string(salt_e) {
                        self.peer_salt = Some(salt);
                        // Compute common salt once both are present.
                        if !self.own_salt.is_empty() {
                            self.common_salt = Some(min_lex(
                                &self.own_salt,
                                self.peer_salt.as_ref().unwrap(),
                            ));
                            self.rebuild_digests();
                        }
                    }
                }
            }
            "psi-commit" => {
                // We trust the commit; reveal verification is implicit (we
                // compare full digest lists at psi-reveal time).
            }
            "psi-reveal" => {
                if let Some(hashes_e) = content::get_kw(inner, "hashes") {
                    if let Some(hs) = content::as_string_list(hashes_e) {
                        self.peer_digests = Some(hs);
                    }
                }
            }
            "psi-claim" => {
                if let Some(members_e) = content::get_kw(inner, "members") {
                    if let Some(ms) = content::as_string_list(members_e) {
                        self.peer_claim = Some(ms);
                    }
                }
            }
            _ => {}
        }
    }

    fn next_outbound(&mut self, rng: &mut dyn RngCore) -> Option<OutboundDraft> {
        match self.phase {
            Phase::PostSalt => {
                // Generate own salt now (deferred from ingest_setup so we
                // can use the strategy rng).
                if self.own_salt.is_empty() {
                    self.own_salt = format!("salt-{:016x}", rng.next_u64());
                }
                self.phase = Phase::AwaitPeerSalt;
                Some(OutboundDraft {
                    performative: "psi-salt".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form(
                        "salt-proposal",
                        &[("salt", SExpr::Atom(Atom::Str(self.own_salt.clone())))],
                    ),
                    caused_by: CausedBySelector::Begin,
                })
            }
            Phase::AwaitPeerSalt => {
                if self.peer_salt.is_some() {
                    if self.common_salt.is_none() {
                        self.common_salt = Some(min_lex(
                            &self.own_salt,
                            self.peer_salt.as_ref().unwrap(),
                        ));
                        self.rebuild_digests();
                    }
                    self.phase = Phase::PostCommit;
                    self.next_outbound(rng)
                } else {
                    None
                }
            }
            Phase::PostCommit => {
                let root = self
                    .own_digests
                    .first()
                    .cloned()
                    .unwrap_or_else(|| "empty-root".to_string());
                let count = self.own_digests.len() as i64;
                self.phase = Phase::AwaitPeerCommit;
                Some(OutboundDraft {
                    performative: "psi-commit".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form(
                        "set-commitment",
                        &[
                            ("root", SExpr::Atom(Atom::Str(root))),
                            ("count", SExpr::Atom(Atom::Num(count))),
                        ],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative("psi-salt".to_string()),
                })
            }
            Phase::AwaitPeerCommit => {
                // The peer's psi-commit content carries no information we
                // need to wait on (root + count) since we verify by digest
                // overlap later. Move forward as soon as our store contains
                // a peer psi-commit. Use the strategy's tracked phase: we
                // advance unconditionally so both agents progress in
                // lockstep.
                self.phase = Phase::PostReveal;
                self.next_outbound(rng)
            }
            Phase::PostReveal => {
                let hashes: Vec<SExpr> = self
                    .own_digests
                    .iter()
                    .map(|h| SExpr::Atom(Atom::Str(h.clone())))
                    .collect();
                self.phase = Phase::AwaitPeerReveal;
                Some(OutboundDraft {
                    performative: "psi-reveal".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form(
                        "hash-reveal",
                        &[("hashes", SExpr::List(hashes))],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative("psi-commit".to_string()),
                })
            }
            Phase::AwaitPeerReveal => {
                if let Some(peer_d) = self.peer_digests.clone() {
                    let peer_set: BTreeSet<String> = peer_d.into_iter().collect();
                    let salt = self.common_salt.clone().unwrap_or_default();
                    self.intersection = self
                        .own_set
                        .iter()
                        .filter(|e| peer_set.contains(&salt_hash(&salt, e)))
                        .cloned()
                        .collect();
                    self.intersection.sort();
                    self.phase = Phase::PostClaim;
                    self.next_outbound(rng)
                } else {
                    None
                }
            }
            Phase::PostClaim => {
                let members: Vec<SExpr> = self
                    .intersection
                    .iter()
                    .map(|m| SExpr::Atom(Atom::Str(m.clone())))
                    .collect();
                self.phase = Phase::AwaitPeerClaim;
                Some(OutboundDraft {
                    performative: "psi-claim".to_string(),
                    recipient: Some("@peer".to_string()),
                    content: content::keyword_form(
                        "intersection-claim",
                        &[("members", SExpr::List(members))],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative("psi-reveal".to_string()),
                })
            }
            Phase::AwaitPeerClaim => {
                // Don't gate on peer claim (advance regardless).
                self.phase = Phase::PostFinal;
                self.next_outbound(rng)
            }
            Phase::PostFinal => {
                let members: Vec<SExpr> = self
                    .intersection
                    .iter()
                    .map(|m| SExpr::Atom(Atom::Str(m.clone())))
                    .collect();
                self.phase = Phase::Done;
                Some(OutboundDraft {
                    performative: "psi-final".to_string(),
                    recipient: Some("@operator".to_string()),
                    content: content::keyword_form(
                        "intersection-answer",
                        &[("members", SExpr::List(members))],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative("psi-claim".to_string()),
                })
            }
            Phase::Done => None,
        }
    }

    fn final_guess(&self) -> Self::Guess {
        self.intersection.clone()
    }

    fn is_done(&self) -> bool {
        self.phase == Phase::Done
    }
}

fn min_lex(a: &str, b: &str) -> String {
    if a <= b {
        a.to_string()
    } else {
        b.to_string()
    }
}

fn salt_hash(salt: &str, elem: &str) -> String {
    let mut buf = Vec::with_capacity(salt.len() + 1 + elem.len());
    buf.extend_from_slice(salt.as_bytes());
    buf.push(0);
    buf.extend_from_slice(elem.as_bytes());
    super::strategy_hash(&buf)
}
