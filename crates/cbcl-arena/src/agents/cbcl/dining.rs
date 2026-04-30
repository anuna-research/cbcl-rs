//! dining: Dining Cryptographers strategy for the CBCL-disciplined agent
//! (REQ-1112-paired).
//!
//! Implements the DC-net protocol per `demo/dialects/dining.cbcl`:
//!
//! ```text
//! begin
//!   ↓
//! (any dc-mask-12 dc-mask-13 dc-mask-23)
//!   ↓     [(all dc-mask-12, dc-mask-13, dc-mask-23) barrier]
//! (any dc-reveal-12 dc-reveal-13 dc-reveal-23)
//!   ↓     [(all dc-reveal-12, dc-reveal-13, dc-reveal-23) barrier]
//! dc-announce
//!   ↓
//! dc-final
//! ```
//!
//! ## Pair-bit derivation
//!
//! DC-net requires each pair to share *one* random bit. Both members of a
//! pair must compute the same bit. We derive `r_{ij}` deterministically
//! from a pair seed shared via `Setup::pair_seed`; in tests the operator
//! gives both pair members the same seed. The bit is `H(seed || "i-j") & 1`.
//!
//! ## Announcement
//!
//! Each diner i, in pairs (i,j) and (i,k), computes
//! `a_i = r_{ij} XOR r_{ik} XOR p_i` and emits `(dc-announce :bit a_i)`.
//! The XOR sum of all three announcements is the "anyone paid?" bit.
//!
//! ## Verdict
//!
//! After all three `dc-announce` land, each diner XORs the three bits.
//! - sum = 1 → exactly one diner paid → emit `internal`.
//! - sum = 0 → external paid → emit `external`.
//!
//! Following the task brief's simplified rule: we do not attempt to name a
//! specific payer (which would require additional rounds).

use cbcl_core::message::Message;
use cbcl_core::sexpr::{Atom, SExpr};
use rand::RngCore;

use super::content;
use super::CausedBySelector;
use super::ChallengeStrategy;
use super::OutboundDraft;

/// DC verdict types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DcVerdict {
    /// Outsider paid.
    External,
    /// One of the diners paid (we do not attempt to name them).
    Internal,
    /// Insufficient information.
    Unknown,
}

/// DC strategy setup payload.
#[derive(Clone, Debug)]
pub struct DcSetup {
    /// 1-indexed diner index ∈ {1, 2, 3}.
    pub diner_idx: u8,
    /// Whether this diner paid.
    pub paid: bool,
    /// Shared per-game seed used to derive pair-bits. The operator gives
    /// the same seed to all three diners.
    pub pair_seed: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    PostMasks,
    AwaitMasks,
    PostReveals,
    AwaitReveals,
    PostAnnounce,
    AwaitAnnounces,
    PostFinal,
    Done,
}

/// Pair tag, 1-indexed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pair(pub u8, pub u8);

impl Pair {
    fn label(self) -> String {
        format!("{}-{}", self.0, self.1)
    }
    fn perf_mask(self) -> String {
        format!("dc-mask-{}{}", self.0, self.1)
    }
    fn perf_reveal(self) -> String {
        format!("dc-reveal-{}{}", self.0, self.1)
    }
}

const ALL_PAIRS: [Pair; 3] = [Pair(1, 2), Pair(1, 3), Pair(2, 3)];

/// DC-net strategy state machine.
pub struct DiningCbclStrategy {
    setup: Option<DcSetup>,
    /// Pairs this diner is a member of.
    own_pairs: Vec<Pair>,
    /// Bit assignments per pair (deterministic from seed).
    pair_bits: Vec<(Pair, bool)>,
    /// Salts for own mask commitments.
    own_salts: Vec<(Pair, String)>,
    /// Count of OWN reveal emissions (independent of peer reveals).
    own_reveals_emitted: usize,
    /// Set of pair tags whose `dc-mask-XY` has been seen across all
    /// senders (own + peers).
    masks_seen: [bool; 3],
    /// Set of pair tags whose `dc-reveal-XY` has been seen.
    reveals_seen: [bool; 3],
    /// Per-pair reveal bit observed (used as cross-check; honest peers
    /// produce consistent bits).
    revealed_bit: [Option<bool>; 3],
    /// Number of `dc-announce` messages observed (own + peers).
    announces_seen: u8,
    /// XOR accumulator over observed announce bits.
    announce_xor: bool,
    phase: Phase,
}

impl DiningCbclStrategy {
    /// Construct a new DC strategy.
    pub fn new() -> Self {
        Self {
            setup: None,
            own_pairs: Vec::new(),
            pair_bits: Vec::new(),
            own_salts: Vec::new(),
            own_reveals_emitted: 0,
            masks_seen: [false; 3],
            reveals_seen: [false; 3],
            revealed_bit: [None, None, None],
            announces_seen: 0,
            announce_xor: false,
            phase: Phase::PostMasks,
        }
    }

    fn pair_bit(seed: &str, p: Pair) -> bool {
        let key = format!("{}|{}", seed, p.label());
        let h = super::strategy_hash(key.as_bytes());
        // Take the last hex digit's parity.
        h.bytes().last().map(|b| b & 1 == 1).unwrap_or(false)
    }

    fn own_announce_bit(&self) -> bool {
        let setup = self.setup.as_ref().expect("setup absent");
        let mut bit = setup.paid;
        for (_, b) in &self.pair_bits {
            bit ^= *b;
        }
        bit
    }

    fn pair_idx(p: Pair) -> usize {
        match (p.0, p.1) {
            (1, 2) => 0,
            (1, 3) => 1,
            (2, 3) => 2,
            _ => unreachable!(),
        }
    }

    fn perf_to_pair(perf: &str) -> Option<(Pair, &'static str)> {
        match perf {
            "dc-mask-12" => Some((Pair(1, 2), "mask")),
            "dc-mask-13" => Some((Pair(1, 3), "mask")),
            "dc-mask-23" => Some((Pair(2, 3), "mask")),
            "dc-reveal-12" => Some((Pair(1, 2), "reveal")),
            "dc-reveal-13" => Some((Pair(1, 3), "reveal")),
            "dc-reveal-23" => Some((Pair(2, 3), "reveal")),
            _ => None,
        }
    }
}

impl Default for DiningCbclStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl ChallengeStrategy for DiningCbclStrategy {
    type Setup = DcSetup;
    type Guess = DcVerdict;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        // Determine which pairs this diner is in.
        let i = setup.diner_idx;
        let pairs: Vec<Pair> = ALL_PAIRS
            .iter()
            .copied()
            .filter(|p| p.0 == i || p.1 == i)
            .collect();
        self.pair_bits = pairs
            .iter()
            .map(|p| (*p, Self::pair_bit(&setup.pair_seed, *p)))
            .collect();
        self.own_pairs = pairs;
        // Mark our own masks/reveals as already-seen at completion.
        for p in &self.own_pairs {
            self.masks_seen[Self::pair_idx(*p)] = true;
        }
        self.setup = Some(setup);
    }

    fn ingest_inbound(&mut self, msg: &Message) {
        let inner = msg.innermost_simple().unwrap_or(msg);
        let Some(perf) = inner.performative() else {
            return;
        };
        let perf_name = perf.name();
        if let Some((pair, kind)) = Self::perf_to_pair(perf_name) {
            let idx = Self::pair_idx(pair);
            match kind {
                "mask" => {
                    self.masks_seen[idx] = true;
                }
                "reveal" => {
                    self.reveals_seen[idx] = true;
                    if let Some(bit_e) = content::get_kw(inner, "bit") {
                        if let Some(b) = content::as_bool(bit_e) {
                            self.revealed_bit[idx] = Some(b);
                        }
                    }
                }
                _ => {}
            }
        } else if perf_name == "dc-announce" {
            if let Some(bit_e) = content::get_kw(inner, "bit") {
                if let Some(b) = content::as_bool(bit_e) {
                    self.announces_seen = self.announces_seen.saturating_add(1);
                    self.announce_xor ^= b;
                }
            }
        }
    }

    fn next_outbound(&mut self, rng: &mut dyn RngCore) -> Option<OutboundDraft> {
        match self.phase {
            Phase::PostMasks => {
                // Emit masks for all of own pairs in turn. We maintain
                // remaining-pairs in `own_salts`-empty state.
                if self.own_salts.len() < self.own_pairs.len() {
                    let pair = self.own_pairs[self.own_salts.len()];
                    let salt = format!("salt-{:016x}", rng.next_u64());
                    let bit = self
                        .pair_bits
                        .iter()
                        .find(|(p, _)| *p == pair)
                        .map(|(_, b)| *b)
                        .unwrap_or(false);
                    let bit_byte = if bit { 1u8 } else { 0u8 };
                    let mut buf = salt.as_bytes().to_vec();
                    buf.push(bit_byte);
                    let commitment = super::strategy_hash(&buf);
                    self.own_salts.push((pair, salt));
                    // Mark as locally-seen (own outbound counts).
                    self.masks_seen[Self::pair_idx(pair)] = true;
                    return Some(OutboundDraft {
                        performative: pair.perf_mask(),
                        recipient: Some("@peers".to_string()),
                        content: content::keyword_form(
                            "pair-mask",
                            &[
                                ("pair", SExpr::Atom(Atom::Str(pair.label()))),
                                ("commitment", SExpr::Atom(Atom::Str(commitment))),
                            ],
                        ),
                        caused_by: CausedBySelector::Begin,
                    });
                }
                self.phase = Phase::AwaitMasks;
                self.next_outbound(rng)
            }
            Phase::AwaitMasks => {
                if self.masks_seen.iter().all(|s| *s) {
                    self.phase = Phase::PostReveals;
                    self.next_outbound(rng)
                } else {
                    None
                }
            }
            Phase::PostReveals => {
                // Emit reveals for own pairs.
                if self.own_reveals_emitted < self.own_pairs.len() {
                    let pair = self.own_pairs[self.own_reveals_emitted];
                    self.own_reveals_emitted += 1;
                    let bit = self
                        .pair_bits
                        .iter()
                        .find(|(p, _)| *p == pair)
                        .map(|(_, b)| *b)
                        .unwrap_or(false);
                    let salt = self
                        .own_salts
                        .iter()
                        .find(|(p, _)| *p == pair)
                        .map(|(_, s)| s.clone())
                        .unwrap_or_default();
                    self.reveals_seen[Self::pair_idx(pair)] = true;
                    self.revealed_bit[Self::pair_idx(pair)] = Some(bit);
                    return Some(OutboundDraft {
                        performative: pair.perf_reveal(),
                        recipient: Some("@peers".to_string()),
                        content: content::keyword_form(
                            "pair-reveal",
                            &[
                                ("pair", SExpr::Atom(Atom::Str(pair.label()))),
                                ("bit", SExpr::Atom(Atom::Bool(bit))),
                                ("salt", SExpr::Atom(Atom::Str(salt))),
                            ],
                        ),
                        // Reveals require fan-in over all three masks.
                        caused_by: CausedBySelector::AllOfPerformatives(vec![
                            "dc-mask-12".to_string(),
                            "dc-mask-13".to_string(),
                            "dc-mask-23".to_string(),
                        ]),
                    });
                }
                self.phase = Phase::AwaitReveals;
                self.next_outbound(rng)
            }
            Phase::AwaitReveals => {
                if self.reveals_seen.iter().all(|s| *s) {
                    self.phase = Phase::PostAnnounce;
                    self.next_outbound(rng)
                } else {
                    None
                }
            }
            Phase::PostAnnounce => {
                let bit = self.own_announce_bit();
                self.phase = Phase::AwaitAnnounces;
                self.announces_seen = self.announces_seen.saturating_add(1);
                self.announce_xor ^= bit;
                Some(OutboundDraft {
                    performative: "dc-announce".to_string(),
                    recipient: Some("@peers".to_string()),
                    content: content::keyword_form(
                        "announcement",
                        &[("bit", SExpr::Atom(Atom::Bool(bit)))],
                    ),
                    caused_by: CausedBySelector::AllOfPerformatives(vec![
                        "dc-reveal-12".to_string(),
                        "dc-reveal-13".to_string(),
                        "dc-reveal-23".to_string(),
                    ]),
                })
            }
            Phase::AwaitAnnounces => {
                if self.announces_seen >= 3 {
                    self.phase = Phase::PostFinal;
                    self.next_outbound(rng)
                } else {
                    None
                }
            }
            Phase::PostFinal => {
                let verdict = if self.announce_xor {
                    DcVerdict::Internal
                } else {
                    DcVerdict::External
                };
                let v_str = match verdict {
                    DcVerdict::External => "external",
                    DcVerdict::Internal => "internal",
                    DcVerdict::Unknown => "unknown",
                };
                self.phase = Phase::Done;
                Some(OutboundDraft {
                    performative: "dc-final".to_string(),
                    recipient: Some("@operator".to_string()),
                    content: content::keyword_form(
                        "paid-verdict",
                        &[("verdict", SExpr::Atom(Atom::Symbol(v_str.to_string())))],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative(
                        "dc-announce".to_string(),
                    ),
                })
            }
            Phase::Done => None,
        }
    }

    fn final_guess(&self) -> Self::Guess {
        if self.announces_seen < 3 {
            return DcVerdict::Unknown;
        }
        if self.announce_xor {
            DcVerdict::Internal
        } else {
            DcVerdict::External
        }
    }

    fn is_done(&self) -> bool {
        self.phase == Phase::Done
    }
}
