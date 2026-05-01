//! Dining Cryptographers [`ProtocolAdapter`] for [`crate::llm::DisciplinedSeat`].
//!
//! Eight-performative DC-net protocol per `demo/dialects/dining.cbcl`:
//!
//! ```text
//! begin
//!   ↓
//! (any dc-mask-12 dc-mask-13 dc-mask-23)
//!   ↓ (all three pair-masks committed)
//! (any dc-reveal-12 dc-reveal-13 dc-reveal-23)
//!   ↓ (all three pair-reveals exchanged)
//! dc-announce
//!   ↓
//! dc-final
//! ```
//!
//! ## Seat role
//!
//! [`crate::llm::DisciplinedSeat`] is hard-wired to `agent_idx == 0` —
//! i.e. diner 1 (1-indexed). Diner 1 is in pairs `(1,2)` and `(1,3)`,
//! so this adapter emits `dc-mask-12 + dc-mask-13` for the commit
//! step and the matching reveals.
//!
//! ## Tool surface
//!
//! Four tools, with the shim handling the multi-emission internally:
//!
//! - `commit_masks` — emits `dc-mask-12` + `dc-mask-13` back-to-back.
//! - `reveal_masks` — emits `dc-reveal-12` + `dc-reveal-13`.
//! - `announce` — emits `dc-announce` with `a_i = paid ⊕ pair_bits`.
//! - `submit_verdict` — emits `dc-final` and ends the protocol.
//!
//! ## Hash bindings (must match `crate::agents::cbcl::dining`)
//!
//! - Pair bit: `parity(last hex digit of strategy_hash("{pair_seed}|{pair_label}"))`.
//! - Mask commitment: `strategy_hash(salt_bytes ++ [bit_byte])` — bare
//!   FNV-1a-128 hex (no `h` prefix).
//! - Canonical content hash for `:caused-by`: FNV-1a-128 of canonical
//!   serialised payload, prefixed `h`.

use std::collections::BTreeMap;

use crate::llm::{FunctionDef, ProtocolAdapter, ToolCall, ToolDef, ToolDispatch, ToolKind};
use crate::operator::dining::{DiningGuess, DiningSetup};

/// Shared pair seed used across all three diners. Matches the value
/// hard-wired in `crate::measurement::DiningSeat::ingest_setup` so the
/// LLM seat's pair bits agree with the deterministic CBCL peer's.
const PAIR_SEED: &str = "dc-game-shared-seed";

/// All three pair labels in canonical order.
const ALL_PAIR_LABELS: &[&str] = &["1-2", "1-3", "2-3"];

/// System prompt template.
const DC_SYSTEM_TEMPLATE: &str = "You are diner 1 in the Dining Cryptographers Protocol with three diners (you are diner 1; the other diners are diner 2 and diner 3). {PAID_LINE} Pairwise random bits between you and each other diner are derived deterministically from a public seed (the shim handles this). The chat channel uses a strict protocol with eight performatives: dc-mask-12, dc-mask-13, dc-mask-23, dc-reveal-12, dc-reveal-13, dc-reveal-23, dc-announce, dc-final. You communicate ONLY by calling tools. Step 1: call commit_masks \u{2014} the shim emits salted-hash commitments for both your pairs (1-2) and (1-3). Step 2 (after all three pair-masks are observed on the wire): call reveal_masks \u{2014} the shim emits your bits and salts. Step 3 (after all three pair-reveals are observed): call announce \u{2014} the shim emits a_i = paid_bit XOR pair_bits. Step 4 (after both peer announcements are observed): XOR all three announce bits. If the result is 1, a diner paid (verdict \"internal\"); if the result is 0, an outsider paid (verdict \"external\"). Call submit_verdict with the verdict.";

/// Phase of the DC seat.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    /// Awaiting LLM to call `commit_masks`.
    NeedCommit,
    /// Awaiting LLM to call `reveal_masks`.
    NeedReveal,
    /// Awaiting LLM to call `announce`.
    NeedAnnounce,
    /// Awaiting LLM to call `submit_verdict`.
    NeedFinal,
    /// Protocol complete.
    Done,
}

/// DC [`ProtocolAdapter`] (diner 1 role).
pub struct DiningDisciplinedAdapter {
    setup: Option<DiningSetup>,
    /// Pair bits this diner is part of: `(pair_label, bit)`.
    pair_bits: BTreeMap<&'static str, bool>,
    /// Per-pair salt for mask commitments.
    pair_salts: BTreeMap<&'static str, String>,
    /// Per-pair-mask sender count: `pair_label → number of senders`.
    /// One pair receives a mask from each of its two members; we count
    /// distinct senders per pair to track the all-three-masks barrier.
    masks_seen: BTreeMap<&'static str, usize>,
    /// Per-pair-reveal sender count.
    reveals_seen: BTreeMap<&'static str, usize>,
    /// Number of `dc-announce` payloads observed (own + peers).
    announces_seen: u8,
    /// XOR accumulator over observed `dc-announce :bit` values.
    announce_xor: bool,
    /// Own canonical hashes for `:caused-by`.
    own_hashes: BTreeMap<String, String>,
    /// Peer canonical hashes for `:caused-by`.
    peer_hashes: BTreeMap<String, String>,
    thread_id: String,
    sender_id: String,
    phase: Phase,
    final_guess: Option<DiningGuess>,
    salt_counter: u64,
    done: bool,
}

impl DiningDisciplinedAdapter {
    /// Construct a new DC adapter for diner 1 (agent_idx=0).
    /// Conventional values: `("dc-game", "diner-1")`.
    pub fn new(thread_id: impl Into<String>, sender_id: impl Into<String>) -> Self {
        Self {
            setup: None,
            pair_bits: BTreeMap::new(),
            pair_salts: BTreeMap::new(),
            masks_seen: BTreeMap::new(),
            reveals_seen: BTreeMap::new(),
            announces_seen: 0,
            announce_xor: false,
            own_hashes: BTreeMap::new(),
            peer_hashes: BTreeMap::new(),
            thread_id: thread_id.into(),
            sender_id: sender_id.into(),
            phase: Phase::NeedCommit,
            final_guess: None,
            salt_counter: 0,
            done: false,
        }
    }

    /// Pair labels this diner is in. Diner 1 is in (1,2) and (1,3).
    fn own_pair_labels() -> &'static [&'static str] {
        &["1-2", "1-3"]
    }

    /// Derive the pair bit for a given pair label. Matches
    /// `DiningCbclStrategy::pair_bit` byte-for-byte.
    fn derive_pair_bit(pair_label: &str) -> bool {
        let key = format!("{}|{}", PAIR_SEED, pair_label);
        let h = fnv1a_bare_hex(key.as_bytes());
        h.bytes().last().map(|b| b & 1 == 1).unwrap_or(false)
    }

    /// Sample a deterministic salt for the next emission.
    fn sample_salt(&mut self) -> String {
        use sha2::Digest;
        let mut hasher = sha2::Sha256::new();
        hasher.update(b"dc-salt:");
        hasher.update(self.thread_id.as_bytes());
        hasher.update(b":");
        hasher.update(self.sender_id.as_bytes());
        hasher.update(b":");
        hasher.update(self.salt_counter.to_le_bytes());
        let out = hasher.finalize();
        self.salt_counter = self.salt_counter.saturating_add(1);
        let mut s = String::with_capacity(32);
        for b in out.iter().take(16) {
            s.push_str(&format!("{:02x}", b));
        }
        s
    }

    /// Build canonical-form DC message + h-hash.
    fn build_canonical(
        &self,
        perf: &str,
        recipient: &str,
        content_inner: &str,
        caused_by: &str,
    ) -> (String, String) {
        let raw = format!(
            "({perf} {recipient} {content_inner} :thread \"{thread}\" :sender \"{sender}\" :caused-by {cb})",
            thread = self.thread_id,
            sender = self.sender_id,
            cb = caused_by,
        );
        let canonical = match cbcl_parser::parse(&raw)
            .ok()
            .and_then(|s| cbcl_parser::parse_message(&s).ok())
        {
            Some(m) => {
                let inner = m.innermost_simple().unwrap_or(&m).clone();
                cbcl_core::serializer::serialize(&cbcl_core::sexpr::SExpr::from(&inner))
            }
            None => raw,
        };
        let hash = fnv1a_h_hex(canonical.as_bytes());
        (canonical, hash)
    }

    /// `:caused-by` selector for the named outgoing performative under
    /// the dialect's fan-in chain. `dc-mask-XY` follows `begin`;
    /// `dc-reveal-XY` follows any `dc-mask-*` (we use the most-recent
    /// own mask hash); `dc-announce` follows any `dc-reveal-*`;
    /// `dc-final` follows `dc-announce`.
    fn caused_by_for(&self, name: &str) -> String {
        let pred_perf = match name {
            n if n.starts_with("dc-mask-") => return "begin".to_string(),
            n if n.starts_with("dc-reveal-") => "dc-mask",
            "dc-announce" => "dc-reveal",
            "dc-final" => "dc-announce",
            _ => return "begin".to_string(),
        };
        // Pick any own predecessor of the right family. We store own
        // hashes keyed by full performative name (e.g. "dc-mask-12").
        for (perf, h) in self.own_hashes.iter().rev() {
            if perf.starts_with(pred_perf) {
                return h.clone();
            }
        }
        for (perf, h) in self.peer_hashes.iter().rev() {
            if perf.starts_with(pred_perf) {
                return h.clone();
            }
        }
        "begin".to_string()
    }

    /// Announce bit `a_i = paid ⊕ pair_bits` per the DC-net algorithm.
    fn own_announce_bit(&self) -> bool {
        let paid = self.setup.as_ref().map(|s| s.paid).unwrap_or(false);
        let mut bit = paid;
        for (_, b) in self.pair_bits.iter() {
            bit ^= *b;
        }
        bit
    }

    fn pair_bit_for(&self, pair_label: &'static str) -> bool {
        *self
            .pair_bits
            .get(pair_label)
            .expect("pair_bits initialised in ingest_setup")
    }

    /// Emit own commitments for the pairs this diner is in.
    fn emit_own_masks(&mut self, emit: &mut dyn FnMut(Vec<u8>)) {
        for &label in Self::own_pair_labels() {
            // Sample salt + compute commitment.
            let salt = if let Some(s) = self.pair_salts.get(label) {
                s.clone()
            } else {
                let s = self.sample_salt();
                self.pair_salts.insert(label, s.clone());
                s
            };
            let bit = self.pair_bit_for(label);
            let mut buf = salt.as_bytes().to_vec();
            buf.push(if bit { 1u8 } else { 0u8 });
            let commitment = fnv1a_bare_hex(&buf);
            let perf = format!("dc-mask-{}", label.replace('-', ""));
            let cb = self.caused_by_for(&perf);
            let (payload, hash) = self.build_canonical(
                &perf,
                "@peers",
                &format!(
                    "(pair-mask :pair \"{label}\" :commitment \"{commitment}\")"
                ),
                &cb,
            );
            self.own_hashes.insert(perf.clone(), hash);
            // Bump own contribution to masks_seen.
            *self.masks_seen.entry(label).or_insert(0) += 1;
            emit(payload.into_bytes());
        }
    }

    /// Emit own reveals.
    fn emit_own_reveals(&mut self, emit: &mut dyn FnMut(Vec<u8>)) {
        for &label in Self::own_pair_labels() {
            let salt = self
                .pair_salts
                .get(label)
                .cloned()
                .unwrap_or_else(|| {
                    // Should not happen if commit ran first; fall back.
                    let s = self.sample_salt();
                    self.pair_salts.insert(label, s.clone());
                    s
                });
            let bit = self.pair_bit_for(label);
            let perf = format!("dc-reveal-{}", label.replace('-', ""));
            let cb = self.caused_by_for(&perf);
            let (payload, hash) = self.build_canonical(
                &perf,
                "@peers",
                &format!(
                    "(pair-reveal :pair \"{label}\" :bit {bit} :salt \"{salt}\")"
                ),
                &cb,
            );
            self.own_hashes.insert(perf.clone(), hash);
            *self.reveals_seen.entry(label).or_insert(0) += 1;
            emit(payload.into_bytes());
        }
    }
}

impl ProtocolAdapter for DiningDisciplinedAdapter {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        // Initialise pair bits for the seat's two pairs.
        for &label in Self::own_pair_labels() {
            self.pair_bits
                .insert(label, Self::derive_pair_bit(label));
        }
        self.setup = Some(setup);
    }

    fn build_system_prompt(&self) -> String {
        let paid = self.setup.as_ref().map(|s| s.paid).unwrap_or(false);
        let paid_line = if paid {
            "You paid the bill (your private bit is 1)."
        } else {
            "You did NOT pay the bill (your private bit is 0)."
        };
        DC_SYSTEM_TEMPLATE.replace("{PAID_LINE}", paid_line)
    }

    fn tools(&self) -> Vec<ToolDef> {
        let f = |name: &str, desc: &str, params: serde_json::Value| ToolDef {
            kind: "function".into(),
            function: FunctionDef {
                name: name.into(),
                description: desc.into(),
                parameters: params,
            },
        };
        let no_params = serde_json::json!({"type":"object","properties":{},"required":[]});
        vec![
            f(
                "commit_masks",
                "Emit hash commitments for both your pair-masks. The shim derives the pair bits from the public seed, samples salts, computes H(salt || bit), and emits dc-mask-12 then dc-mask-13 on your behalf.",
                no_params.clone(),
            ),
            f(
                "reveal_masks",
                "Emit reveals (bit + salt) for both your pair-masks. The shim emits dc-reveal-12 then dc-reveal-13. Call this only after all three pair-masks are observed on the wire.",
                no_params.clone(),
            ),
            f(
                "announce",
                "Emit your DC-net announcement a_i = paid_bit XOR pair_bits. The shim computes the bit from your setup and pair bits. Call this only after all three pair-reveals are observed.",
                no_params,
            ),
            f(
                "submit_verdict",
                "Submit the operator-bound verdict. Compute it from the XOR of all three observed announce bits: 1 \u{21d2} \"internal\" (a diner paid); 0 \u{21d2} \"external\" (an outsider paid). Use \"unknown\" if you have not observed all three announces.",
                serde_json::json!({
                    "type":"object",
                    "properties": {
                        "verdict": {
                            "type":"string",
                            "enum":["external","internal","unknown"],
                            "description":"One of external / internal / unknown."
                        }
                    },
                    "required":["verdict"],
                }),
            ),
        ]
    }

    fn observe_inbound(&mut self, payload: &[u8]) -> String {
        let payload_str = String::from_utf8_lossy(payload).to_string();
        let parsed = parse_dc_message(&payload_str);
        if let Some(msg) = &parsed {
            let perf_key = match msg {
                ParsedMsg::Mask { pair, .. } => format!("dc-mask-{}", pair.replace('-', "")),
                ParsedMsg::Reveal { pair, .. } => format!("dc-reveal-{}", pair.replace('-', "")),
                ParsedMsg::Announce { .. } => "dc-announce".into(),
                ParsedMsg::Final { .. } => "dc-final".into(),
            };
            let h = canonical_hash_of(&payload_str)
                .unwrap_or_else(|| fnv1a_h_hex(payload_str.as_bytes()));
            self.peer_hashes.entry(perf_key).or_insert(h);
            match msg {
                ParsedMsg::Mask { pair, .. } => {
                    if let Some(label) = ALL_PAIR_LABELS.iter().find(|l| **l == pair) {
                        *self.masks_seen.entry(*label).or_insert(0) += 1;
                    }
                }
                ParsedMsg::Reveal { pair, .. } => {
                    if let Some(label) = ALL_PAIR_LABELS.iter().find(|l| **l == pair) {
                        *self.reveals_seen.entry(*label).or_insert(0) += 1;
                    }
                }
                ParsedMsg::Announce { bit } => {
                    self.announces_seen = self.announces_seen.saturating_add(1);
                    self.announce_xor ^= *bit;
                }
                ParsedMsg::Final { .. } => {}
            }
        }
        match parsed {
            Some(ParsedMsg::Mask { pair, commitment }) => format!(
                "(peer sent dc-mask-{} :pair \"{}\" :commitment \"{commitment}\")",
                pair.replace('-', ""),
                pair
            ),
            Some(ParsedMsg::Reveal { pair, bit, salt }) => format!(
                "(peer sent dc-reveal-{} :pair \"{}\" :bit {bit} :salt \"{salt}\")",
                pair.replace('-', ""),
                pair
            ),
            Some(ParsedMsg::Announce { bit }) => format!("(peer sent dc-announce :bit {bit})"),
            Some(ParsedMsg::Final { verdict }) => format!("(peer sent dc-final :verdict {verdict})"),
            None => format!("(quarantined: unparseable inbound: {:?})", payload_str),
        }
    }

    fn kickoff_prompt(&self) -> String {
        "All three diners are seated. Begin the protocol by calling commit_masks.".to_string()
    }

    fn idle_prompt(&self) -> Option<String> {
        Some(match self.phase {
            Phase::NeedCommit => "Begin: call commit_masks.".to_string(),
            Phase::NeedReveal => {
                let covered = ALL_PAIR_LABELS
                    .iter()
                    .filter(|l| self.masks_seen.get(*l).copied().unwrap_or(0) > 0)
                    .count();
                if covered == 3 {
                    "All three pair-masks are committed. Call reveal_masks to advance.".to_string()
                } else {
                    format!(
                        "Awaiting peer pair-masks ({}/3 pair labels covered). Call reveal_masks once all three are in.",
                        covered
                    )
                }
            }
            Phase::NeedAnnounce => {
                let covered = ALL_PAIR_LABELS
                    .iter()
                    .filter(|l| self.reveals_seen.get(*l).copied().unwrap_or(0) >= 2)
                    .count();
                if covered == 3 {
                    "All three pair-reveals are exchanged. Call announce.".to_string()
                } else {
                    format!(
                        "Awaiting peer pair-reveals ({}/3 pair labels fully revealed). Call announce once all three are in.",
                        covered
                    )
                }
            }
            Phase::NeedFinal => {
                if self.announces_seen >= 3 {
                    let xor = self.announce_xor;
                    format!(
                        "All three announcements observed. XOR = {xor}. Call submit_verdict with \"{}\" .",
                        if xor { "internal" } else { "external" }
                    )
                } else {
                    "Awaiting peer announcements. Call submit_verdict once all three are in.".to_string()
                }
            }
            Phase::Done => return None,
        })
    }

    fn classify_tool(&self, _name: &str) -> ToolKind {
        ToolKind::Protocol
    }

    fn dispatch_tool(
        &mut self,
        tc: &ToolCall,
        emit: &mut dyn FnMut(Vec<u8>),
    ) -> ToolDispatch {
        let args: serde_json::Value =
            serde_json::from_str(&tc.function.arguments).unwrap_or(serde_json::Value::Null);

        match tc.function.name.as_str() {
            "commit_masks" => {
                if !matches!(self.phase, Phase::NeedCommit) {
                    return ToolDispatch {
                        ack: "ignored: commit_masks out of phase".into(),
                    };
                }
                self.emit_own_masks(emit);
                self.phase = Phase::NeedReveal;
                ToolDispatch {
                    ack: "ok: dc-mask-12 + dc-mask-13 sent".into(),
                }
            }
            "reveal_masks" => {
                if !matches!(self.phase, Phase::NeedReveal) {
                    return ToolDispatch {
                        ack: "ignored: reveal_masks out of phase".into(),
                    };
                }
                self.emit_own_reveals(emit);
                self.phase = Phase::NeedAnnounce;
                ToolDispatch {
                    ack: "ok: dc-reveal-12 + dc-reveal-13 sent".into(),
                }
            }
            "announce" => {
                if !matches!(self.phase, Phase::NeedAnnounce) {
                    return ToolDispatch {
                        ack: "ignored: announce out of phase".into(),
                    };
                }
                let bit = self.own_announce_bit();
                self.announces_seen = self.announces_seen.saturating_add(1);
                self.announce_xor ^= bit;
                let cb = self.caused_by_for("dc-announce");
                let (payload, hash) = self.build_canonical(
                    "dc-announce",
                    "@peers",
                    &format!("(announcement :bit {bit})"),
                    &cb,
                );
                self.own_hashes.insert("dc-announce".into(), hash);
                emit(payload.into_bytes());
                self.phase = Phase::NeedFinal;
                ToolDispatch {
                    ack: format!("ok: dc-announce sent (own bit = {bit})"),
                }
            }
            "submit_verdict" => {
                if !matches!(self.phase, Phase::NeedFinal) {
                    return ToolDispatch {
                        ack: "ignored: submit_verdict out of phase".into(),
                    };
                }
                let v = args
                    .get("verdict")
                    .and_then(|v| v.as_str())
                    .unwrap_or("unknown")
                    .to_lowercase();
                let verdict = match v.as_str() {
                    "external" => DiningGuess::External,
                    "internal" => DiningGuess::Internal,
                    _ => DiningGuess::Unknown,
                };
                let v_str = match verdict {
                    DiningGuess::External => "external",
                    DiningGuess::Internal => "internal",
                    DiningGuess::InviteCode(_) => "internal", // never produced by this adapter
                    DiningGuess::Unknown => "unknown",
                };
                self.final_guess = Some(verdict);
                let cb = self.caused_by_for("dc-final");
                let (payload, hash) = self.build_canonical(
                    "dc-final",
                    "@operator",
                    &format!("(paid-verdict :verdict {v_str})"),
                    &cb,
                );
                self.own_hashes.insert("dc-final".into(), hash);
                emit(payload.into_bytes());
                self.phase = Phase::Done;
                self.done = true;
                ToolDispatch {
                    ack: "ok: dc-final sent; protocol complete".into(),
                }
            }
            other => ToolDispatch {
                ack: format!("ignored: unknown tool {other}"),
            },
        }
    }

    fn is_done(&self) -> bool {
        self.done
    }

    fn final_guess(&self) -> Self::Guess {
        self.final_guess.clone().unwrap_or(DiningGuess::Unknown)
    }
}

/// Inbound parse cases for DC.
#[derive(Clone, Debug)]
enum ParsedMsg {
    Mask {
        pair: String,
        commitment: String,
    },
    Reveal {
        pair: String,
        bit: bool,
        salt: String,
    },
    Announce {
        bit: bool,
    },
    Final {
        verdict: String,
    },
}

/// Best-effort DC inbound parse.
fn parse_dc_message(payload: &str) -> Option<ParsedMsg> {
    let p = payload.trim();
    if p.contains("dc-final") || p.contains("paid-verdict") {
        let verdict = extract_kw(p, "verdict")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        return Some(ParsedMsg::Final { verdict });
    }
    if p.contains("dc-announce") || p.contains("(announcement") {
        let bit = extract_kw(p, "bit")
            .map(|s| matches!(s.trim_matches('"'), "true" | "1" | "yes"))
            .unwrap_or(false);
        return Some(ParsedMsg::Announce { bit });
    }
    if p.contains("pair-reveal") || p.contains("dc-reveal-") {
        let pair = extract_kw(p, "pair")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        let bit = extract_kw(p, "bit")
            .map(|s| matches!(s.trim_matches('"'), "true" | "1" | "yes"))
            .unwrap_or(false);
        let salt = extract_kw(p, "salt")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        return Some(ParsedMsg::Reveal { pair, bit, salt });
    }
    if p.contains("pair-mask") || p.contains("dc-mask-") {
        let pair = extract_kw(p, "pair")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        let commitment = extract_kw(p, "commitment")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        return Some(ParsedMsg::Mask { pair, commitment });
    }
    None
}

/// Extract `:key value` (raw token; quotes intact).
fn extract_kw(payload: &str, key: &str) -> Option<String> {
    let needle = format!(":{}", key);
    let idx = payload.find(&needle)?;
    let after = &payload[idx + needle.len()..];
    let after = after.trim_start();
    if after.starts_with('"') {
        let rest = &after[1..];
        let end = rest.find('"')?;
        return Some(rest[..end].to_string());
    }
    let end = after
        .find(|c: char| c.is_whitespace() || c == ')')
        .unwrap_or(after.len());
    Some(after[..end].to_string())
}

/// FNV-1a-128 of canonical content bytes, prefixed `h`.
fn fnv1a_h_hex(bytes: &[u8]) -> String {
    const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
    const PRIME: u128 = 0x0000000001000000000000000000013b;
    let mut h: u128 = OFFSET;
    for &b in bytes {
        h ^= b as u128;
        h = h.wrapping_mul(PRIME);
    }
    format!("h{:032x}", h)
}

/// FNV-1a-128 bare hex (matches `super::strategy_hash`).
fn fnv1a_bare_hex(bytes: &[u8]) -> String {
    const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
    const PRIME: u128 = 0x0000000001000000000000000000013b;
    let mut h: u128 = OFFSET;
    for &b in bytes {
        h ^= b as u128;
        h = h.wrapping_mul(PRIME);
    }
    format!("{:032x}", h)
}

/// Canonical hash of an inbound parseable payload.
fn canonical_hash_of(payload: &str) -> Option<String> {
    let sexpr = cbcl_parser::parse(payload).ok()?;
    let msg = cbcl_parser::parse_message(&sexpr).ok()?;
    let inner = msg.innermost_simple().unwrap_or(&msg).clone();
    let canonical =
        cbcl_core::serializer::serialize(&cbcl_core::sexpr::SExpr::from(&inner));
    Some(fnv1a_h_hex(canonical.as_bytes()))
}
