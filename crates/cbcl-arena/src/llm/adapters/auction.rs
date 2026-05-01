//! Sealed-bid auction [`ProtocolAdapter`] for [`crate::llm::DisciplinedSeat`].
//!
//! Three-phase commit / reveal / declare-winner protocol per
//! `demo/dialects/auction.cbcl` (SPEC-004 REQ-410..414):
//!
//! ```text
//! begin
//!   ↓
//! commit (bid-commitment :hash H)
//!   ↓
//! reveal (bid-reveal :body :salt :proof-commit H)
//!   ↓
//! declare-winner (winner-declaration :winner :winning-bid
//!                                    :proof-commit :proof-reveal)
//! ```
//!
//! ## Auctioneer convention
//!
//! By dialect convention the auctioneer is the lowest `agent_idx`. The
//! [`crate::llm::DisciplinedSeat`] always sits at `agent_idx == 0`, so
//! this adapter is implemented for the auctioneer role: commit own bid,
//! reveal it, then collect peer reveals and declare a winner. (A future
//! bidder-only variant would reuse the same parser and hash bindings;
//! the only delta is dropping the `declare_winner` tool.)
//!
//! ## Hash bindings (must match `crates/cbcl-arena/src/agents/cbcl/auction.rs`)
//!
//! - `commit_hash = strategy_hash("{valuation}|{salt}".as_bytes())` — bare
//!   FNV-1a-128 hex (no `h` prefix).
//! - `reveal_hash = strategy_hash("{commit_hash}|{valuation}|{salt}".as_bytes())` —
//!   bare FNV-1a-128 hex (no `h` prefix).
//! - Canonical message digest (used for `:caused-by` resolution) is
//!   `h{32hex}` FNV-1a-128 of the canonical-form serialised message —
//!   same as PSI / Yao adapters.

use std::collections::BTreeMap;

use crate::llm::{FunctionDef, ProtocolAdapter, ToolCall, ToolDef, ToolDispatch, ToolKind};
use crate::operator::auction::{AuctionGuess, AuctionSetup};

/// System prompt template. `{N}`, `{VALUATION}` are filled at runtime.
const AUCTION_SYSTEM_TEMPLATE: &str = "You are the auctioneer in a sealed-bid auction with {N} bidders. You are bidder 0; the other bidders are 1..{N_MINUS_ONE}. Your private valuation is: {VALUATION}. The chat channel uses a strict protocol with three performatives: commit, reveal, declare-winner, in that order. You communicate ONLY by calling tools \u{2014} you cannot send free-form chat messages. Use propose_commit first \u{2014} the shim hashes (valuation || salt) and emits the commitment. Then call propose_reveal \u{2014} the shim emits your valuation, salt, and a proof-commit citation. Once all peer bidders have revealed their valuations, identify the highest-valuation bidder. Then call declare_winner with that bidder's index and bid \u{2014} the shim cites the matching commit and reveal hashes. Ties: lower agent_idx wins.";

/// Phase of the auction seat.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    /// Awaiting LLM to call `propose_commit`.
    NeedCommit,
    /// Awaiting LLM to call `propose_reveal`.
    NeedReveal,
    /// Awaiting LLM to call `declare_winner`.
    NeedDeclare,
    /// Protocol complete.
    Done,
}

/// Sealed-bid auction [`ProtocolAdapter`] (auctioneer role).
pub struct AuctionDisciplinedAdapter {
    setup: Option<AuctionSetup>,
    own_salt: String,
    own_commit_hash: Option<String>,
    own_reveal_hash: Option<String>,
    /// Peer commits observed: `agent_idx → commit_hash`.
    peer_commits: BTreeMap<usize, String>,
    /// Peer reveals observed and verified:
    /// `agent_idx → (valuation, salt, commit_hash)`.
    peer_reveals: BTreeMap<usize, (u64, String, String)>,
    /// Own canonical-form content hashes, for `:caused-by`.
    own_hashes: BTreeMap<String, String>,
    /// Peer canonical-form content hashes, for `:caused-by`.
    peer_hashes: BTreeMap<String, String>,
    thread_id: String,
    sender_id: String,
    phase: Phase,
    final_guess: Option<AuctionGuess>,
    /// Salt counter for deterministic-without-RngCore salt generation.
    salt_counter: u64,
    done: bool,
}

impl AuctionDisciplinedAdapter {
    /// Construct a new auction adapter for the auctioneer (agent_idx=0).
    /// Conventional values: `("auction-game", "bidder-0")`.
    pub fn new(thread_id: impl Into<String>, sender_id: impl Into<String>) -> Self {
        Self {
            setup: None,
            own_salt: String::new(),
            own_commit_hash: None,
            own_reveal_hash: None,
            peer_commits: BTreeMap::new(),
            peer_reveals: BTreeMap::new(),
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

    /// Pick a deterministic salt for this seat / counter.
    fn sample_salt(&mut self) -> String {
        use sha2::Digest;
        let mut hasher = sha2::Sha256::new();
        hasher.update(b"auction-salt:");
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

    /// Build a canonical-form auction message. Returns (wire_payload, h-hash).
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

    fn caused_by_for(&self, name: &str) -> String {
        let pred = match name {
            "commit" => return "begin".to_string(),
            "reveal" => "commit",
            "declare-winner" => "reveal",
            _ => return "begin".to_string(),
        };
        if let Some(h) = self.own_hashes.get(pred) {
            return h.clone();
        }
        if let Some(h) = self.peer_hashes.get(pred) {
            return h.clone();
        }
        "begin".to_string()
    }

    /// Bind `(valuation, salt) → commit-hash` per the auction protocol.
    fn commit_hash_for(valuation: u64, salt: &str) -> String {
        fnv1a_bare_hex(format!("{valuation}|{salt}").as_bytes())
    }

    /// Bind `(commit_hash, valuation, salt) → reveal-hash` per the
    /// auction protocol.
    fn reveal_hash_for(commit_hash: &str, valuation: u64, salt: &str) -> String {
        fnv1a_bare_hex(format!("{commit_hash}|{valuation}|{salt}").as_bytes())
    }

    /// Look up the highest-valuation peer reveal. Lower `agent_idx`
    /// breaks ties (matches `AuctionCbclStrategy::winner_from_reveals`).
    fn highest_peer(&self) -> Option<(usize, u64, String, String)> {
        self.peer_reveals
            .iter()
            .map(|(idx, (val, salt, ch))| {
                let rh = Self::reveal_hash_for(ch, *val, salt);
                (*idx, *val, ch.clone(), rh)
            })
            .max_by(|a, b| a.1.cmp(&b.1).then_with(|| b.0.cmp(&a.0)))
    }
}

impl ProtocolAdapter for AuctionDisciplinedAdapter {
    type Setup = AuctionSetup;
    type Guess = AuctionGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(setup);
    }

    fn build_system_prompt(&self) -> String {
        let n = self.setup.as_ref().map(|s| s.n_bidders).unwrap_or(3);
        let v = self.setup.as_ref().map(|s| s.valuation).unwrap_or(0);
        AUCTION_SYSTEM_TEMPLATE
            .replace("{N}", &n.to_string())
            .replace("{N_MINUS_ONE}", &n.saturating_sub(1).to_string())
            .replace("{VALUATION}", &v.to_string())
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
                "propose_commit",
                "Commit to your sealed bid. The shim hashes (valuation || salt) into the commitment H and emits the commit on the wire; you only call this tool to advance.",
                no_params.clone(),
            ),
            f(
                "propose_reveal",
                "Reveal your bid: the shim emits (body=valuation, salt, proof-commit citing your prior commit) on the wire; you only call this tool to advance.",
                no_params,
            ),
            f(
                "declare_winner",
                "Declare the auction winner. Pick the bidder with the highest revealed valuation (lowest agent_idx breaks ties). The shim cites the matching commit and reveal hashes from the wire transcript.",
                serde_json::json!({
                    "type":"object",
                    "properties": {
                        "winner_idx": {"type":"integer","description":"agent_idx of the winning bidder"},
                        "winning_bid": {"type":"integer","description":"the winner's revealed valuation"}
                    },
                    "required":["winner_idx","winning_bid"],
                }),
            ),
        ]
    }

    fn observe_inbound(&mut self, payload: &[u8]) -> String {
        let payload_str = String::from_utf8_lossy(payload).to_string();
        let parsed = parse_auction_message(&payload_str);
        if let Some(msg) = &parsed {
            let perf_name = match msg {
                ParsedMsg::Commit { .. } => "commit",
                ParsedMsg::Reveal { .. } => "reveal",
                ParsedMsg::Declare { .. } => "declare-winner",
            };
            let h = canonical_hash_of(&payload_str)
                .unwrap_or_else(|| fnv1a_h_hex(payload_str.as_bytes()));
            self.peer_hashes
                .entry(perf_name.to_string())
                .or_insert(h);
            match msg {
                ParsedMsg::Commit { sender_idx, hash } => {
                    self.peer_commits.insert(*sender_idx, hash.clone());
                }
                ParsedMsg::Reveal {
                    sender_idx,
                    body,
                    salt,
                    proof_commit,
                } => {
                    // Verify reveal binds to commit before accepting.
                    let recomputed = Self::commit_hash_for(*body, salt);
                    if recomputed == *proof_commit {
                        self.peer_reveals.insert(
                            *sender_idx,
                            (*body, salt.clone(), proof_commit.clone()),
                        );
                    }
                    // Mismatches are silently dropped at the adapter
                    // level (the operator scores binding violations).
                }
                ParsedMsg::Declare { .. } => {}
            }
        }
        match parsed {
            Some(ParsedMsg::Commit { sender_idx, hash }) => {
                format!("(bidder-{sender_idx} sent commit :hash \"{hash}\")")
            }
            Some(ParsedMsg::Reveal {
                sender_idx,
                body,
                salt,
                proof_commit,
            }) => format!(
                "(bidder-{sender_idx} sent reveal :body {body} :salt \"{salt}\" :proof-commit \"{proof_commit}\")"
            ),
            Some(ParsedMsg::Declare {
                winner_idx,
                winning_bid,
            }) => format!(
                "(peer auctioneer sent declare-winner :winner {winner_idx} :winning-bid {winning_bid})"
            ),
            None => format!("(quarantined: unparseable inbound: {:?})", payload_str),
        }
    }

    fn kickoff_prompt(&self) -> String {
        "All bidders are connected. Begin the protocol by calling propose_commit.".to_string()
    }

    fn idle_prompt(&self) -> Option<String> {
        Some(match self.phase {
            Phase::NeedCommit => "Begin: call propose_commit.".to_string(),
            Phase::NeedReveal => "Advance: call propose_reveal.".to_string(),
            Phase::NeedDeclare => {
                let n_expected = self
                    .setup
                    .as_ref()
                    .map(|s| s.n_bidders.saturating_sub(1))
                    .unwrap_or(0);
                if self.peer_reveals.len() >= n_expected {
                    "All peer reveals are in. Identify the winner and call declare_winner.".to_string()
                } else {
                    format!(
                        "Awaiting peer reveals ({} of {} so far). Once all {} land, call declare_winner.",
                        self.peer_reveals.len(),
                        n_expected,
                        n_expected
                    )
                }
            }
            Phase::Done => return None,
        })
    }

    fn classify_tool(&self, name: &str) -> ToolKind {
        match name {
            "propose_commit" | "propose_reveal" | "declare_winner" => ToolKind::Protocol,
            _ => ToolKind::Protocol,
        }
    }

    fn dispatch_tool(
        &mut self,
        tc: &ToolCall,
        emit: &mut dyn FnMut(Vec<u8>),
    ) -> ToolDispatch {
        let args: serde_json::Value =
            serde_json::from_str(&tc.function.arguments).unwrap_or(serde_json::Value::Null);

        match tc.function.name.as_str() {
            "propose_commit" => {
                if !matches!(self.phase, Phase::NeedCommit) {
                    return ToolDispatch {
                        ack: "ignored: propose_commit out of phase".into(),
                    };
                }
                let valuation = self.setup.as_ref().map(|s| s.valuation).unwrap_or(0);
                if self.own_salt.is_empty() {
                    self.own_salt = self.sample_salt();
                }
                let salt = self.own_salt.clone();
                let commit_hash = Self::commit_hash_for(valuation, &salt);
                self.own_commit_hash = Some(commit_hash.clone());
                let cb = self.caused_by_for("commit");
                let (payload, hash) = self.build_canonical(
                    "commit",
                    "@auctioneer",
                    &format!("(bid-commitment :hash \"{commit_hash}\")"),
                    &cb,
                );
                self.own_hashes.insert("commit".into(), hash);
                emit(payload.into_bytes());
                self.phase = Phase::NeedReveal;
                ToolDispatch {
                    ack: "ok: commit sent".into(),
                }
            }
            "propose_reveal" => {
                if !matches!(self.phase, Phase::NeedReveal) {
                    return ToolDispatch {
                        ack: "ignored: propose_reveal out of phase".into(),
                    };
                }
                let valuation = self.setup.as_ref().map(|s| s.valuation).unwrap_or(0);
                let salt = self.own_salt.clone();
                let proof_commit = self
                    .own_commit_hash
                    .clone()
                    .unwrap_or_else(|| Self::commit_hash_for(valuation, &salt));
                let reveal_hash = Self::reveal_hash_for(&proof_commit, valuation, &salt);
                self.own_reveal_hash = Some(reveal_hash);
                let cb = self.caused_by_for("reveal");
                let (payload, hash) = self.build_canonical(
                    "reveal",
                    "@auctioneer",
                    &format!(
                        "(bid-reveal :body {valuation} :salt \"{salt}\" :proof-commit \"{proof_commit}\")"
                    ),
                    &cb,
                );
                self.own_hashes.insert("reveal".into(), hash);
                emit(payload.into_bytes());
                self.phase = Phase::NeedDeclare;
                ToolDispatch {
                    ack: "ok: reveal sent".into(),
                }
            }
            "declare_winner" => {
                if !matches!(self.phase, Phase::NeedDeclare) {
                    return ToolDispatch {
                        ack: "ignored: declare_winner out of phase".into(),
                    };
                }
                let llm_winner = args
                    .get("winner_idx")
                    .and_then(|v| v.as_u64())
                    .map(|n| n as usize);
                let llm_bid = args.get("winning_bid").and_then(|v| v.as_u64());

                // Validate the LLM's claim against the wire-observed reveals
                // (including own). If the LLM names a bidder we've not seen
                // a reveal for, fall back to the highest peer or own.
                let own_idx = self.setup.as_ref().map(|s| s.agent_idx).unwrap_or(0);
                let own_val = self.setup.as_ref().map(|s| s.valuation).unwrap_or(0);
                let own_commit = self.own_commit_hash.clone();
                let own_reveal = self.own_reveal_hash.clone();

                // Find the (idx, bid, commit_hash, reveal_hash) the LLM is
                // claiming. We trust the LLM's identification when its
                // (idx, bid) lines up with an observed reveal or with own.
                let chosen: Option<(usize, u64, String, String)> = match (llm_winner, llm_bid) {
                    (Some(idx), Some(bid)) if Some(idx) == Some(own_idx) && bid == own_val => {
                        if let (Some(c), Some(r)) = (own_commit.clone(), own_reveal.clone()) {
                            Some((own_idx, own_val, c, r))
                        } else {
                            None
                        }
                    }
                    (Some(idx), Some(bid)) => {
                        if let Some((val, salt, commit_hash)) = self.peer_reveals.get(&idx) {
                            if *val == bid {
                                let rh = Self::reveal_hash_for(commit_hash, *val, salt);
                                Some((idx, *val, commit_hash.clone(), rh))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                let (winner_idx, winner_bid, proof_commit, proof_reveal) = match chosen {
                    Some(t) => t,
                    None => {
                        // Fallback: pick the actual highest from observed.
                        let mut all: Vec<(usize, u64, String, String)> = Vec::new();
                        if let (Some(c), Some(r)) = (own_commit.clone(), own_reveal.clone()) {
                            all.push((own_idx, own_val, c, r));
                        }
                        if let Some(t) = self.highest_peer() {
                            all.push(t);
                        }
                        match all
                            .into_iter()
                            .max_by(|a, b| a.1.cmp(&b.1).then_with(|| b.0.cmp(&a.0)))
                        {
                            Some(t) => t,
                            None => {
                                self.phase = Phase::Done;
                                self.done = true;
                                self.final_guess = Some(AuctionGuess::Unknown);
                                return ToolDispatch {
                                    ack: "ignored: no observed reveals to base a declaration on".into(),
                                };
                            }
                        }
                    }
                };

                let cb = self.caused_by_for("declare-winner");
                let (payload, hash) = self.build_canonical(
                    "declare-winner",
                    "@bidders",
                    &format!(
                        "(winner-declaration :winner {winner_idx} :winning-bid {winner_bid} :proof-commit \"{proof_commit}\" :proof-reveal \"{proof_reveal}\")"
                    ),
                    &cb,
                );
                self.own_hashes.insert("declare-winner".into(), hash);
                emit(payload.into_bytes());
                self.final_guess = Some(AuctionGuess::Winner {
                    agent_idx: winner_idx,
                    bid: winner_bid,
                });
                self.phase = Phase::Done;
                self.done = true;
                ToolDispatch {
                    ack: "ok: declare-winner sent; protocol complete".into(),
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
        self.final_guess.unwrap_or(AuctionGuess::Unknown)
    }
}

/// Inbound parse cases for the auction.
#[derive(Clone, Debug)]
enum ParsedMsg {
    Commit {
        sender_idx: usize,
        hash: String,
    },
    Reveal {
        sender_idx: usize,
        body: u64,
        salt: String,
        proof_commit: String,
    },
    Declare {
        winner_idx: usize,
        winning_bid: u64,
    },
}

/// Best-effort auction inbound parse.
fn parse_auction_message(payload: &str) -> Option<ParsedMsg> {
    let p = payload.trim();
    if p.contains("declare-winner") || p.contains("winner-declaration") {
        let winner_idx = extract_kw(p, "winner")
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(0);
        let winning_bid = extract_kw(p, "winning-bid")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        return Some(ParsedMsg::Declare {
            winner_idx,
            winning_bid,
        });
    }
    let sender_idx = extract_sender_idx(p).unwrap_or(usize::MAX);
    if p.contains("bid-reveal") {
        let body = extract_kw(p, "body")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        let salt = extract_kw(p, "salt")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        let proof_commit = extract_kw(p, "proof-commit")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        return Some(ParsedMsg::Reveal {
            sender_idx,
            body,
            salt,
            proof_commit,
        });
    }
    if p.contains("bid-commitment") || (p.contains("commit") && p.contains(":hash")) {
        let hash = extract_kw(p, "hash")
            .unwrap_or_default()
            .trim_matches('"')
            .to_string();
        return Some(ParsedMsg::Commit { sender_idx, hash });
    }
    None
}

/// Extract `:key value` (raw token; quotes intact). Same shape as PSI /
/// Yao adapters' `extract_kw`.
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

/// Extract sender agent_idx from a payload's `:sender` field. Accepts
/// `bidder-<idx>`, `alice` ↔ 0 / `bob` ↔ 1 / `carol` ↔ 2 conventional
/// names, or any string with a trailing decimal.
fn extract_sender_idx(payload: &str) -> Option<usize> {
    let sender = extract_kw(payload, "sender")?;
    let s = sender.trim_matches('"');
    if let Some(rest) = s.strip_prefix("bidder-") {
        return rest.parse::<usize>().ok();
    }
    match s {
        "alice" | "Alice" => return Some(0),
        "bob" | "Bob" => return Some(1),
        "carol" | "Carol" => return Some(2),
        "dave" | "Dave" => return Some(3),
        _ => {}
    }
    let tail: String = s.chars().rev().take_while(|c| c.is_ascii_digit()).collect();
    let tail: String = tail.chars().rev().collect();
    tail.parse::<usize>().ok()
}

/// FNV-1a-128 with `h` prefix (canonical content-hash form).
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

/// FNV-1a-128 bare hex (no prefix). Matches `super::strategy_hash`
/// byte-for-byte so the cooperative `AuctionCbclStrategy` peer's
/// recomputed bindings line up.
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

/// Canonical hash of a parseable inbound payload.
fn canonical_hash_of(payload: &str) -> Option<String> {
    let sexpr = cbcl_parser::parse(payload).ok()?;
    let msg = cbcl_parser::parse_message(&sexpr).ok()?;
    let inner = msg.innermost_simple().unwrap_or(&msg).clone();
    let canonical =
        cbcl_core::serializer::serialize(&cbcl_core::sexpr::SExpr::from(&inner));
    Some(fnv1a_h_hex(canonical.as_bytes()))
}
