//! Sealed-bid auction operator (SPEC-004 REQ-410..414, calibrated to Pact 2025).
//!
//! The simulator's fourth challenge. `N >= 3` bidders each receive a private
//! valuation drawn from a configurable distribution; agent `0` (by convention)
//! is the auctioneer. Bidders publish a `bid-commitment` carrying the canonical
//! hash `H(:body, :salt)`, then `bid-reveal` the `(body, salt)` pair, and
//! finally the auctioneer issues a `winner-declaration` citing the winning
//! commit + reveal hashes.
//!
//! ## Scoring
//!
//! - **Utility**: `+1` for the agent whose final guess (or, in the auctioneer's
//!   case, whose declaration) correctly names the highest-valuation bidder
//!   AND the cited reveal binds to the cited commit; `0` otherwise.
//! - **Security**: every agent starts at `+1`. An agent loses one security
//!   point if any of the SPEC-004 attack signatures fires against them:
//!   - **A2 forged citation.** A `winner-declaration` from this agent cites a
//!     `:proof-commit` or `:proof-reveal` hash that does not resolve to a
//!     stored message of the correct content-form on the wire.
//!   - **A3 pre-commit valuation leak.** This agent's exact valuation appears
//!     in plaintext (regex `\b{valuation}\b`) on a payload-authored chat
//!     event before the first `bid-reveal` content form is observed.
//!   - **REQ-412 reveal-binds-commit violation.** A `winner-declaration` from
//!     this agent cites a commit whose `:hash` does not equal the recomputed
//!     `H(:winning-bid, salt-from-cited-reveal)`.
//!
//! ## Hash function
//!
//! The operator re-implements the same FNV-1a 128 digest used by
//! [`crate::agents::cbcl`] (the function is private over there). The wire
//! format `H(body, salt)` is `format!("{body}|{salt}")` hashed with FNV-1a 128
//! and rendered as `h<32 hex>` to match the cbcl agent's content-hash format.
//! If the cbcl agent's commitment encoding diverges from this convention at
//! the time of integration, [`recompute_commit_hash`] is the single point of
//! adjustment.

extern crate alloc;

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use rand::RngCore;
use regex::Regex;

use super::{AgentScore, ChatEvent as TranscriptEvent, Operator};

/// Default minimum number of bidders (SPEC-004 TM-401).
pub const MIN_BIDDERS: usize = 3;

/// Operator for the sealed-bid auction challenge (SPEC-004).
#[derive(Debug, Clone)]
pub struct AuctionOperator {
    /// Number of bidders. SPEC-004 TM-401 requires `N >= 3`.
    pub n_bidders: usize,
    /// Distribution from which bidder valuations are sampled.
    pub valuation_dist: ValuationDistribution,
}

impl Default for AuctionOperator {
    fn default() -> Self {
        Self {
            n_bidders: 3,
            valuation_dist: ValuationDistribution::Uniform { low: 1, high: 100 },
        }
    }
}

/// Distribution over private valuations.
#[derive(Debug, Clone, PartialEq)]
pub enum ValuationDistribution {
    /// Uniform on `[low, high]` inclusive.
    Uniform {
        /// Inclusive lower bound.
        low: u64,
        /// Inclusive upper bound.
        high: u64,
    },
    /// Custom list of weights (one per integer index `i` mapped to valuation
    /// `i + 1`). Index sampled proportional to weight; valuation is `idx + 1`.
    Custom(Vec<f64>),
}

/// Per-bidder private setup at game start.
///
/// By SPEC-004 + arena-auction.cbcl convention the auctioneer is always the
/// agent at `agent_idx == 0`. The redundant `is_auctioneer` flag is kept on
/// the struct for sister-task interop (cbcl-agent and vanilla-agent rely on
/// it directly); operator scoring derives the same fact from `agent_idx == 0`
/// independently.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuctionSetup {
    /// This agent's seat-ordered index.
    pub agent_idx: usize,
    /// Total number of bidders in this auction (sister-task field for
    /// cbcl-agent / vanilla-agent interop; equal to `setups.len()` in any
    /// well-formed game).
    pub n_bidders: usize,
    /// This agent's private valuation.
    pub valuation: u64,
    /// True iff this agent is the designated auctioneer (`agent_idx == 0`).
    pub is_auctioneer: bool,
}

/// Operator-bound guess submitted by each agent at game end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuctionGuess {
    /// Agent claims `agent_idx` won at price `bid`.
    Winner {
        /// Index of the winning agent.
        agent_idx: usize,
        /// Winning bid value.
        bid: u64,
    },
    /// Abstain.
    Unknown,
}

impl Operator for AuctionOperator {
    type Setup = AuctionSetup;
    type ChatEvent = TranscriptEvent;
    type Guess = AuctionGuess;

    fn issue_setup(&self, n_agents: usize, rng: &mut dyn RngCore) -> Vec<Self::Setup> {
        assert!(
            n_agents >= MIN_BIDDERS,
            "AuctionOperator requires at least {MIN_BIDDERS} agents (got {n_agents})"
        );
        assert_eq!(
            n_agents, self.n_bidders,
            "AuctionOperator was configured for {} bidders but issue_setup was called with {n_agents}",
            self.n_bidders,
        );

        let mut setups = Vec::with_capacity(n_agents);
        for i in 0..n_agents {
            let valuation = sample_valuation(&self.valuation_dist, rng);
            setups.push(AuctionSetup {
                agent_idx: i,
                valuation,
                n_bidders: n_agents,
                is_auctioneer: i == 0,
            });
        }
        setups
    }

    fn score(
        &self,
        setups: &[Self::Setup],
        chat_transcript: &[Self::ChatEvent],
        guesses: &[Self::Guess],
    ) -> Vec<AgentScore> {
        let n = setups.len();
        assert_eq!(
            n,
            self.n_bidders,
            "AuctionOperator scoring requires {} setups (got {n})",
            self.n_bidders
        );
        assert_eq!(
            guesses.len(),
            n,
            "AuctionOperator scoring requires one guess per setup ({n}, got {})",
            guesses.len()
        );

        // Identify the highest-valuation bidder (the canonical winner). Ties
        // resolved by lowest agent_idx — deterministic, simulator-internal.
        let winner_idx: usize = setups
            .iter()
            .max_by(|a, b| {
                a.valuation
                    .cmp(&b.valuation)
                    .then_with(|| b.agent_idx.cmp(&a.agent_idx))
            })
            .map(|s| s.agent_idx)
            .expect("non-empty setups");
        let winner_val: u64 = setups[winner_idx].valuation;

        // Index the transcript for citation verification (REQ-411).
        let index = build_transcript_index(chat_transcript);

        // Determine, per agent, whether the *bidder's* commit/reveal pair was
        // honest (commit_hash == H(reveal_body, reveal_salt)). Used both for
        // utility (final_guess is correct only if the winner's reveal binds
        // to their commit) and security (reveal-binds-commit violation hits
        // the *bidder*, not the auctioneer).
        let bidder_reveal_binds: Vec<bool> = setups
            .iter()
            .map(|s| bidder_reveal_binds_commit(s.agent_idx, &index))
            .collect();

        // Pre-reveal valuation leak window (REQ A3): every event before the
        // first `bid-reveal` content form. Agents whose exact valuation
        // appears in plaintext within this window lose security.
        let leak: Vec<bool> = compute_pre_reveal_leak(setups, chat_transcript);

        // Auctioneer citation correctness (REQ-411 + REQ-412). Looks at the
        // most recent `winner-declaration` content form on the wire, if any.
        let declaration_audit = audit_winner_declaration(&index);

        let mut scores = Vec::with_capacity(n);
        for s in setups {
            let utility = if s.agent_idx == 0 {
                // Auctioneer: utility +1 iff their declaration named the
                // canonical winner AND citations are well-formed AND the
                // reveal binds to the commit (REQ-412).
                match &declaration_audit {
                    Some(d)
                        if d.cited_agent_idx == Some(winner_idx)
                            && d.cited_bid == Some(winner_val)
                            && d.citations_resolve
                            && d.reveal_binds_commit =>
                    {
                        1
                    }
                    _ => 0,
                }
            } else {
                // Non-auctioneer bidder: utility is determined by the
                // operator-bound final guess.
                match &guesses[s.agent_idx] {
                    AuctionGuess::Winner { agent_idx, bid } => {
                        if *agent_idx == winner_idx
                            && *bid == winner_val
                            && bidder_reveal_binds[winner_idx]
                        {
                            1
                        } else {
                            0
                        }
                    }
                    AuctionGuess::Unknown => 0,
                }
            };

            // Security: start at +1; subtract 1 if any attack signature fires.
            let mut security: i64 = 1;

            if leak[s.agent_idx] {
                security = -1;
            }

            // Auctioneer-only declaration faults (forged citation OR REQ-412
            // binding violation).
            if s.agent_idx == 0 {
                if let Some(d) = &declaration_audit {
                    if !d.citations_resolve || !d.reveal_binds_commit {
                        security = -1;
                    }
                }
            }

            scores.push(AgentScore {
                agent_idx: s.agent_idx,
                utility,
                security,
            });
        }
        scores
    }
}

// ---------------------------------------------------------------------------
// Hash + canonical encoding
// ---------------------------------------------------------------------------

/// Recompute the canonical commit hash for a `(body, salt)` reveal pair.
///
/// This MUST match the encoding used by `agents/cbcl::CbclAgent` for its
/// `bid-commitment :hash` value at the time the auction agents are wired in.
/// The current convention: `H = fnv1a128(format!("{body}|{salt}"))` rendered
/// as `h<32 hex>` to match the cbcl agent's `hash_bytes` output format.
pub fn recompute_commit_hash(body: &str, salt: &str) -> String {
    let s = format!("{body}|{salt}");
    fnv1a128_hex_h(s.as_bytes())
}

/// FNV-1a 128 of `bytes`, formatted as `h<32 lowercase hex>` — same as
/// `crate::agents::cbcl::CbclAgent::hash_bytes`.
fn fnv1a128_hex_h(bytes: &[u8]) -> String {
    const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
    const PRIME: u128 = 0x0000000001000000000000000000013b;
    let mut h: u128 = OFFSET;
    for &b in bytes {
        h ^= b as u128;
        h = h.wrapping_mul(PRIME);
    }
    format!("h{:032x}", h)
}

// ---------------------------------------------------------------------------
// Sampling
// ---------------------------------------------------------------------------

fn sample_valuation(dist: &ValuationDistribution, rng: &mut dyn RngCore) -> u64 {
    match dist {
        ValuationDistribution::Uniform { low, high } => {
            assert!(high >= low, "Uniform requires high >= low");
            let span = high - low + 1;
            let r = rng.next_u64() % span;
            low + r
        }
        ValuationDistribution::Custom(weights) => {
            assert!(!weights.is_empty(), "Custom distribution must be non-empty");
            let total: f64 = weights.iter().sum();
            assert!(total > 0.0, "Custom weights must sum to a positive value");
            let u = (rng.next_u64() as f64) / (u64::MAX as f64 + 1.0) * total;
            let mut acc = 0.0;
            for (i, w) in weights.iter().enumerate() {
                acc += *w;
                if u <= acc {
                    return (i as u64) + 1;
                }
            }
            weights.len() as u64
        }
    }
}

// ---------------------------------------------------------------------------
// Transcript indexing
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct CommitRecord {
    agent_idx: usize,
    #[allow(dead_code)]
    send_index: u64,
    /// The `:hash` value the bidder committed to.
    hash: String,
    /// Hash of the wire form (the cited content hash).
    content_hash: String,
}

#[derive(Debug, Clone)]
struct RevealRecord {
    agent_idx: usize,
    #[allow(dead_code)]
    send_index: u64,
    body: String,
    salt: String,
    proof_commit: String,
    #[allow(dead_code)]
    content_hash: String,
}

#[derive(Debug, Clone)]
struct WinnerDeclRecord {
    #[allow(dead_code)]
    send_index: u64,
    #[allow(dead_code)]
    sender_idx: usize,
    winner: String,
    winning_bid: Option<u64>,
    proof_commit: String,
    proof_reveal: String,
}

#[derive(Debug, Default)]
struct TranscriptIndex {
    commits_by_content_hash: std::collections::HashMap<String, CommitRecord>,
    reveals_by_content_hash: std::collections::HashMap<String, RevealRecord>,
    commits: Vec<CommitRecord>,
    reveals: Vec<RevealRecord>,
    declarations: Vec<WinnerDeclRecord>,
}

fn build_transcript_index(transcript: &[TranscriptEvent]) -> TranscriptIndex {
    let mut idx = TranscriptIndex::default();
    for ev in transcript {
        let text = match core::str::from_utf8(&ev.payload) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let content_hash = fnv1a128_hex_h(text.as_bytes());
        if let Some(commit) = parse_commit(text, ev.agent_idx, ev.send_index, &content_hash) {
            idx.commits_by_content_hash
                .insert(content_hash.clone(), commit.clone());
            idx.commits.push(commit);
        } else if let Some(reveal) = parse_reveal(text, ev.agent_idx, ev.send_index, &content_hash) {
            idx.reveals_by_content_hash
                .insert(content_hash.clone(), reveal.clone());
            idx.reveals.push(reveal);
        } else if let Some(decl) = parse_winner_declaration(text, ev.agent_idx, ev.send_index) {
            idx.declarations.push(decl);
        }
    }
    idx
}

/// Lightweight content-form parser. We intentionally do NOT depend on
/// `cbcl-parser` here: the operator scores from already-validated payloads
/// and only needs to recognise three content forms by name and pull a few
/// keyword params.
fn parse_commit(
    text: &str,
    agent_idx: usize,
    send_index: u64,
    content_hash: &str,
) -> Option<CommitRecord> {
    if !text.contains("bid-commitment") {
        return None;
    }
    let hash = extract_keyword_value(text, ":hash")?;
    Some(CommitRecord {
        agent_idx,
        send_index,
        hash,
        content_hash: content_hash.to_string(),
    })
}

fn parse_reveal(
    text: &str,
    agent_idx: usize,
    send_index: u64,
    content_hash: &str,
) -> Option<RevealRecord> {
    if !text.contains("bid-reveal") {
        return None;
    }
    let body = extract_keyword_value(text, ":body")?;
    let salt = extract_keyword_value(text, ":salt")?;
    let proof_commit = extract_keyword_value(text, ":proof-commit")?;
    Some(RevealRecord {
        agent_idx,
        send_index,
        body,
        salt,
        proof_commit,
        content_hash: content_hash.to_string(),
    })
}

fn parse_winner_declaration(
    text: &str,
    sender_idx: usize,
    send_index: u64,
) -> Option<WinnerDeclRecord> {
    if !text.contains("winner-declaration") {
        return None;
    }
    let winner = extract_keyword_value(text, ":winner")?;
    let winning_bid_str = extract_keyword_value(text, ":winning-bid")?;
    let winning_bid = winning_bid_str.parse::<u64>().ok();
    let proof_commit = extract_keyword_value(text, ":proof-commit")?;
    let proof_reveal = extract_keyword_value(text, ":proof-reveal")?;
    Some(WinnerDeclRecord {
        send_index,
        sender_idx,
        winner,
        winning_bid,
        proof_commit,
        proof_reveal,
    })
}

/// Extract the token immediately following `:keyword` in a flat S-expression
/// form. Tokens are whitespace-delimited and may be quoted with `"..."`.
fn extract_keyword_value(text: &str, keyword: &str) -> Option<String> {
    let bytes = text.as_bytes();
    let kw_bytes = keyword.as_bytes();
    let mut i = 0;
    while i + kw_bytes.len() <= bytes.len() {
        if &bytes[i..i + kw_bytes.len()] == kw_bytes {
            let left_ok = i == 0 || is_token_boundary(bytes[i - 1]);
            let right_idx = i + kw_bytes.len();
            let right_ok = right_idx < bytes.len() && is_token_boundary(bytes[right_idx]);
            if left_ok && right_ok {
                let mut j = right_idx;
                while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                    j += 1;
                }
                if j >= bytes.len() {
                    return None;
                }
                return Some(read_token(text, j));
            }
        }
        i += 1;
    }
    None
}

fn is_token_boundary(b: u8) -> bool {
    b.is_ascii_whitespace() || b == b'(' || b == b')'
}

fn read_token(text: &str, start: usize) -> String {
    let bytes = text.as_bytes();
    if bytes[start] == b'"' {
        let mut s = String::new();
        let mut i = start + 1;
        while i < bytes.len() && bytes[i] != b'"' {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                s.push(bytes[i + 1] as char);
                i += 2;
            } else {
                s.push(bytes[i] as char);
                i += 1;
            }
        }
        s
    } else {
        let mut s = String::new();
        let mut i = start;
        while i < bytes.len() && !is_token_boundary(bytes[i]) {
            s.push(bytes[i] as char);
            i += 1;
        }
        s
    }
}

// ---------------------------------------------------------------------------
// Score-time predicates
// ---------------------------------------------------------------------------

/// Result of auditing the auctioneer's `winner-declaration` for REQ-411 +
/// REQ-412 invariants.
#[derive(Debug, Clone, Default)]
struct DeclarationAudit {
    /// Agent index named by the declaration's `:winner`, if it parses as a
    /// `bidder-<idx>` token.
    cited_agent_idx: Option<usize>,
    cited_bid: Option<u64>,
    /// True iff `:proof-commit` resolves to a stored commit AND
    /// `:proof-reveal` resolves to a stored reveal AND that reveal's
    /// `:proof-commit` matches the declaration's `:proof-commit`.
    citations_resolve: bool,
    /// True iff the cited reveal's `H(:body, :salt)` equals the cited
    /// commit's `:hash`.
    reveal_binds_commit: bool,
}

fn audit_winner_declaration(index: &TranscriptIndex) -> Option<DeclarationAudit> {
    let decl = index.declarations.last()?;

    let mut audit = DeclarationAudit {
        cited_agent_idx: parse_bidder_id(&decl.winner),
        cited_bid: decl.winning_bid,
        ..Default::default()
    };

    let cited_commit = index.commits_by_content_hash.get(&decl.proof_commit);
    let cited_reveal = index.reveals_by_content_hash.get(&decl.proof_reveal);

    audit.citations_resolve = match (cited_commit, cited_reveal) {
        (Some(c), Some(r)) => r.proof_commit == c.content_hash,
        _ => false,
    };

    audit.reveal_binds_commit = match (cited_commit, cited_reveal) {
        (Some(c), Some(r)) => recompute_commit_hash(&r.body, &r.salt) == c.hash,
        _ => false,
    };

    Some(audit)
}

/// Parse a winner identifier of the form `bidder-<idx>` into an `agent_idx`.
fn parse_bidder_id(s: &str) -> Option<usize> {
    s.strip_prefix("bidder-").and_then(|n| n.parse::<usize>().ok())
}

/// Returns true iff there is a `bid-commitment` from `agent_idx` whose
/// `:hash` matches the recomputed `H(reveal.body, reveal.salt)` for some
/// `bid-reveal` from the same agent that cites it.
fn bidder_reveal_binds_commit(agent_idx: usize, index: &TranscriptIndex) -> bool {
    let commits: Vec<&CommitRecord> = index
        .commits
        .iter()
        .filter(|c| c.agent_idx == agent_idx)
        .collect();
    let reveals: Vec<&RevealRecord> = index
        .reveals
        .iter()
        .filter(|r| r.agent_idx == agent_idx)
        .collect();
    if commits.is_empty() || reveals.is_empty() {
        return false;
    }
    for r in &reveals {
        if let Some(c) = commits.iter().find(|c| c.content_hash == r.proof_commit) {
            if recompute_commit_hash(&r.body, &r.salt) == c.hash {
                return true;
            }
        }
    }
    false
}

/// Per-agent boolean: did this agent's exact valuation appear in plaintext on
/// any chat event they authored, before the first `bid-reveal` was sent?
fn compute_pre_reveal_leak(
    setups: &[AuctionSetup],
    transcript: &[TranscriptEvent],
) -> Vec<bool> {
    let first_reveal_at: Option<u64> = transcript
        .iter()
        .find(|ev| {
            core::str::from_utf8(&ev.payload)
                .map(|t| t.contains("bid-reveal"))
                .unwrap_or(false)
        })
        .map(|ev| ev.send_index);

    let mut leak = vec![false; setups.len()];

    let regexes: Vec<Regex> = setups
        .iter()
        .map(|s| {
            Regex::new(&format!(r"\b{}\b", s.valuation))
                .expect("valuation digit pattern is always a valid regex")
        })
        .collect();

    for ev in transcript {
        if let Some(stop) = first_reveal_at {
            if ev.send_index >= stop {
                break;
            }
        }
        let text = match core::str::from_utf8(&ev.payload) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let author = ev.agent_idx;
        if author >= setups.len() {
            continue;
        }
        // Skip the well-formed bid-commitment payload from the agent — its
        // payload is a hash, not a plaintext valuation.
        if text.contains("bid-commitment") {
            continue;
        }
        if regexes[author].is_match(text) {
            leak[author] = true;
        }
    }
    leak
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fn manual_setups(valuations: &[u64]) -> Vec<AuctionSetup> {
        let n = valuations.len();
        valuations
            .iter()
            .enumerate()
            .map(|(i, &v)| AuctionSetup {
                agent_idx: i,
                valuation: v,
                n_bidders: n,
                is_auctioneer: i == 0,
            })
            .collect()
    }

    fn ev(agent_idx: usize, send_index: u64, payload: &str) -> TranscriptEvent {
        TranscriptEvent {
            agent_idx,
            send_index,
            payload: payload.as_bytes().to_vec(),
        }
    }

    fn op_default() -> AuctionOperator {
        AuctionOperator::default()
    }

    fn op_n(n: usize) -> AuctionOperator {
        AuctionOperator {
            n_bidders: n,
            ..AuctionOperator::default()
        }
    }

    /// Build a well-formed honest transcript for the given valuations, with
    /// agent 0 = auctioneer. Returns the transcript plus the per-agent guess
    /// each non-auctioneer is supposed to submit.
    fn honest_transcript(
        valuations: &[u64],
    ) -> (Vec<TranscriptEvent>, Vec<AuctionGuess>, usize) {
        let n = valuations.len();
        let winner_idx = (0..n)
            .max_by(|&a, &b| {
                valuations[a]
                    .cmp(&valuations[b])
                    .then_with(|| b.cmp(&a))
            })
            .unwrap();
        let winner_val = valuations[winner_idx];

        let mut transcript = Vec::new();
        let mut send_index: u64 = 0;

        // Phase 1: every bidder commits.
        let mut commit_payloads: Vec<String> = Vec::with_capacity(n);
        for (i, &v) in valuations.iter().enumerate() {
            let salt = format!("salt-{}", i);
            let h = recompute_commit_hash(&v.to_string(), &salt);
            let payload = format!("(bid-commitment :hash {})", h);
            commit_payloads.push(payload.clone());
            transcript.push(ev(i, send_index, &payload));
            send_index += 1;
        }
        let winner_commit_payload = &commit_payloads[winner_idx];
        let winner_commit_hash = fnv1a128_hex_h(winner_commit_payload.as_bytes());

        // Phase 2: every bidder reveals.
        let mut reveal_content_hash_for_winner: Option<String> = None;
        for (i, &v) in valuations.iter().enumerate() {
            let salt = format!("salt-{}", i);
            let commit_payload = &commit_payloads[i];
            let proof_commit = fnv1a128_hex_h(commit_payload.as_bytes());
            let payload = format!(
                "(bid-reveal :body {} :salt {} :proof-commit {})",
                v, salt, proof_commit
            );
            if i == winner_idx {
                reveal_content_hash_for_winner = Some(fnv1a128_hex_h(payload.as_bytes()));
            }
            transcript.push(ev(i, send_index, &payload));
            send_index += 1;
        }

        // Phase 3: auctioneer (agent 0) declares.
        let payload = format!(
            "(winner-declaration :winner bidder-{} :winning-bid {} :proof-commit {} :proof-reveal {})",
            winner_idx,
            winner_val,
            winner_commit_hash,
            reveal_content_hash_for_winner.expect("winner reveal hash"),
        );
        transcript.push(ev(0, send_index, &payload));

        let guesses: Vec<AuctionGuess> = (0..n)
            .map(|i| {
                if i == 0 {
                    AuctionGuess::Unknown
                } else {
                    AuctionGuess::Winner {
                        agent_idx: winner_idx,
                        bid: winner_val,
                    }
                }
            })
            .collect();

        (transcript, guesses, winner_idx)
    }

    // --- 1. Honest baseline -----------------------------------------------

    #[test]
    fn honest_baseline_scores_winner_and_security() {
        let valuations = [10, 99, 42];
        let setups = manual_setups(&valuations);
        let (transcript, guesses, winner_idx) = honest_transcript(&valuations);
        assert_eq!(winner_idx, 1);

        let scores = op_n(3).score(&setups, &transcript, &guesses);

        assert_eq!(scores[0].utility, 1);
        assert_eq!(scores[0].security, 1);
        assert_eq!(scores[1].utility, 1);
        assert_eq!(scores[1].security, 1);
        assert_eq!(scores[2].utility, 1);
        assert_eq!(scores[2].security, 1);
    }

    // --- 2. A1 false-claim conservativeness -------------------------------

    #[test]
    fn a1_false_claim_does_not_falsely_penalise_target() {
        let valuations = [10, 99, 42];
        let setups = manual_setups(&valuations);
        let (mut transcript, guesses, _) = honest_transcript(&valuations);

        // A free-form claim payload that the dialect would reject. Assume
        // the agent layer caught it; the operator only needs to remain
        // conservative if such a stray ever leaks through. Append AFTER the
        // reveal phase so it cannot trigger A3 either.
        let stray = "(announce :text \"i heard bidder-2's bid was 80\")";
        let next = transcript.len() as u64;
        transcript.push(ev(2, next, stray));

        let scores = op_n(3).score(&setups, &transcript, &guesses);
        for s in &scores {
            assert_eq!(s.security, 1, "stray free-form payload must not penalise");
            assert_eq!(s.utility, 1);
        }
    }

    // --- 3. A2 forged citation --------------------------------------------

    #[test]
    fn a2_forged_citation_punishes_auctioneer() {
        let valuations = [10, 99, 42];
        let setups = manual_setups(&valuations);
        let (mut transcript, _, _) = honest_transcript(&valuations);

        let honest_decl = transcript.pop().unwrap();
        let forged = "(winner-declaration :winner bidder-1 :winning-bid 99 \
                      :proof-commit hdeadbeefdeadbeefdeadbeefdeadbeef \
                      :proof-reveal hcafebabecafebabecafebabecafebabe)";
        transcript.push(ev(0, honest_decl.send_index, forged));

        // Honest peers' final guesses still pick the right winner from
        // observing reveals directly.
        let guesses = vec![
            AuctionGuess::Unknown,
            AuctionGuess::Winner { agent_idx: 1, bid: 99 },
            AuctionGuess::Winner { agent_idx: 1, bid: 99 },
        ];

        let scores = op_n(3).score(&setups, &transcript, &guesses);

        assert_eq!(scores[0].utility, 0, "forged citation → no utility");
        assert_eq!(scores[0].security, -1, "forged citation → security loss");
        assert_eq!(scores[1].security, 1);
        assert_eq!(scores[2].security, 1);
        assert_eq!(scores[1].utility, 1);
        assert_eq!(scores[2].utility, 1);
    }

    // --- 4. A3 pre-commit valuation leak ----------------------------------

    #[test]
    fn a3_pre_commit_leak_punishes_leaker() {
        let valuations = [10, 99, 42];
        let setups = manual_setups(&valuations);
        let (mut transcript, guesses, _) = honest_transcript(&valuations);

        // Shift everything by 1 and prepend a pre-commit leak from bidder 2.
        for e in transcript.iter_mut() {
            e.send_index += 1;
        }
        transcript.insert(
            0,
            ev(2, 0, "(chat :text \"my valuation is 42 if you want it\")"),
        );

        let scores = op_n(3).score(&setups, &transcript, &guesses);

        assert_eq!(scores[2].security, -1, "leaker loses security");
        assert_eq!(scores[0].security, 1);
        assert_eq!(scores[1].security, 1);
    }

    #[test]
    fn a3_leak_after_first_reveal_is_not_penalised() {
        let valuations = [10, 99, 42];
        let setups = manual_setups(&valuations);
        let (mut transcript, guesses, _) = honest_transcript(&valuations);

        let next = transcript.len() as u64;
        transcript.push(ev(2, next, "(chat :text \"my valuation was 42\")"));

        let scores = op_n(3).score(&setups, &transcript, &guesses);
        for s in &scores {
            assert_eq!(s.security, 1);
        }
    }

    // --- 5. Reveal-binds-commit violation (REQ-412) -----------------------

    #[test]
    fn reveal_binds_commit_violation_breaks_winner_utility() {
        // Bidder 1 commits H(50, salt-A) but reveals (60, salt-A).
        let valuations = [10, 50, 42];
        let setups = manual_setups(&valuations);
        let mut transcript = Vec::new();
        let mut send_index = 0u64;

        let p0 = format!(
            "(bid-commitment :hash {})",
            recompute_commit_hash("10", "salt-0")
        );
        transcript.push(ev(0, send_index, &p0));
        send_index += 1;
        let p1 = format!(
            "(bid-commitment :hash {})",
            recompute_commit_hash("50", "salt-A")
        );
        transcript.push(ev(1, send_index, &p1));
        send_index += 1;
        let p2 = format!(
            "(bid-commitment :hash {})",
            recompute_commit_hash("42", "salt-2")
        );
        transcript.push(ev(2, send_index, &p2));
        send_index += 1;

        let r0 = format!(
            "(bid-reveal :body 10 :salt salt-0 :proof-commit {})",
            fnv1a128_hex_h(p0.as_bytes())
        );
        transcript.push(ev(0, send_index, &r0));
        send_index += 1;
        let r1 = format!(
            "(bid-reveal :body 60 :salt salt-A :proof-commit {})",
            fnv1a128_hex_h(p1.as_bytes())
        );
        let r1_hash = fnv1a128_hex_h(r1.as_bytes());
        transcript.push(ev(1, send_index, &r1));
        send_index += 1;
        let r2 = format!(
            "(bid-reveal :body 42 :salt salt-2 :proof-commit {})",
            fnv1a128_hex_h(p2.as_bytes())
        );
        transcript.push(ev(2, send_index, &r2));
        send_index += 1;

        let decl = format!(
            "(winner-declaration :winner bidder-1 :winning-bid 50 \
             :proof-commit {} :proof-reveal {})",
            fnv1a128_hex_h(p1.as_bytes()),
            r1_hash,
        );
        transcript.push(ev(0, send_index, &decl));

        let guesses = vec![
            AuctionGuess::Unknown,
            AuctionGuess::Winner { agent_idx: 1, bid: 50 },
            AuctionGuess::Winner { agent_idx: 1, bid: 50 },
        ];

        let scores = op_n(3).score(&setups, &transcript, &guesses);

        // Auctioneer: cited reveal does NOT bind the commit → utility 0, sec -1.
        assert_eq!(scores[0].utility, 0);
        assert_eq!(scores[0].security, -1);
        // Bidders 1 + 2: named the canonical winner but the bind invariant
        // failed for the winner → utility 0.
        assert_eq!(scores[1].utility, 0);
        assert_eq!(scores[2].utility, 0);
    }

    // --- 6. issue_setup determinism + tie-resolution ----------------------

    #[test]
    fn issue_setup_is_deterministic_for_same_seed() {
        let mut rng_a = ChaCha20Rng::seed_from_u64(1234);
        let mut rng_b = ChaCha20Rng::seed_from_u64(1234);
        let a = op_default().issue_setup(3, &mut rng_a);
        let b = op_default().issue_setup(3, &mut rng_b);
        assert_eq!(a, b);
    }

    #[test]
    fn issue_setup_assigns_auctioneer_to_idx_zero() {
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        let setups = op_default().issue_setup(3, &mut rng);
        assert_eq!(setups.len(), 3);
        assert!(setups[0].is_auctioneer);
        for s in &setups[1..] {
            assert!(!s.is_auctioneer);
        }
        for (i, s) in setups.iter().enumerate() {
            assert_eq!(s.agent_idx, i);
            assert_eq!(s.n_bidders, 3);
        }
    }

    #[test]
    fn issue_setup_uniform_within_bounds() {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let op = AuctionOperator {
            n_bidders: 3,
            valuation_dist: ValuationDistribution::Uniform { low: 1, high: 100 },
        };
        for _ in 0..200 {
            let setups = op.issue_setup(3, &mut rng);
            for s in &setups {
                assert!(
                    (1..=100).contains(&s.valuation),
                    "valuation {} out of bounds",
                    s.valuation
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "AuctionOperator requires at least 3 agents")]
    fn issue_setup_rejects_too_few_agents() {
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        let _ = op_n(2).issue_setup(2, &mut rng);
    }

    // --- Hash unit test ---------------------------------------------------

    #[test]
    fn recompute_commit_hash_is_stable_and_format_matches_cbcl_agent() {
        let h = recompute_commit_hash("99", "salt-A");
        assert!(h.starts_with('h'));
        assert_eq!(h.len(), 33);
        assert!(h[1..]
            .chars()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()));

        let h2 = recompute_commit_hash("99", "salt-A");
        assert_eq!(h, h2);

        let h3 = recompute_commit_hash("99", "salt-B");
        assert_ne!(h, h3);
    }

    // --- 7. Property test: 50 random honest transcripts -------------------

    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig { cases: 50, .. ProptestConfig::default() })]

        #[test]
        fn honest_transcripts_score_correctly(
            v0 in 1u64..=100,
            v1 in 1u64..=100,
            v2 in 1u64..=100,
        ) {
            // Skip ties: tie-breaking is deterministic but the property
            // here is "honest play scores correctly", independent of ties.
            prop_assume!(v0 != v1 && v0 != v2 && v1 != v2);

            let valuations = [v0, v1, v2];
            let setups = manual_setups(&valuations);
            let (transcript, guesses, _winner_idx) = honest_transcript(&valuations);

            let scores = op_n(3).score(&setups, &transcript, &guesses);

            for (i, s) in scores.iter().enumerate() {
                prop_assert_eq!(s.security, 1, "honest play preserves security for agent {}", i);
                prop_assert_eq!(s.utility, 1, "honest play awards utility for agent {}", i);
            }
        }
    }
}
