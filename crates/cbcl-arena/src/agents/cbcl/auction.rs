//! auction: Sealed-bid auction strategy for the CBCL-disciplined agent
//! (REQ-410 / REQ-412 / REQ-414).
//!
//! Implements the three-phase commit-reveal-declare auction per
//! `demo/dialects/auction.cbcl`:
//!
//! ```text
//! begin
//!   ↓
//! commit (bid-commitment :hash H)            -- once per bidder
//!   ↓
//! reveal (bid-reveal :body :salt :proof-commit H)
//!   ↓
//! declare-winner (winner-declaration :winner :winning-bid
//!                                    :proof-commit :proof-reveal)
//!     -- emitted only by the auctioneer (lowest agent_idx).
//! ```
//!
//! ## Hash bindings
//!
//! - The commit's `:hash` field is `H = strategy_hash(valuation || "|" || salt)`.
//!   The reveal's `:proof-commit` MUST equal this `H`, and recipients verify
//!   `strategy_hash(body || "|" || salt) == proof-commit` before accepting
//!   the reveal into strategy state. Mismatches that parse and survive
//!   `verify_causal` (i.e. land in `ingest_inbound`) are recorded in the
//!   strategy's `binding_quarantine` set and do NOT update `other_reveals`.
//!
//! - The winner-declaration's `:proof-commit` echoes the winner's commit
//!   `:hash`, and `:proof-reveal` is `strategy_hash(commit_hash || body || salt)` —
//!   a deterministic derivative each peer can recompute from its observed
//!   reveal tuple `(valuation, salt, commit_hash)`. Both citations are
//!   verified on receipt; verification failure routes to `binding_quarantine`.
//!
//! ## Auctioneer convention
//!
//! Per `auction.cbcl`'s top-of-file comment, the auctioneer is "the lowest
//! `agent_idx` by convention". `AuctionSetup` carries `agent_idx` and
//! `n_bidders`; we derive `is_auctioneer = (agent_idx == 0)`.
//!
//! ## Coordination note
//!
//! `AuctionSetup` and `AuctionGuess` are imported from
//! [`crate::operator::auction`]. The operator-side stub in main only
//! declares the type shapes; the full operator implementation is being
//! produced by a sister IMPL task. Our strategy depends on the *type
//! signatures* and is robust to the operator's internal scoring evolution.

use std::collections::{BTreeMap, BTreeSet};

use cbcl_core::message::Message;
use cbcl_core::sexpr::{Atom, SExpr};
use rand::RngCore;

use super::content;
use super::CausedBySelector;
use super::ChallengeStrategy;
use super::OutboundDraft;

use crate::operator::auction::{AuctionGuess, AuctionSetup};

/// Internal phases of the auction state machine.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AuctionState {
    /// Pre-emit. Will emit own commit on first poll.
    Init,
    /// Own commit emitted; waiting for `n_bidders - 1` peer commits.
    AwaitingPeerCommits,
    /// Own reveal emitted; waiting for `n_bidders - 1` peer reveals.
    AwaitingPeerReveals,
    /// Auctioneer will emit `declare-winner` on the next poll;
    /// non-auctioneer is waiting to ingest the declaration.
    AwaitingDeclaration,
    /// Strategy complete.
    Done,
}

/// Sealed-bid auction strategy state machine.
pub struct AuctionCbclStrategy {
    /// Setup payload (received once via `ingest_setup`).
    setup: Option<AuctionSetup>,
    /// Random salt used for own commitment. Generated lazily on first poll.
    salt: [u8; 16],
    /// Whether `salt` has been initialised.
    salt_initialised: bool,
    /// Hash committed in our own `commit` message (the `:hash` value).
    own_commit_hash: Option<String>,
    /// Hash bound to our own reveal (used as `:proof-reveal` in the
    /// winner-declaration when we win).
    own_reveal_hash: Option<String>,
    /// Peer commits observed: `agent_idx → commit_hash`.
    other_commits: BTreeMap<usize, String>,
    /// Peer reveals observed and verified: `agent_idx → (valuation, salt, commit_hash)`.
    other_reveals: BTreeMap<usize, (u64, String, String)>,
    /// Winner declared by the auctioneer (set either on own emission or
    /// on receipt of a verified declaration message).
    declared_winner: Option<(usize, u64)>,
    /// Strategy-level quarantine for messages that parsed and verified
    /// causally but failed the protocol's hash-binding invariants.
    binding_quarantine: BTreeSet<String>,
    state: AuctionState,
}

impl AuctionCbclStrategy {
    /// Construct a fresh auction strategy.
    pub fn new() -> Self {
        Self {
            setup: None,
            salt: [0u8; 16],
            salt_initialised: false,
            own_commit_hash: None,
            own_reveal_hash: None,
            other_commits: BTreeMap::new(),
            other_reveals: BTreeMap::new(),
            declared_winner: None,
            binding_quarantine: BTreeSet::new(),
            state: AuctionState::Init,
        }
    }

    fn n_bidders(&self) -> usize {
        self.setup.as_ref().map(|s| s.n_bidders).unwrap_or(0)
    }

    fn agent_idx(&self) -> usize {
        self.setup.as_ref().map(|s| s.agent_idx).unwrap_or(0)
    }

    fn valuation(&self) -> u64 {
        self.setup.as_ref().map(|s| s.valuation).unwrap_or(0)
    }

    /// Auctioneer flag — by dialect convention (auction.cbcl preamble) the
    /// auctioneer is the lowest `agent_idx`.
    fn is_auctioneer(&self) -> bool {
        self.agent_idx() == 0
    }

    fn salt_string(&self) -> String {
        let mut s = String::with_capacity(32);
        for b in &self.salt {
            s.push_str(&format!("{:02x}", b));
        }
        s
    }

    /// Compute the commit-hash binding `(valuation, salt)`.
    fn commit_hash_for(valuation: u64, salt: &str) -> String {
        let buf = format!("{}|{}", valuation, salt);
        super::strategy_hash(buf.as_bytes())
    }

    /// Compute the proof-reveal token binding `(commit_hash, body, salt)`.
    fn reveal_hash_for(commit_hash: &str, valuation: u64, salt: &str) -> String {
        let buf = format!("{}|{}|{}", commit_hash, valuation, salt);
        super::strategy_hash(buf.as_bytes())
    }

    /// Highest valuation across all known reveals (own + others). Returns
    /// `(agent_idx, valuation, commit_hash, reveal_hash)`. Lower agent_idx
    /// breaks ties for determinism.
    fn winner_from_reveals(&self) -> Option<(usize, u64, String, String)> {
        let mut all: Vec<(usize, u64, String, String)> = Vec::new();
        if let (Some(commit_h), Some(reveal_h)) =
            (self.own_commit_hash.as_ref(), self.own_reveal_hash.as_ref())
        {
            all.push((
                self.agent_idx(),
                self.valuation(),
                commit_h.clone(),
                reveal_h.clone(),
            ));
        }
        for (idx, (val, salt, commit_h)) in &self.other_reveals {
            let reveal_h = Self::reveal_hash_for(commit_h, *val, salt);
            all.push((*idx, *val, commit_h.clone(), reveal_h));
        }
        all.into_iter().max_by(|a, b| {
            // Higher valuation wins; lower agent_idx breaks ties.
            a.1.cmp(&b.1).then_with(|| b.0.cmp(&a.0))
        })
    }

    /// Extract the seat index of the message sender from its `:sender`
    /// field. The test harness assigns sender ids of the form
    /// `bidder-<idx>`; we accept that form and a bare-integer fallback.
    fn sender_idx(msg: &Message) -> Option<usize> {
        let inner = msg.innermost_simple().unwrap_or(msg);
        let s = inner.sender()?;
        if let Some(rest) = s.strip_prefix("bidder-") {
            return rest.parse::<usize>().ok();
        }
        let tail: String = s.chars().rev().take_while(|c| c.is_ascii_digit()).collect();
        let tail: String = tail.chars().rev().collect();
        tail.parse::<usize>().ok()
    }

    fn extract_u64(e: &SExpr) -> Option<u64> {
        match e {
            SExpr::Atom(Atom::Num(n)) if *n >= 0 => Some(*n as u64),
            SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) => s.parse::<u64>().ok(),
            _ => None,
        }
    }

    fn extract_usize(e: &SExpr) -> Option<usize> {
        match e {
            SExpr::Atom(Atom::Num(n)) if *n >= 0 => Some(*n as usize),
            SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) => s.parse::<usize>().ok(),
            _ => None,
        }
    }
}

impl Default for AuctionCbclStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl ChallengeStrategy for AuctionCbclStrategy {
    type Setup = AuctionSetup;
    type Guess = AuctionGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(setup);
    }

    fn ingest_inbound(&mut self, msg: &Message) {
        let inner = msg.innermost_simple().unwrap_or(msg);
        let perf = match inner.performative() {
            Some(p) => p.name().to_string(),
            None => return,
        };
        let sender = match Self::sender_idx(msg) {
            Some(i) => i,
            None => return,
        };
        match perf.as_str() {
            "commit" => {
                if let Some(hash_e) = content::get_kw(inner, "hash") {
                    if let Some(h) = content::as_string(hash_e) {
                        self.other_commits.insert(sender, h);
                    }
                }
            }
            "reveal" => {
                let body = content::get_kw(inner, "body").and_then(Self::extract_u64);
                let salt = content::get_kw(inner, "salt").and_then(content::as_string);
                let proof = content::get_kw(inner, "proof-commit").and_then(content::as_string);
                let (Some(body), Some(salt), Some(proof)) = (body, salt, proof) else {
                    self.binding_quarantine
                        .insert(format!("malformed-reveal:{sender}"));
                    return;
                };
                // Verify the recomputed binding equals the cited proof-commit.
                let recomputed = Self::commit_hash_for(body, &salt);
                if recomputed != proof {
                    self.binding_quarantine
                        .insert(format!("bad-reveal:{sender}"));
                    return;
                }
                // Cross-check: peer's earlier commit hash (if any) must match.
                if let Some(prior) = self.other_commits.get(&sender) {
                    if *prior != proof {
                        self.binding_quarantine
                            .insert(format!("commit-mismatch:{sender}"));
                        return;
                    }
                }
                self.other_reveals.insert(sender, (body, salt, proof));
            }
            "declare-winner" => {
                let winner =
                    content::get_kw(inner, "winner").and_then(Self::extract_usize);
                let bid =
                    content::get_kw(inner, "winning-bid").and_then(Self::extract_u64);
                let proof_commit =
                    content::get_kw(inner, "proof-commit").and_then(content::as_string);
                let proof_reveal =
                    content::get_kw(inner, "proof-reveal").and_then(content::as_string);
                let (Some(winner), Some(bid), Some(pc), Some(pr)) =
                    (winner, bid, proof_commit, proof_reveal)
                else {
                    self.binding_quarantine
                        .insert("malformed-declare-winner".to_string());
                    return;
                };
                // Resolve the cited commit & reveal against our local view.
                let resolves = if winner == self.agent_idx() {
                    self.own_commit_hash.as_deref() == Some(&pc)
                        && self.own_reveal_hash.as_deref() == Some(&pr)
                        && bid == self.valuation()
                } else if let Some((val, salt, commit_h)) = self.other_reveals.get(&winner) {
                    *commit_h == pc
                        && Self::reveal_hash_for(commit_h, *val, salt) == pr
                        && bid == *val
                } else {
                    false
                };
                if !resolves {
                    self.binding_quarantine
                        .insert("bad-declare-winner".to_string());
                    return;
                }
                self.declared_winner = Some((winner, bid));
            }
            _ => {}
        }
    }

    fn next_outbound(&mut self, rng: &mut dyn RngCore) -> Option<OutboundDraft> {
        // Lazy salt initialisation on first poll (uses the strategy rng).
        if !self.salt_initialised {
            for chunk in self.salt.chunks_mut(8) {
                let bytes = rng.next_u64().to_le_bytes();
                let n = chunk.len();
                chunk.copy_from_slice(&bytes[..n]);
            }
            self.salt_initialised = true;
        }
        match self.state {
            AuctionState::Init => {
                let salt = self.salt_string();
                let h = Self::commit_hash_for(self.valuation(), &salt);
                self.own_commit_hash = Some(h.clone());
                self.state = AuctionState::AwaitingPeerCommits;
                Some(OutboundDraft {
                    performative: "commit".to_string(),
                    recipient: Some("@auctioneer".to_string()),
                    content: content::keyword_form(
                        "bid-commitment",
                        &[("hash", SExpr::Atom(Atom::Str(h)))],
                    ),
                    caused_by: CausedBySelector::Begin,
                })
            }
            AuctionState::AwaitingPeerCommits => {
                let need = self.n_bidders().saturating_sub(1);
                if self.other_commits.len() < need {
                    return None;
                }
                let salt = self.salt_string();
                let val = self.valuation();
                let commit_h = self.own_commit_hash.clone().unwrap_or_default();
                let reveal_h = Self::reveal_hash_for(&commit_h, val, &salt);
                self.own_reveal_hash = Some(reveal_h);
                self.state = AuctionState::AwaitingPeerReveals;
                Some(OutboundDraft {
                    performative: "reveal".to_string(),
                    recipient: Some("@auctioneer".to_string()),
                    content: content::keyword_form(
                        "bid-reveal",
                        &[
                            ("body", SExpr::Atom(Atom::Num(val as i64))),
                            ("salt", SExpr::Atom(Atom::Str(salt))),
                            ("proof-commit", SExpr::Atom(Atom::Str(commit_h))),
                        ],
                    ),
                    caused_by: CausedBySelector::LatestOfPerformative("commit".to_string()),
                })
            }
            AuctionState::AwaitingPeerReveals => {
                let need = self.n_bidders().saturating_sub(1);
                if self.other_reveals.len() < need {
                    return None;
                }
                self.state = AuctionState::AwaitingDeclaration;
                self.next_outbound(rng)
            }
            AuctionState::AwaitingDeclaration => {
                if self.is_auctioneer() {
                    let (winner_idx, winning_bid, commit_h, reveal_h) =
                        match self.winner_from_reveals() {
                            Some(t) => t,
                            None => return None,
                        };
                    self.declared_winner = Some((winner_idx, winning_bid));
                    self.state = AuctionState::Done;
                    Some(OutboundDraft {
                        performative: "declare-winner".to_string(),
                        recipient: Some("@bidders".to_string()),
                        content: content::keyword_form(
                            "winner-declaration",
                            &[
                                ("winner", SExpr::Atom(Atom::Num(winner_idx as i64))),
                                (
                                    "winning-bid",
                                    SExpr::Atom(Atom::Num(winning_bid as i64)),
                                ),
                                ("proof-commit", SExpr::Atom(Atom::Str(commit_h))),
                                ("proof-reveal", SExpr::Atom(Atom::Str(reveal_h))),
                            ],
                        ),
                        caused_by: CausedBySelector::LatestOfPerformative(
                            "reveal".to_string(),
                        ),
                    })
                } else {
                    if self.declared_winner.is_some() {
                        self.state = AuctionState::Done;
                    }
                    None
                }
            }
            AuctionState::Done => None,
        }
    }

    fn final_guess(&self) -> Self::Guess {
        match self.declared_winner {
            Some((agent_idx, bid)) => AuctionGuess::Winner { agent_idx, bid },
            None => AuctionGuess::Unknown,
        }
    }

    fn is_done(&self) -> bool {
        self.state == AuctionState::Done
    }
}

// =====================================================================
// TESTS
// =====================================================================

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use cbcl_core::dialect::Dialect;
    use cbcl_core::message::Message;
    use cbcl_parser::{parse, parse_message};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::agents::cbcl::{load_dialect, CbclAgent, ChallengeStrategy, StepStatus};
    use crate::operator::ChatEvent;

    const AUCTION_DIALECT_SRC: &str =
        include_str!("../../../../../demo/dialects/auction.cbcl");

    fn auction_dialect() -> Dialect {
        load_dialect(AUCTION_DIALECT_SRC).expect("auction dialect parses")
    }

    /// Round-robin step harness, mirrors `agents/cbcl/tests.rs::run_game`.
    fn run_game(
        agents: &mut [CbclAgent<AuctionCbclStrategy>],
        setups: Vec<AuctionSetup>,
        rng_seed: u64,
    ) -> (Vec<ChatEvent>, Vec<AuctionGuess>) {
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

        for _round in 0..256 {
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
            if !any_progress {
                break;
            }
            if !any_unfinished {
                break;
            }
        }

        let guesses: Vec<AuctionGuess> =
            agents.iter().map(|a| a.strategy.final_guess()).collect();
        (transcript, guesses)
    }

    fn assert_dialect_conformance(transcript: &[ChatEvent], dialect: &Dialect) {
        let allowed: BTreeSet<&str> = dialect.performative_names().into_iter().collect();
        for ev in transcript {
            let text = std::str::from_utf8(&ev.payload)
                .unwrap_or_else(|_| panic!("emitted non-utf8 payload"));
            let sexpr = parse(text)
                .unwrap_or_else(|e| panic!("emitted unparsable s-expr: {e:?}\n{text}"));
            let msg: Message = parse_message(&sexpr)
                .unwrap_or_else(|e| panic!("emitted non-CBCL message: {e}\n{text}"));
            let inner = msg.innermost_simple().unwrap_or(&msg);
            let perf = inner.performative().expect("simple message").name();
            assert!(
                allowed.contains(perf),
                "performative '{}' not declared in dialect '{}': allowed = {:?}",
                perf,
                dialect.name,
                allowed,
            );
        }
    }

    fn build_agents(
        n: usize,
        dialect: &Dialect,
        thread_root: &str,
    ) -> Vec<CbclAgent<AuctionCbclStrategy>> {
        (0..n)
            .map(|i| {
                CbclAgent::new(
                    dialect.clone(),
                    AuctionCbclStrategy::new(),
                    thread_root,
                    format!("bidder-{i}"),
                )
            })
            .collect()
    }

    fn build_setups(valuations: &[u64]) -> Vec<AuctionSetup> {
        let n = valuations.len();
        valuations
            .iter()
            .enumerate()
            .map(|(i, v)| AuctionSetup {
                agent_idx: i,
                n_bidders: n,
                valuation: *v,
                is_auctioneer: i == 0,
            })
            .collect()
    }

    // -----------------------------------------------------------------
    // 1. Honest 3-agent game with fixed seed.
    // -----------------------------------------------------------------
    #[test]
    fn auction_honest_3_agents_fixed_seed() {
        let dialect = auction_dialect();
        let valuations = vec![17u64, 42, 88];
        let true_winner = 2usize;
        let true_bid = 88u64;

        let mut agents = build_agents(3, &dialect, "auction-game-fixed");
        let setups = build_setups(&valuations);
        let (transcript, guesses) = run_game(&mut agents, setups, 0xa1c1);

        assert_dialect_conformance(&transcript, &dialect);

        // Auctioneer is bidder-0.
        let auctioneer_guess = guesses[0].clone();
        assert_eq!(
            auctioneer_guess,
            AuctionGuess::Winner {
                agent_idx: true_winner,
                bid: true_bid,
            },
            "auctioneer mis-identified winner: {:?}",
            auctioneer_guess
        );
        for (i, g) in guesses.iter().enumerate() {
            assert_eq!(
                *g, auctioneer_guess,
                "agent {i} disagreed with auctioneer's declaration"
            );
        }
        for (i, a) in agents.iter().enumerate() {
            assert!(
                a.quarantine.is_empty(),
                "agent {i} quarantined an honest message: {:?}",
                a.quarantine
            );
            assert!(
                a.strategy.binding_quarantine.is_empty(),
                "agent {i} flagged binding violation: {:?}",
                a.strategy.binding_quarantine
            );
        }
    }

    // -----------------------------------------------------------------
    // 2. 30 random honest games.
    // -----------------------------------------------------------------
    #[test]
    fn auction_honest_3_agents_30_random_games() {
        const N_GAMES: u64 = 30;
        let dialect = auction_dialect();

        for game in 0..N_GAMES {
            let mut rng = ChaCha8Rng::seed_from_u64(0xbe11u64.wrapping_add(game));
            let valuations: Vec<u64> =
                (0..3).map(|_| rng.gen_range(1..=100u64)).collect();

            let mut indexed: Vec<(usize, u64)> =
                valuations.iter().copied().enumerate().collect();
            indexed.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            let (true_winner, true_bid) = indexed[0];

            let thread_root = format!("auction-game-{game}");
            let mut agents = build_agents(3, &dialect, &thread_root);
            let setups = build_setups(&valuations);
            let (transcript, guesses) = run_game(&mut agents, setups, game);

            assert_dialect_conformance(&transcript, &dialect);

            let auctioneer_guess = guesses[0].clone();
            assert_eq!(
                auctioneer_guess,
                AuctionGuess::Winner {
                    agent_idx: true_winner,
                    bid: true_bid
                },
                "game {game}: auctioneer mis-declared winner (vals = {:?})",
                valuations
            );
            for (i, g) in guesses.iter().enumerate() {
                assert_eq!(
                    *g, auctioneer_guess,
                    "game {game}: agent {i} disagreed with declaration (vals = {:?})",
                    valuations
                );
            }
            for (i, a) in agents.iter().enumerate() {
                assert!(
                    a.quarantine.is_empty(),
                    "game {game}: agent {i} quarantined honest message: {:?}",
                    a.quarantine
                );
                assert!(
                    a.strategy.binding_quarantine.is_empty(),
                    "game {game}: agent {i} flagged binding violation: {:?}",
                    a.strategy.binding_quarantine
                );
            }
        }
    }

    // -----------------------------------------------------------------
    // 3. Bad-reveal rejection: a reveal whose body+salt does NOT bind to
    //    the cited proof-commit lands in `binding_quarantine`, NOT in
    //    `other_reveals`.
    // -----------------------------------------------------------------
    #[test]
    fn auction_bad_reveal_lands_in_binding_quarantine() {
        let dialect = auction_dialect();
        let mut agent = CbclAgent::new(
            dialect.clone(),
            AuctionCbclStrategy::new(),
            "auction-bad-reveal",
            "bidder-0",
        );
        super::super::ingest_setup(
            &mut agent,
            AuctionSetup {
                agent_idx: 0,
                n_bidders: 2,
                valuation: 50,
                is_auctioneer: true,
            },
        );

        // Drive the agent forward one step so it emits its own commit and
        // populates the local store; we need that for `verify_causal` to
        // admit the synthesised peer-commit + reveal pair below.
        let mut rng = ChaCha8Rng::seed_from_u64(0xbad);
        let mut send_idx = 0u64;
        let mut emissions: Vec<ChatEvent> = Vec::new();
        {
            let mut empty = std::iter::empty();
            let mut sink = |ev: ChatEvent| emissions.push(ev);
            let _ = agent.step(&mut empty, &mut sink, &mut rng, &mut send_idx);
        }
        assert_eq!(emissions.len(), 1, "agent did not emit commit");

        // Synthesise peer-1's commit. The honest commit hash for valuation=77
        // would be `h1`. We use this hash in both the commit (truthful) and
        // the reveal (which lies about the body).
        let peer_salt = "deadbeefdeadbeefdeadbeefdeadbeef";
        let true_val: u64 = 77;
        let h1 = AuctionCbclStrategy::commit_hash_for(true_val, peer_salt);

        let peer_commit = format!(
            "(commit (bid-commitment :hash \"{}\") :thread auction-bad-reveal :sender bidder-1 :caused-by begin)",
            h1
        );
        // We need the peer-commit's *content hash* (not the body's `h1`) for
        // the reveal's `:caused-by`, since `verify_causal` walks the agent's
        // store of accepted messages by content hash. Replicate the agent's
        // FNV-1a-128-of-canonical-serialise computation here.
        let peer_commit_msg = cbcl_parser::parse_message(
            &cbcl_parser::parse(&peer_commit).expect("parse peer-commit s-expr"),
        )
        .expect("parse peer-commit message");
        let peer_commit_hash = {
            let s = cbcl_core::serializer::serialize(
                &cbcl_core::sexpr::SExpr::from(&peer_commit_msg),
            );
            // strategy_hash is FNV-1a-128 hex *without* the leading `h`; the
            // agent uses `h<hex>` so the symbol round-trips through the parser.
            format!("h{}", super::super::strategy_hash(s.as_bytes()))
        };
        let ev = ChatEvent {
            agent_idx: 1,
            send_index: 100,
            payload: peer_commit.into_bytes(),
        };
        {
            let mut iter = std::iter::once(ev);
            let mut sink = |_ev: ChatEvent| {};
            let _ = agent.step(&mut iter, &mut sink, &mut rng, &mut send_idx);
        }
        assert!(
            agent.quarantine.is_empty(),
            "honest peer commit was quarantined: {:?}",
            agent.quarantine
        );
        assert_eq!(
            agent.strategy.other_commits.get(&1).cloned(),
            Some(h1.clone()),
            "peer commit not recorded in other_commits"
        );

        // Construct a *bad* reveal that cites `h1` but body=99 (a lie).
        let bad_body: u64 = 99;
        let peer_reveal = format!(
            "(reveal (bid-reveal :body {} :salt \"{}\" :proof-commit \"{}\") :thread auction-bad-reveal :sender bidder-1 :caused-by {})",
            bad_body, peer_salt, h1, peer_commit_hash
        );
        let ev = ChatEvent {
            agent_idx: 1,
            send_index: 101,
            payload: peer_reveal.into_bytes(),
        };
        {
            let mut iter = std::iter::once(ev);
            let mut sink = |_ev: ChatEvent| {};
            let _ = agent.step(&mut iter, &mut sink, &mut rng, &mut send_idx);
        }

        // The reveal parsed and survived `verify_causal` (its `:caused-by`
        // points to the commit we appended), so it landed in `ingest_inbound`.
        // The strategy's binding check rejected it.
        assert!(
            agent.quarantine.is_empty(),
            "bad reveal wrongly placed in agent quarantine: {:?}",
            agent.quarantine
        );
        assert!(
            !agent.strategy.binding_quarantine.is_empty(),
            "bad reveal did not populate binding_quarantine"
        );
        assert!(
            agent.strategy.other_reveals.is_empty(),
            "bad reveal wrongly updated other_reveals: {:?}",
            agent.strategy.other_reveals
        );
    }
}
