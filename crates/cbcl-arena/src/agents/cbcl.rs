//! cbcl: CBCL-disciplined agent strategy (REQ-1120 / CON-1120).
//!
//! `CbclAgent<S>` is the load-bearing artefact of SPEC-011: a per-challenge
//! agent that is *only* able to emit messages from the challenge's dialect
//! and that drops every inbound message that fails to parse or whose
//! causal-link does not validate against the dialect's `(protocol …)` clause.
//!
//! ## Architecture
//!
//! The agent is parameterised by a [`ChallengeStrategy`] — the per-challenge
//! state machine that owns the private setup, decides what to emit next,
//! and computes the operator-bound guess. The agent itself owns the
//! *discipline*: parsing, causal verification, quarantine, threading.
//!
//! ## Thread discipline (ADR-008)
//!
//! All agents in a single game share a `thread_root`, used as the `:thread`
//! field on every outbound message. Each agent maintains an in-memory
//! [`MessageStore`](cbcl_core::store::MessageStore) populated with the
//! messages it has *accepted* (its own outbound, plus peers' inbound that
//! survived `verify_causal`). Quarantined messages NEVER enter the store and
//! NEVER influence strategy state (CON-1120 post-condition #3).
//!
//! ## Hash function
//!
//! Outbound messages need stable, distinct content hashes so the peer can
//! reference them via `:caused-by`. We use a 128-bit FNV-1a digest over the
//! canonical S-expression serialisation; this is deterministic, dependency-
//! free (NFR-1112), and adequate for the simulator's discipline-checking
//! purpose. It is *not* cryptographic — the simulator's threat model does
//! not include collision attacks (TM-1101 Honest-cooperative cell).
//!
//! Submodules:
//! - [`psi`]          — PSI strategy (REQ-1110-paired).
//! - [`millionaire`]  — Yao's Millionaire strategy (REQ-1111-paired).
//! - [`dining`]       — Dining Cryptographers strategy (REQ-1112-paired).

use cbcl_core::message::{CausedBy, Message, Performative};
use cbcl_core::protocol::{verify_causal, VerificationResult};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use cbcl_parser::{parse, parse_message};
use rand::RngCore;

use super::Agent;
use crate::operator::ChatEvent;

pub mod auction;
pub mod dining;
pub mod millionaire;
pub mod psi;

/// One quarantined inbound message together with the reason it was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuarantineEntry {
    /// Driver-assigned send index of the offending event.
    pub send_index: u64,
    /// Why the agent rejected the message.
    pub reason: QuarantineReason,
    /// The raw bytes the driver delivered.
    pub bytes: Vec<u8>,
}

/// Reason a message was quarantined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuarantineReason {
    /// The byte string failed to parse as an S-expression or as a CBCL message.
    ParseError(String),
    /// The message parsed but `verify_causal` returned `Violation`.
    CausalViolation(String),
    /// The message parsed but `verify_causal` returned `Unknown`
    /// (predecessor missing from this agent's store).
    CausalUnknown,
}

/// CBCL-disciplined agent (CON-1120).
///
/// `S` is the per-challenge [`ChallengeStrategy`] state machine.
pub struct CbclAgent<S: ChallengeStrategy> {
    /// The challenge dialect, parsed from `demo/dialects/<challenge>.cbcl`.
    pub dialect: cbcl_core::dialect::Dialect,
    /// Per-challenge strategy state machine.
    pub strategy: S,
    /// Session-shared `:thread` value used on every outbound message.
    pub thread_root: String,
    /// Sender id used as `:sender` on outbound messages.
    pub sender_id: String,
    /// Quarantine buffer (CON-1120 post-condition #2).
    pub quarantine: Vec<QuarantineEntry>,
    /// Accepted-message store. Both own outbound and peers' valid inbound
    /// land in the same `:thread = thread_root` so cross-sender
    /// `:caused-by` references resolve (ADR-008).
    store: ThreadedMessageStore,
}

/// Per-challenge strategy state machine.
///
/// The discipline (parse, verify_causal, quarantine, hash, store) lives in
/// [`CbclAgent`]; the strategy lives here. `ingest_inbound` is called only
/// after a message has parsed AND `verify_causal` has returned `Valid`.
pub trait ChallengeStrategy {
    /// Operator-issued private setup payload.
    type Setup;
    /// Operator-bound guess type submitted at end-of-game.
    type Guess;

    /// Called once before any chat: agent absorbs its private setup.
    fn ingest_setup(&mut self, setup: Self::Setup);

    /// Called once per Valid inbound message (post-`verify_causal`).
    /// May update internal state but MUST NOT emit chat directly.
    fn ingest_inbound(&mut self, msg: &Message);

    /// Called once per turn: returns the next outbound CBCL [`Message`] to
    /// send, or `None` if the agent has nothing more to say this turn.
    /// Successive calls within a single turn drain all outbound until `None`.
    ///
    /// The strategy is responsible for the message's `performative`,
    /// `content`, and (logical) predecessor selector; the wrapping agent
    /// fills in `:thread`, `:sender`, and resolves `:caused-by`.
    fn next_outbound(&mut self, rng: &mut dyn RngCore) -> Option<OutboundDraft>;

    /// Compute the operator-bound guess. Called once at end-of-game.
    /// MUST be derived from accepted-message state only (CON-1120 post-#3).
    fn final_guess(&self) -> Self::Guess;

    /// Whether the strategy has run to completion. The agent's outer loop
    /// terminates when this returns true AND the inbound channel is empty.
    fn is_done(&self) -> bool;
}

/// A strategy-emitted message draft. The agent fills in `:thread`,
/// `:sender`, and `:caused-by` before sending.
#[derive(Clone, Debug)]
pub struct OutboundDraft {
    /// Performative name (one of the dialect's `(extend …)` step names).
    pub performative: String,
    /// Recipient symbol — `@peer` for two-party games, `@peers` for DC,
    /// `@operator` for the final-guess submission.
    pub recipient: Option<String>,
    /// Message content S-expression (the `(set-commitment :root … :count …)`
    /// form per the dialect templates).
    pub content: SExpr,
    /// `:caused-by` predecessor selector. The agent resolves this against
    /// its store at send time.
    pub caused_by: CausedBySelector,
}

/// Strategy-level selector for `:caused-by`. The agent resolves it against
/// its own store at send time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CausedBySelector {
    /// Root of the causal chain — emits `:caused-by begin`.
    Begin,
    /// Most-recent accepted message whose performative is `name`.
    LatestOfPerformative(String),
    /// Multiple predecessors — fan-in. The agent picks the most recent of
    /// each named performative; if any are absent the message is skipped
    /// (build_outbound returns None).
    AllOfPerformatives(Vec<String>),
}

impl<S> CbclAgent<S>
where
    S: ChallengeStrategy,
{
    /// Construct a new disciplined agent.
    pub fn new(
        dialect: cbcl_core::dialect::Dialect,
        strategy: S,
        thread_root: impl Into<String>,
        sender_id: impl Into<String>,
    ) -> Self {
        Self {
            dialect,
            strategy,
            thread_root: thread_root.into(),
            sender_id: sender_id.into(),
            quarantine: Vec::new(),
            store: ThreadedMessageStore::new(),
        }
    }

    /// The session `:thread` used for every outbound message.
    fn thread_id(&self) -> ThreadId {
        ThreadId(self.thread_root.clone())
    }

    /// 128-bit FNV-1a digest, hex-encoded with a leading `h` so the
    /// resulting symbol round-trips through the CBCL parser (which
    /// otherwise interprets a leading-digit token as a number).
    fn hash_bytes(bytes: &[u8]) -> String {
        // FNV-1a 128 reference parameters.
        const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
        const PRIME: u128 = 0x0000000001000000000000000000013b;
        let mut h: u128 = OFFSET;
        for &b in bytes {
            h ^= b as u128;
            h = h.wrapping_mul(PRIME);
        }
        format!("h{:032x}", h)
    }

    /// Compute the content hash for a CBCL message — the FNV-1a digest of
    /// its canonical serialisation.
    fn content_hash(msg: &Message) -> ContentHash {
        let s = serialize(&SExpr::from(msg));
        ContentHash(Self::hash_bytes(s.as_bytes()))
    }

    /// Find the hash of the most recent accepted message whose performative
    /// matches `name`, in this agent's session thread.
    fn latest_hash_of(&self, name: &str) -> Option<ContentHash> {
        let thread = self.thread_id();
        // Collect every (hash, message) in the thread by walking the
        // closure of every frontier leaf. This is O(n²) but n is tiny
        // (game-bounded) and the only correctness requirement is "most
        // recent" — we approximate that by preferring the leaves.
        let frontier: Vec<ContentHash> =
            self.store.frontier(&thread).into_iter().cloned().collect();
        for h in &frontier {
            if let Some(m) = self.store.lookup_in_thread(h, &thread) {
                let inner = m.innermost_simple().unwrap_or(m);
                if performative_name(inner).as_deref() == Some(name) {
                    return Some(h.clone());
                }
            }
        }
        // Fallback: full-thread scan via causal closures.
        for leaf in &frontier {
            for h in self.store.causal_closure(leaf, &thread) {
                if let Some(m) = self.store.lookup_in_thread(&h, &thread) {
                    let inner = m.innermost_simple().unwrap_or(m);
                    if performative_name(inner).as_deref() == Some(name) {
                        return Some(h);
                    }
                }
            }
        }
        None
    }

    /// Resolve a strategy-level [`CausedBySelector`] into a wire-format
    /// [`CausedBy`].
    fn resolve_caused_by(&self, selector: &CausedBySelector) -> Option<CausedBy> {
        match selector {
            CausedBySelector::Begin => Some(CausedBy::Begin),
            CausedBySelector::LatestOfPerformative(name) => {
                self.latest_hash_of(name).map(|h| CausedBy::Single(h.0))
            }
            CausedBySelector::AllOfPerformatives(names) => {
                let mut hashes = Vec::with_capacity(names.len());
                for n in names {
                    hashes.push(self.latest_hash_of(n)?.0);
                }
                hashes.sort();
                Some(CausedBy::Multiple(hashes))
            }
        }
    }

    /// Build a wire-format [`Message`] from a strategy-emitted
    /// [`OutboundDraft`]. Returns `None` if `:caused-by` cannot be resolved
    /// (e.g. fan-in references an absent predecessor).
    fn build_outbound(&self, draft: &OutboundDraft) -> Option<Message> {
        let caused_by = self.resolve_caused_by(&draft.caused_by)?;
        Some(Message::Simple {
            performative: Performative::Custom(draft.performative.clone()),
            recipient: draft.recipient.clone(),
            content: draft.content.clone(),
            params: Vec::new(),
            thread: Some(self.thread_root.clone()),
            sender: Some(self.sender_id.clone()),
            caused_by: Some(caused_by),
        })
    }

    /// Handle one inbound chat event: parse, verify_causal, dispatch or
    /// quarantine.
    fn handle_inbound(&mut self, event: &ChatEvent) {
        // Skip events that the driver attributed to ourselves: a single
        // chat channel echoes own sends back, which we must not re-process.
        // We can't see agent_idx here without driver coordination, so we
        // distinguish by `:sender` after parsing.

        // Step 1: bytes → str.
        let text = match core::str::from_utf8(&event.payload) {
            Ok(t) => t,
            Err(e) => {
                self.quarantine.push(QuarantineEntry {
                    send_index: event.send_index,
                    reason: QuarantineReason::ParseError(format!("non-utf8: {e}")),
                    bytes: event.payload.clone(),
                });
                return;
            }
        };
        // Step 2: str → SExpr.
        let sexpr = match parse(text) {
            Ok(s) => s,
            Err(e) => {
                self.quarantine.push(QuarantineEntry {
                    send_index: event.send_index,
                    reason: QuarantineReason::ParseError(format!("sexpr: {e:?}")),
                    bytes: event.payload.clone(),
                });
                return;
            }
        };
        // Step 3: SExpr → Message.
        let msg = match parse_message(&sexpr) {
            Ok(m) => m,
            Err(e) => {
                self.quarantine.push(QuarantineEntry {
                    send_index: event.send_index,
                    reason: QuarantineReason::ParseError(format!("message: {e}")),
                    bytes: event.payload.clone(),
                });
                return;
            }
        };
        // Drop our own echoed sends silently (not quarantine, not ingest).
        let inner = msg.innermost_simple().unwrap_or(&msg);
        if inner.sender() == Some(self.sender_id.as_str()) {
            return;
        }
        // Step 4: extract performative + thread for verify_causal.
        let perf_name = match performative_name(inner) {
            Some(n) => n,
            None => {
                self.quarantine.push(QuarantineEntry {
                    send_index: event.send_index,
                    reason: QuarantineReason::ParseError("no performative".to_string()),
                    bytes: event.payload.clone(),
                });
                return;
            }
        };
        let thread_str = inner.thread().unwrap_or(&self.thread_root).to_string();
        let thread = ThreadId(thread_str);
        let proto = match self.dialect.causal_protocol.as_ref() {
            Some(p) => p,
            None => {
                // No protocol → trivially Valid.
                self.accept_inbound(&msg, &thread);
                self.strategy.ingest_inbound(&msg);
                return;
            }
        };
        // Step 5: verify_causal.
        let result = verify_causal(
            &perf_name,
            inner.caused_by(),
            &self.store,
            proto,
            &thread,
        );
        match result {
            VerificationResult::Valid => {
                self.accept_inbound(&msg, &thread);
                self.strategy.ingest_inbound(&msg);
            }
            VerificationResult::Violation(v) => {
                self.quarantine.push(QuarantineEntry {
                    send_index: event.send_index,
                    reason: QuarantineReason::CausalViolation(format!("{v}")),
                    bytes: event.payload.clone(),
                });
            }
            VerificationResult::Unknown => {
                self.quarantine.push(QuarantineEntry {
                    send_index: event.send_index,
                    reason: QuarantineReason::CausalUnknown,
                    bytes: event.payload.clone(),
                });
            }
        }
    }

    fn accept_inbound(&mut self, msg: &Message, thread: &ThreadId) {
        let inner = msg.innermost_simple().unwrap_or(msg);
        let hash = Self::content_hash(inner);
        let _ = self.store.append(hash, thread.clone(), msg.clone());
    }

    fn append_outbound(&mut self, msg: &Message) {
        let hash = Self::content_hash(msg);
        let _ = self.store.append(hash, self.thread_id(), msg.clone());
    }
}

/// Extract the performative name from a (possibly wrapped) message's
/// innermost simple form. Returns `None` for `Meta` messages.
pub(crate) fn performative_name(msg: &Message) -> Option<String> {
    msg.performative().map(|p| p.name().to_string())
}

impl<S> CbclAgent<S>
where
    S: ChallengeStrategy,
{
    /// Run one drain-then-emit step. The test/driver harness calls this
    /// repeatedly across all agents, interleaving turns, until every agent
    /// reports `is_done`. Returns `true` if either the strategy progressed
    /// (consumed an inbound event or emitted an outbound) or is now done.
    pub fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> StepStatus {
        let mut had_inbound = false;
        while let Some(event) = in_channel.next() {
            had_inbound = true;
            self.handle_inbound(&event);
        }
        let mut had_outbound = false;
        while let Some(draft) = self.strategy.next_outbound(rng) {
            let msg = match self.build_outbound(&draft) {
                Some(m) => m,
                None => continue,
            };
            had_outbound = true;
            self.append_outbound(&msg);
            let payload = serialize(&SExpr::from(&msg)).into_bytes();
            out_channel(ChatEvent {
                agent_idx: 0, // driver overwrites
                send_index: *send_index_seed,
                payload,
            });
            *send_index_seed = send_index_seed.saturating_add(1);
        }
        StepStatus {
            had_inbound,
            had_outbound,
            is_done: self.strategy.is_done(),
        }
    }
}

/// Result of one [`CbclAgent::step`] call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StepStatus {
    /// True if at least one inbound event was consumed.
    pub had_inbound: bool,
    /// True if at least one outbound event was emitted.
    pub had_outbound: bool,
    /// True if the strategy reports it has nothing more to do.
    pub is_done: bool,
}

impl<S> Agent for CbclAgent<S>
where
    S: ChallengeStrategy,
{
    type Setup = S::Setup;
    type ChatEvent = ChatEvent;
    type Guess = S::Guess;

    fn play(
        &mut self,
        setup: Self::Setup,
        in_channel: &mut dyn Iterator<Item = Self::ChatEvent>,
        out_channel: &mut dyn FnMut(Self::ChatEvent),
        rng: &mut dyn RngCore,
    ) -> Self::Guess {
        self.strategy.ingest_setup(setup);
        let mut send_index: u64 = 0;
        loop {
            let s = self.step(in_channel, out_channel, rng, &mut send_index);
            if s.is_done && !s.had_inbound {
                break;
            }
            if !s.had_inbound && !s.had_outbound {
                break;
            }
        }
        self.strategy.final_guess()
    }
}

/// Initialise the strategy with its setup. Exposed separately so the
/// test/driver harness can step agents in turn after a single common setup.
pub fn ingest_setup<S: ChallengeStrategy>(agent: &mut CbclAgent<S>, setup: S::Setup) {
    agent.strategy.ingest_setup(setup);
}

/// Helper: load and parse a dialect from on-disk source text.
///
/// Used by the per-challenge strategy constructors.
pub fn load_dialect(source: &str) -> Result<cbcl_core::dialect::Dialect, String> {
    let sexpr = parse(source).map_err(|e| format!("dialect parse: {e:?}"))?;
    cbcl_parser::parse_dialect(&sexpr)
}

/// Convenience helpers shared across the per-challenge strategies.
pub(crate) mod content {
    use cbcl_core::message::Message;
    use cbcl_core::sexpr::{Atom, SExpr};

    /// Build `(head :key val :key2 val2 ...)`-style content S-expression.
    pub fn keyword_form(head: &str, kwargs: &[(&str, SExpr)]) -> SExpr {
        let mut items: Vec<SExpr> = vec![SExpr::Atom(Atom::Symbol(head.to_string()))];
        for (k, v) in kwargs {
            items.push(SExpr::Atom(Atom::Keyword((*k).to_string())));
            items.push(v.clone());
        }
        SExpr::List(items)
    }

    /// Extract a keyword-positioned param from a message's content list,
    /// e.g. `(set-commitment :root <hash> :count 4)` with key `"root"`.
    pub fn get_kw<'a>(msg: &'a Message, key: &str) -> Option<&'a SExpr> {
        let content = msg.content()?;
        let SExpr::List(items) = content else {
            return None;
        };
        let mut iter = items.iter();
        // Skip the head symbol.
        let _ = iter.next()?;
        while let Some(item) = iter.next() {
            if let SExpr::Atom(Atom::Keyword(k)) = item {
                let v = iter.next()?;
                if k == key {
                    return Some(v);
                }
            }
        }
        None
    }

    /// Convert an `SExpr` to a plain `String` if it is a Str, Symbol, or
    /// Keyword atom. Useful for extracting commitments and bit values.
    pub fn as_string(e: &SExpr) -> Option<String> {
        match e {
            SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Keyword(s)) => {
                Some(s.clone())
            }
            _ => None,
        }
    }

    /// Convert an `SExpr` to a list of `String`s if it is a list of string
    /// atoms.
    pub fn as_string_list(e: &SExpr) -> Option<Vec<String>> {
        let SExpr::List(items) = e else {
            return None;
        };
        items.iter().map(as_string).collect()
    }

    /// Extract a `bool` from an SExpr atom (Bool, or 0/1 Num).
    pub fn as_bool(e: &SExpr) -> Option<bool> {
        match e {
            SExpr::Atom(Atom::Bool(b)) => Some(*b),
            SExpr::Atom(Atom::Num(n)) => match *n {
                0 => Some(false),
                1 => Some(true),
                _ => None,
            },
            _ => None,
        }
    }

}

/// Hash function exposed to per-challenge strategies for commitment
/// constructions. Same FNV-1a 128 used for content hashing — non-
/// cryptographic but deterministic and dependency-free (NFR-1112).
pub(crate) fn strategy_hash(bytes: &[u8]) -> String {
    // Inline copy of `CbclAgent::hash_bytes` (which is pinned to `Self`).
    const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
    const PRIME: u128 = 0x0000000001000000000000000000013b;
    let mut h: u128 = OFFSET;
    for &b in bytes {
        h ^= b as u128;
        h = h.wrapping_mul(PRIME);
    }
    format!("{:032x}", h)
}

#[cfg(test)]
mod tests;
