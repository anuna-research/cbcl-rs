//! CBCL-native live-LLM seat (raw s-expression emissions).
//!
//! Unlike [`super::disciplined::GlmDisciplinedSeat`] — which exposes the
//! dialect's five performatives as OpenAI-style function tools and lets a
//! shim handle all crypto/serialisation — the **native** seat asks the
//! LLM to *speak the dialect directly*: each turn, the assistant emits a
//! single CBCL s-expression as plain chat content, and the seat parses
//! and verify_causal-checks it before forwarding to the wire.
//!
//! The only auxiliary tool exposed is [`hash_element`] (SHA-256 of
//! `salt || ':' || element` → lowercase hex). Salt-and-element hashing
//! is otherwise infeasible in-context for current chat models.
//!
//! ## `latest` resolution (usability concession)
//!
//! The dialect grammar requires every non-root message to carry a
//! `:caused-by <hash>`. Computing CBCL's FNV-1a-128 content digest in-
//! context by hand is not reasonable. As a usability concession, the
//! native seat accepts the literal symbol `latest` (or, equivalently, a
//! missing `:caused-by`) in the LLM's emission and resolves it
//! server-side to the most-recent accepted message of the protocol's
//! required predecessor performative. If no such predecessor exists the
//! emission is rejected and the LLM is asked to retry.
//!
//! Hash function and canonical form match `CbclAgent` exactly — see the
//! parent module — so the cooperative `CbclAgent` peer accepts the
//! resulting messages without quarantine.

use rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

use cbcl_core::dialect::Dialect;
use cbcl_core::message::{CausedBy, Message, Performative};
use cbcl_core::protocol::{verify_causal, NodeRef, VerificationResult};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use cbcl_parser::{parse, parse_message};

use crate::agents::cbcl::QuarantineEntry;
use crate::driver::{DrivenAgent, StepStatus};
use crate::operator::psi::{PsiGuess, PsiSetup};
use crate::operator::ChatEvent;

use super::{
    append_transcript, ChatMessage, ChatRequest, FunctionDef, GlmClient, ToolCall, ToolDef,
    MODEL,
};

const NATIVE_SYSTEM_TEMPLATE: &str = "You are participant Alice in a Private Set Intersection game with another participant, Bob. Your private set is: {SET}.

You communicate ONLY by emitting CBCL s-expressions as chat messages. Free-form English does not reach Bob and will not advance the protocol. Each message you emit must be a single, syntactically valid CBCL message in the arena-psi dialect.

The protocol has five performatives in strict order:

1. psi-salt \u{2014} propose a salt:
   (psi-salt :salt \"alice-1\" :sender \"alice\" :thread \"psi-game\" :caused-by begin)

2. psi-commit \u{2014} commit to your set's Merkle root + cardinality:
   (psi-commit :root \"<hex>\" :count 4 :sender \"alice\" :thread \"psi-game\" :caused-by latest)

3. psi-reveal \u{2014} reveal the hashed leaves:
   (psi-reveal :hashes (\"<hex1>\" \"<hex2>\" \"<hex3>\" \"<hex4>\") :sender \"alice\" :thread \"psi-game\" :caused-by latest)

4. psi-claim \u{2014} claim the plaintext members you believe are in the intersection:
   (psi-claim :members (\"apple\" \"banana\") :sender \"alice\" :thread \"psi-game\" :caused-by latest)

5. psi-final \u{2014} operator-bound final answer:
   (psi-final :members (\"apple\" \"banana\") :sender \"alice\" :thread \"psi-game\" :caused-by latest)

Use the hash_element tool to compute the protocol-defined hash of (salt, element). After Bob's psi-reveal lands, hash each element of your own set with the agreed salt; the digest the tool returns is byte-identical to the entries in Bob's revealed list, so the elements whose hashes match Bob's reveals are the intersection.

The :caused-by field references the content hash of the immediate predecessor message. For the first message use `begin`. For subsequent messages, you may write the literal symbol `latest` and the runtime will resolve it to the most recent accepted message of the protocol-required predecessor type.

If your message fails to parse or violates the protocol, you'll receive an error and can retry.";

/// Maximum number of inner `hash_element` (or other tool-only) iterations
/// per [`DrivenAgent::step`] before forcing the model to commit to a
/// content emission.
const MAX_INNER_TOOL_ITERS: usize = 5;

/// CBCL-native live-LLM seat for the PSI challenge.
pub struct GlmCbclNativeSeat {
    client: GlmClient,
    transcript_path: std::path::PathBuf,
    trial: u32,
    /// Maximum LLM (outer) turns before forcing termination.
    max_turns: u32,
    /// Parsed dialect.
    dialect: Dialect,
    /// Accepted-message store. Holds both own emissions and Bob's accepted
    /// inbound, so `:caused-by` references resolve uniformly.
    store: ThreadedMessageStore,
    /// Quarantine buffer (invalid inbound + invalid LLM emissions both go
    /// here, with origin marker).
    quarantine: Vec<QuarantineEntry>,
    /// Chat history (system + user + assistant + tool messages).
    history: Vec<ChatMessage>,
    /// Outer turn counter (one per LLM call that yields content).
    turn: u32,
    /// Setup payload — kept so we can render the system prompt and
    /// derive the fallback final-guess from local knowledge.
    setup: Option<PsiSetup>,
    /// Sender id used on outbound messages (must match the seat's role).
    sender_id: String,
    /// Thread id used on outbound messages.
    thread_id: ThreadId,
    /// Done flag: once the LLM emits psi-final (or we hit max_turns).
    done: bool,
    /// Counter of LLM emissions overall (for parser-rejection rate).
    pub emit_attempts: u32,
    /// Counter of emissions that were rejected by parse / verify_causal.
    pub emit_rejections: u32,
}

impl GlmCbclNativeSeat {
    /// Construct a new CBCL-native seat.
    pub fn new(
        client: GlmClient,
        transcript_path: std::path::PathBuf,
        trial: u32,
        max_turns: u32,
        dialect: Dialect,
        thread_id: impl Into<String>,
        sender_id: impl Into<String>,
    ) -> Self {
        Self {
            client,
            transcript_path,
            trial,
            max_turns,
            dialect,
            store: ThreadedMessageStore::new(),
            quarantine: Vec::new(),
            history: Vec::new(),
            turn: 0,
            setup: None,
            sender_id: sender_id.into(),
            thread_id: ThreadId(thread_id.into()),
            done: false,
            emit_attempts: 0,
            emit_rejections: 0,
        }
    }

    fn build_system_prompt(set: &[String]) -> String {
        let joined = set.join(", ");
        NATIVE_SYSTEM_TEMPLATE.replace("{SET}", &joined)
    }

    fn tools() -> Vec<ToolDef> {
        vec![ToolDef {
            kind: "function".into(),
            function: FunctionDef {
                name: "hash_element".into(),
                description: "Compute the protocol-defined hash of (salt, element). Returns lowercase hex. The output is byte-identical to the digests Bob places in psi-reveal, so you can hash each of your own set elements with the agreed salt and check which ones appear in Bob's revealed list. The matching elements are the intersection.".into(),
                parameters: serde_json::json!({
                    "type":"object",
                    "properties": {
                        "salt": {"type":"string"},
                        "element": {"type":"string"}
                    },
                    "required":["salt","element"],
                }),
            },
        }]
    }

    fn call_all(&mut self) -> Result<(Vec<ToolCall>, Option<String>), String> {
        let req = ChatRequest {
            model: MODEL.to_string(),
            messages: self.history.clone(),
            tools: Some(Self::tools()),
            tool_choice: Some("auto".into()),
            max_tokens: 4096,
            temperature: 0.0,
        };
        let (resp, raw) = self.client.chat(&req)?;
        let _ = append_transcript(
            &self.transcript_path,
            self.trial,
            self.turn,
            &req,
            &raw,
        );
        let choice = match resp.choices.first() {
            Some(c) => c.clone(),
            None => return Ok((Vec::new(), None)),
        };
        let content = choice.message.content.clone();
        let tool_calls = choice.message.tool_calls.clone().unwrap_or_default();
        let msg = ChatMessage {
            role: "assistant".into(),
            content: content.clone(),
            tool_calls: choice.message.tool_calls.clone(),
            tool_call_id: None,
        };
        self.history.push(msg);
        Ok((tool_calls, content))
    }

    fn tool_ack(&mut self, tool_call_id: &str, body: &str) {
        self.history.push(ChatMessage::tool(tool_call_id, body));
    }

    fn system_feedback(&mut self, body: &str) {
        // Use a `user`-role feedback turn — that's what GLM-5.1 reliably
        // attends to mid-stream (system messages must precede the dialog).
        self.history.push(ChatMessage::user(body));
    }

    /// 128-bit FNV-1a digest matching `CbclAgent::hash_bytes`. Hex-prefixed
    /// with `h` so it round-trips through the CBCL parser as a symbol.
    fn fnv1a_hash_bytes(bytes: &[u8]) -> String {
        const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
        const PRIME: u128 = 0x0000000001000000000000000000013b;
        let mut h: u128 = OFFSET;
        for &b in bytes {
            h ^= b as u128;
            h = h.wrapping_mul(PRIME);
        }
        format!("h{:032x}", h)
    }

    /// Content hash of a Message — same canonical form as `CbclAgent`.
    fn content_hash(msg: &Message) -> ContentHash {
        let s = serialize(&SExpr::from(msg));
        ContentHash(Self::fnv1a_hash_bytes(s.as_bytes()))
    }

    /// Find the hash of the most-recent accepted message in `thread` whose
    /// performative is `name`. Mirrors `CbclAgent::latest_hash_of`.
    fn latest_hash_of(&self, name: &str) -> Option<ContentHash> {
        let frontier: Vec<ContentHash> = self
            .store
            .frontier(&self.thread_id)
            .into_iter()
            .cloned()
            .collect();
        for h in &frontier {
            if let Some(m) = self.store.lookup_in_thread(h, &self.thread_id) {
                let inner = m.innermost_simple().unwrap_or(m);
                if inner.performative().map(|p| p.name()) == Some(name) {
                    return Some(h.clone());
                }
            }
        }
        for leaf in &frontier {
            for h in self.store.causal_closure(leaf, &self.thread_id) {
                if let Some(m) = self.store.lookup_in_thread(&h, &self.thread_id) {
                    let inner = m.innermost_simple().unwrap_or(m);
                    if inner.performative().map(|p| p.name()) == Some(name) {
                        return Some(h);
                    }
                }
            }
        }
        None
    }

    /// Predecessor performative under the dialect's protocol for the given
    /// performative — picks the first single-predecessor entry that isn't
    /// `begin`. Returns `None` if no protocol or no non-begin predecessor.
    fn protocol_predecessor(&self, name: &str) -> Option<String> {
        let proto = self.dialect.causal_protocol.as_ref()?;
        let step = proto.steps.get(name)?;
        for nr in &step.predecessors {
            match nr {
                NodeRef::Single(s) if s != "begin" => return Some(s.clone()),
                NodeRef::Any(set) => {
                    for s in set {
                        if s != "begin" {
                            return Some(s.clone());
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// True if `begin` is a permitted predecessor for `name` under the dialect.
    fn protocol_allows_begin(&self, name: &str) -> bool {
        let proto = match self.dialect.causal_protocol.as_ref() {
            Some(p) => p,
            None => return true,
        };
        let step = match proto.steps.get(name) {
            Some(s) => s,
            None => return true, // not protocol-constrained
        };
        if step.predecessors.is_empty() {
            return true;
        }
        for nr in &step.predecessors {
            match nr {
                NodeRef::Single(s) if s == "begin" => return true,
                NodeRef::Any(set) if set.contains("begin") => return true,
                _ => {}
            }
        }
        false
    }

    /// Drain inbound. Each event is parsed + verify_causal-checked; valid
    /// peer messages enter our store and are surfaced to the LLM as a
    /// "Bob emitted: <sexpr>" user-turn. Invalid inbound is quarantined
    /// and surfaced as "Bob emitted INVALID: <reason>".
    fn drain_inbound(&mut self, in_channel: &mut dyn Iterator<Item = ChatEvent>) -> bool {
        let mut had_inbound = false;
        let mut feedback_lines: Vec<String> = Vec::new();
        // Materialise events so we can mutate self while iterating.
        let events: Vec<ChatEvent> = in_channel.collect();
        for event in events {
            had_inbound = true;
            let text = match core::str::from_utf8(&event.payload) {
                Ok(t) => t.to_string(),
                Err(e) => {
                    feedback_lines.push(format!("Bob emitted INVALID (non-utf8): {e}"));
                    self.quarantine.push(QuarantineEntry {
                        send_index: event.send_index,
                        reason:
                            crate::agents::cbcl::QuarantineReason::ParseError(format!("non-utf8: {e}")),
                        bytes: event.payload.clone(),
                    });
                    continue;
                }
            };
            let sexpr = match parse(&text) {
                Ok(s) => s,
                Err(e) => {
                    feedback_lines.push(format!("Bob emitted INVALID (parse error): {e:?}"));
                    self.quarantine.push(QuarantineEntry {
                        send_index: event.send_index,
                        reason: crate::agents::cbcl::QuarantineReason::ParseError(format!(
                            "sexpr: {e:?}"
                        )),
                        bytes: event.payload.clone(),
                    });
                    continue;
                }
            };
            let msg = match parse_message(&sexpr) {
                Ok(m) => m,
                Err(e) => {
                    feedback_lines.push(format!("Bob emitted INVALID (message error): {e}"));
                    self.quarantine.push(QuarantineEntry {
                        send_index: event.send_index,
                        reason: crate::agents::cbcl::QuarantineReason::ParseError(format!(
                            "message: {e}"
                        )),
                        bytes: event.payload.clone(),
                    });
                    continue;
                }
            };
            let inner = msg.innermost_simple().unwrap_or(&msg).clone();
            // Skip our own echoed sends (driver may echo back).
            if inner.sender() == Some(self.sender_id.as_str()) {
                continue;
            }
            let perf_name = match inner.performative() {
                Some(p) => p.name().to_string(),
                None => {
                    feedback_lines.push("Bob emitted INVALID (no performative)".to_string());
                    continue;
                }
            };
            let thread = match inner.thread() {
                Some(t) => ThreadId(t.to_string()),
                None => self.thread_id.clone(),
            };
            let result = match self.dialect.causal_protocol.as_ref() {
                Some(proto) => verify_causal(
                    &perf_name,
                    inner.caused_by(),
                    &self.store,
                    proto,
                    &thread,
                ),
                None => VerificationResult::Valid,
            };
            match result {
                VerificationResult::Valid => {
                    let hash = Self::content_hash(&inner);
                    let _ = self.store.append(hash, thread.clone(), msg.clone());
                    feedback_lines.push(format!("Bob emitted: {}", text.trim()));
                }
                VerificationResult::Violation(v) => {
                    feedback_lines.push(format!(
                        "Bob emitted INVALID (causal violation: {v})"
                    ));
                    self.quarantine.push(QuarantineEntry {
                        send_index: event.send_index,
                        reason: crate::agents::cbcl::QuarantineReason::CausalViolation(format!(
                            "{v}"
                        )),
                        bytes: event.payload.clone(),
                    });
                }
                VerificationResult::Unknown => {
                    feedback_lines.push(
                        "Bob emitted INVALID (causal predecessor unknown to me)".to_string(),
                    );
                    self.quarantine.push(QuarantineEntry {
                        send_index: event.send_index,
                        reason: crate::agents::cbcl::QuarantineReason::CausalUnknown,
                        bytes: event.payload.clone(),
                    });
                }
            }
        }
        if !feedback_lines.is_empty() {
            self.history.push(ChatMessage::user(&feedback_lines.join("\n")));
        }
        had_inbound
    }

    /// Try to interpret the assistant's content as an outbound CBCL emission
    /// and (on success) emit it on the wire. Returns true iff an emission
    /// was sent.
    fn try_emit_assistant(
        &mut self,
        content: &str,
        out_channel: &mut dyn FnMut(ChatEvent),
        send_index_seed: &mut u64,
    ) -> bool {
        self.emit_attempts = self.emit_attempts.saturating_add(1);
        let trimmed = content.trim();
        if trimmed.is_empty() {
            self.emit_rejections = self.emit_rejections.saturating_add(1);
            self.system_feedback(
                "PARSE ERROR: assistant content was empty. Emit a single CBCL s-expression.",
            );
            return false;
        }
        // Some models wrap output in code fences; strip them defensively.
        let stripped = strip_code_fences(trimmed);
        let sexpr = match parse(stripped) {
            Ok(s) => s,
            Err(e) => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback(&format!(
                    "PARSE ERROR: {e:?}. Retry with a single valid CBCL s-expression (no prose, no markdown)."
                ));
                return false;
            }
        };
        let parsed_msg = match parse_message(&sexpr) {
            Ok(m) => m,
            Err(e) => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback(&format!(
                    "MESSAGE ERROR: {e}. Retry."
                ));
                return false;
            }
        };
        // Project to the innermost simple form (defensive).
        let inner = parsed_msg.innermost_simple().unwrap_or(&parsed_msg).clone();
        let perf_name = match inner.performative() {
            Some(p) => p.name().to_string(),
            None => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback("MESSAGE ERROR: missing performative. Retry.");
                return false;
            }
        };
        // Validate this is one of the dialect's performatives.
        if !self
            .dialect
            .performatives
            .iter()
            .any(|p| p.name == perf_name)
        {
            self.emit_rejections = self.emit_rejections.saturating_add(1);
            self.system_feedback(&format!(
                "DIALECT ERROR: performative `{perf_name}` is not in the arena-psi dialect. Use one of: psi-salt, psi-commit, psi-reveal, psi-claim, psi-final."
            ));
            return false;
        }

        // Resolve `latest` (or missing) :caused-by → the actual predecessor hash.
        let resolved_cb = match self.resolve_caused_by(&inner, &perf_name) {
            Ok(cb) => cb,
            Err(reason) => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback(&format!("CAUSAL ERROR: {reason}. Retry."));
                return false;
            }
        };

        // Rebuild the message in canonical form: the LLM's natural style is
        // keyword-on-the-message; the existing `CbclAgent` peer expects the
        // dialect-native form `(perf @peer (head :k v ...) :thread ... :sender ... :caused-by ...)`.
        // We construct that here so the peer's strategy can read its fields.
        let canonical = self.canonicalise_message(&inner, &perf_name, resolved_cb.clone());

        // Verify causal against the dialect protocol.
        let proto = match self.dialect.causal_protocol.as_ref() {
            Some(p) => p,
            None => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback(
                    "INTERNAL: dialect has no protocol; cannot verify. Aborting emission.",
                );
                return false;
            }
        };
        let result = verify_causal(
            &perf_name,
            canonical.caused_by(),
            &self.store,
            proto,
            &self.thread_id,
        );
        match result {
            VerificationResult::Valid => {}
            VerificationResult::Violation(v) => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback(&format!(
                    "PROTOCOL VIOLATION: {v}. Retry with a valid predecessor."
                ));
                return false;
            }
            VerificationResult::Unknown => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback(
                    "PROTOCOL UNKNOWN: predecessor not yet in my store. Use `:caused-by latest` or wait for Bob.",
                );
                return false;
            }
        }
        // Append to local store and emit on the wire.
        let hash = Self::content_hash(&canonical);
        let _ = self
            .store
            .append(hash, self.thread_id.clone(), canonical.clone());
        let payload = serialize(&SExpr::from(&canonical));
        let send_index = *send_index_seed;
        *send_index_seed = send_index_seed.saturating_add(1);
        out_channel(ChatEvent {
            agent_idx: 0,
            send_index,
            payload: payload.into_bytes(),
        });
        // Tell the LLM what was actually sent (so its history reflects the
        // canonical form, not its own draft).
        self.history.push(ChatMessage::user(&format!(
            "Alice emitted (canonical): {payload}",
            payload = serialize(&SExpr::from(&canonical))
        )));
        // psi-final ends the protocol.
        if perf_name == "psi-final" {
            self.done = true;
        }
        true
    }

    /// Resolve the LLM's `:caused-by` (which may be `latest` or absent) to
    /// a concrete `CausedBy`. `Begin` is passed through.
    fn resolve_caused_by(
        &self,
        msg: &Message,
        perf_name: &str,
    ) -> Result<CausedBy, String> {
        let cb = msg.caused_by();
        let needs_resolve = match cb {
            None => true,
            Some(CausedBy::Single(s)) if s == "latest" => true,
            _ => false,
        };
        if !needs_resolve {
            return Ok(cb.cloned().unwrap_or(CausedBy::Begin));
        }
        // Resolve: protocol predecessor for this performative.
        let pred_perf = match self.protocol_predecessor(perf_name) {
            Some(p) => p,
            None => {
                if self.protocol_allows_begin(perf_name) {
                    return Ok(CausedBy::Begin);
                }
                return Err(format!(
                    "no protocol predecessor declared for `{perf_name}`"
                ));
            }
        };
        match self.latest_hash_of(&pred_perf) {
            Some(h) => Ok(CausedBy::Single(h.0)),
            None => {
                if self.protocol_allows_begin(perf_name) {
                    Ok(CausedBy::Begin)
                } else {
                    Err(format!(
                        "no accepted `{pred_perf}` message in the store; cannot resolve `latest`"
                    ))
                }
            }
        }
    }

    /// Translate the LLM's keyword-on-message form (e.g. `(psi-salt :salt
    /// "..." :sender ... :thread ... :caused-by ...)`) into the canonical
    /// dialect form expected by the cooperative `CbclAgent` peer:
    ///   `(psi-salt @peer (salt-proposal :salt "...") :thread ... :sender ... :caused-by ...)`
    /// Other performatives map analogously. The LLM may also produce the
    /// dialect-native form directly — `(psi-commit @peer (set-commitment
    /// :root "..." :count 4) ...)` — in which case the LLM-supplied
    /// content list is forwarded verbatim.
    fn canonicalise_message(
        &self,
        inner: &Message,
        perf_name: &str,
        caused_by: CausedBy,
    ) -> Message {
        // Collect top-level keyword params from the parsed message.
        let kw: BTreeMap<String, SExpr> = match inner {
            Message::Simple { params, .. } => keywords_from_params(params),
            _ => BTreeMap::new(),
        };
        // If the LLM emitted dialect-native form (content is a non-empty list
        // headed by a symbol other than the performative name), forward it.
        let llm_content = inner.content().cloned();
        let dialect_content = match &llm_content {
            Some(SExpr::List(items)) if !items.is_empty() => match &items[0] {
                SExpr::Atom(Atom::Symbol(head))
                    if head == "salt-proposal"
                        || head == "set-commitment"
                        || head == "hash-reveal"
                        || head == "intersection-claim"
                        || head == "intersection-answer" =>
                {
                    Some(llm_content.clone().unwrap())
                }
                _ => None,
            },
            _ => None,
        };
        let content: SExpr = if let Some(c) = dialect_content {
            c
        } else {
            match perf_name {
                "psi-salt" => {
                    let salt = kw
                        .get("salt")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Str("".into())));
                    kw_form("salt-proposal", &[("salt", salt)])
                }
                "psi-commit" => {
                    let root = kw
                        .get("root")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Str("".into())));
                    let count = kw
                        .get("count")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Num(0)));
                    kw_form("set-commitment", &[("root", root), ("count", count)])
                }
                "psi-reveal" => {
                    let hashes = kw
                        .get("hashes")
                        .cloned()
                        .unwrap_or_else(|| SExpr::List(Vec::new()));
                    kw_form("hash-reveal", &[("hashes", hashes)])
                }
                "psi-claim" => {
                    let members = kw
                        .get("members")
                        .cloned()
                        .unwrap_or_else(|| SExpr::List(Vec::new()));
                    kw_form("intersection-claim", &[("members", members)])
                }
                "psi-final" => {
                    let members = kw
                        .get("members")
                        .cloned()
                        .unwrap_or_else(|| SExpr::List(Vec::new()));
                    kw_form("intersection-answer", &[("members", members)])
                }
                other => llm_content
                    .unwrap_or_else(|| SExpr::Atom(Atom::Symbol(other.to_string()))),
            }
        };

        // Recipient: psi-final → @operator, others → @peer (per dialect).
        let recipient = match perf_name {
            "psi-final" => Some("@operator".to_string()),
            _ => Some("@peer".to_string()),
        };

        Message::Simple {
            performative: Performative::Custom(perf_name.to_string()),
            recipient,
            content,
            params: Vec::new(),
            thread: Some(self.thread_id.0.clone()),
            sender: Some(self.sender_id.clone()),
            caused_by: Some(caused_by),
        }
    }
}

/// Strip ```cbcl ... ``` or ``` ... ``` fences from an LLM emission.
fn strip_code_fences(s: &str) -> &str {
    let s = s.trim();
    if !s.starts_with("```") {
        return s;
    }
    // Find first newline (after ``` or ```cbcl etc.)
    let after_open = match s.find('\n') {
        Some(i) => &s[i + 1..],
        None => return s,
    };
    if let Some(end) = after_open.rfind("```") {
        after_open[..end].trim()
    } else {
        after_open
    }
}

/// Turn `[Keyword(k), v, Keyword(k2), v2, ...]` into a map.
fn keywords_from_params(params: &[SExpr]) -> BTreeMap<String, SExpr> {
    let mut out = BTreeMap::new();
    let mut i = 0;
    while i + 1 < params.len() {
        if let SExpr::Atom(Atom::Keyword(k)) = &params[i] {
            out.insert(k.clone(), params[i + 1].clone());
            i += 2;
        } else {
            i += 1;
        }
    }
    out
}

/// Build `(head :k1 v1 :k2 v2 ...)`.
fn kw_form(head: &str, kvs: &[(&str, SExpr)]) -> SExpr {
    let mut items: Vec<SExpr> = vec![SExpr::Atom(Atom::Symbol(head.to_string()))];
    for (k, v) in kvs {
        items.push(SExpr::Atom(Atom::Keyword((*k).to_string())));
        items.push(v.clone());
    }
    SExpr::List(items)
}

/// FNV-1a-128 over `(salt-bytes || 0x00 || elem-bytes)`, formatted as
/// 32-char lowercase hex (no prefix). Matches Bob's
/// `PsiCbclStrategy::salt_hash` byte-for-byte.
fn protocol_hash(salt: &str, elem: &str) -> String {
    const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
    const PRIME: u128 = 0x0000000001000000000000000000013b;
    let mut h: u128 = OFFSET;
    for &b in salt.as_bytes() {
        h ^= b as u128;
        h = h.wrapping_mul(PRIME);
    }
    h ^= 0u128;
    h = h.wrapping_mul(PRIME);
    for &b in elem.as_bytes() {
        h ^= b as u128;
        h = h.wrapping_mul(PRIME);
    }
    format!("{:032x}", h)
}

/// SHA-256 hex (lowercase) of `data`.
#[allow(dead_code)]
fn sha256_hex(data: &str) -> String {
    let mut h = Sha256::new();
    h.update(data.as_bytes());
    let out = h.finalize();
    let mut hex = String::with_capacity(64);
    for b in out {
        hex.push_str(&format!("{:02x}", b));
    }
    hex
}

impl DrivenAgent for GlmCbclNativeSeat {
    type Setup = PsiSetup;
    type Guess = PsiGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        let prompt = Self::build_system_prompt(&setup.set);
        self.history.push(ChatMessage::system(&prompt));
        self.setup = Some(setup);
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        _rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> StepStatus {
        let had_inbound = self.drain_inbound(in_channel);
        if self.done {
            return StepStatus {
                had_inbound,
                had_outbound: false,
                is_done: true,
            };
        }
        // Kick the model: if no inbound and no recent prompt, give a brief
        // system-style nudge (only on turn 0).
        if !had_inbound && self.turn == 0 && self.history.len() == 1 {
            self.history.push(ChatMessage::user(
                "Bob has connected. Begin the protocol by emitting a psi-salt s-expression.",
            ));
        }

        let mut had_outbound = false;
        // Inner loop: handle hash_element tool calls until the assistant
        // produces text content (which we try to interpret as an emission).
        for _ in 0..MAX_INNER_TOOL_ITERS {
            let (tool_calls, content) = match self.call_all() {
                Ok(v) => v,
                Err(e) => {
                    eprintln!(
                        "[glm/cbcl_native] trial {} turn {}: {}",
                        self.trial, self.turn, e
                    );
                    self.done = true;
                    return StepStatus {
                        had_inbound,
                        had_outbound,
                        is_done: true,
                    };
                }
            };
            self.turn = self.turn.saturating_add(1);
            if !tool_calls.is_empty() {
                // Ack every tool call. hash_element calls are executed; any
                // other tool name is rejected (the native seat exposes only
                // hash_element).
                for tc in tool_calls.into_iter() {
                    if tc.function.name == "hash_element" {
                        let args: serde_json::Value =
                            serde_json::from_str(&tc.function.arguments)
                                .unwrap_or(serde_json::Value::Null);
                        let salt = args
                            .get("salt")
                            .and_then(|v| v.as_str())
                            .unwrap_or("")
                            .to_string();
                        let element = args
                            .get("element")
                            .and_then(|v| v.as_str())
                            .unwrap_or("")
                            .to_string();
                        // Use `protocol_hash` — the unprefixed FNV-1a-128 form
                        // that matches Bob's `PsiCbclStrategy::salt_hash`.
                        // (`Self::fnv1a_hash_bytes` adds an `h` prefix used
                        // for caused-by content hashes; we must NOT use that
                        // here, or the digests won't match psi-reveal entries.)
                        let digest = protocol_hash(&salt, &element);
                        self.tool_ack(&tc.id, &digest);
                    } else {
                        self.tool_ack(
                            &tc.id,
                            &format!(
                                "ignored: tool `{}` is not exposed by the native seat. Emit CBCL s-expressions as chat content instead.",
                                tc.function.name
                            ),
                        );
                    }
                }
                if self.turn >= self.max_turns {
                    self.done = true;
                    break;
                }
                continue;
            }
            // No tool call: try to interpret the content as a CBCL emission.
            let body = content.unwrap_or_default();
            had_outbound =
                self.try_emit_assistant(&body, out_channel, send_index_seed) || had_outbound;
            break;
        }

        if self.turn >= self.max_turns {
            self.done = true;
        }
        StepStatus {
            had_inbound,
            had_outbound,
            is_done: self.done,
        }
    }

    fn final_guess(&self) -> Self::Guess {
        // Scan our own emissions in store: prefer most-recent psi-final's
        // members, fall back to most-recent psi-claim's members.
        for perf in &["psi-final", "psi-claim"] {
            if let Some(h) = self.latest_hash_of(perf) {
                if let Some(m) = self.store.lookup_in_thread(&h, &self.thread_id) {
                    let inner = m.innermost_simple().unwrap_or(m);
                    if let Some(SExpr::List(items)) = inner.content() {
                        // canonical content is `(intersection-{claim,answer} :members (...))`
                        let mut iter = items.iter();
                        let _ = iter.next(); // head
                        while let Some(item) = iter.next() {
                            if let SExpr::Atom(Atom::Keyword(k)) = item {
                                if let Some(v) = iter.next() {
                                    if k == "members" {
                                        if let SExpr::List(elems) = v {
                                            return elems
                                                .iter()
                                                .filter_map(|e| match e {
                                                    SExpr::Atom(Atom::Str(s))
                                                    | SExpr::Atom(Atom::Symbol(s)) => Some(s.clone()),
                                                    _ => None,
                                                })
                                                .collect();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Vec::new()
    }
}

impl GlmCbclNativeSeat {
    /// Read-only view of the quarantine list (for logging / metrics).
    pub fn quarantine(&self) -> &[QuarantineEntry] {
        &self.quarantine
    }
}
