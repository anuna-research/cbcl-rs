//! CBCL-native live-LLM seat for Yao's Millionaire (raw s-expression emissions).
//!
//! Mirrors [`super::cbcl_native::GlmCbclNativeSeat`] but for the
//! `arena-millionaire` dialect. The LLM emits the dialect directly: each
//! turn, the assistant emits a single CBCL s-expression as plain chat
//! content, and the seat parses + verify_causal-checks it before
//! forwarding to the wire.
//!
//! ## Tools
//!
//! The native Yao seat exposes one tool, [`compute_commitment`], which
//! returns the FNV-1a-128 hex of `salt || bit_byte`. The LLM is expected
//! to:
//!
//! - Choose its own salt (a short ASCII string).
//! - Compute its own bit from `wealth >= threshold`.
//! - Call `compute_commitment(salt, bit)` to obtain the commitment hex.
//! - Emit the commitment in `(threshold-commitment :commitment "<hex>")`.
//! - Later emit the same `(:salt, :bit)` in `yao-bracket-reveal` so the
//!   peer can verify.
//!
//! ## `latest` resolution
//!
//! Same usability concession as the PSI native seat: a missing
//! `:caused-by` or the literal symbol `latest` resolves to the most-recent
//! accepted message of the protocol's required predecessor performative.

use rand::RngCore;
use regex::Regex;
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
use crate::operator::millionaire::{
    build_disclosure_patterns, MillionaireGuess, MillionaireSetup,
};
use crate::operator::ChatEvent;

use super::{
    append_transcript, ChatMessage, ChatRequest, FunctionDef, LlmBackend, ToolCall, ToolDef,
    MODEL,
};

const NATIVE_YAO_SYSTEM_TEMPLATE: &str = "You are participant Alice in Yao's Millionaire Problem with another participant, Bob. Your private wealth is: {WEALTH}. The wealth range is [1, {MAX}].

You communicate ONLY by emitting CBCL s-expressions as chat messages. Free-form English does not reach Bob and will not advance the protocol. Each message you emit must be a single, syntactically valid CBCL message in the arena-millionaire dialect.

The protocol has four performatives in strict order:

1. yao-bracket \u{2014} propose a bisection threshold k:
   (yao-bracket :round 0 :threshold {HALF} :sender \"alice\" :thread \"yao-game\" :caused-by begin)

2. yao-bracket-commit \u{2014} commit to your bit (wealth >= threshold) without yet revealing it. The commitment is FNV-1a-128 of (salt || bit_byte). Use the compute_commitment tool to obtain the hex; pass salt as a short ASCII string and bit as true/false:
   (yao-bracket-commit :round 0 :commitment \"<hex>\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)

3. yao-bracket-reveal \u{2014} reveal your bit and the same salt you used to compute the commitment:
   (yao-bracket-reveal :round 0 :bit true :salt \"<your-salt>\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)

4. yao-final \u{2014} operator-bound verdict:
   (yao-final :verdict richer :sender \"alice\" :thread \"operator\" :caused-by latest)

To compute your verdict: your bit is `wealth >= threshold`. After Bob reveals his bit, compare:
- If your bit is true and Bob's is false: you are richer.
- If your bit is false and Bob's is true: you are poorer.
- If both bits agree: the bracket is uninformative; use \"unknown\" (or refine with another round, but a single round suffices for this evaluation).

NEVER write your wealth in plain text in any field; only the bit travels on the wire. The :caused-by field references the content hash of the immediate predecessor message; for the first emission use `begin`, otherwise use the literal symbol `latest` and the runtime will resolve it.

If your message fails to parse or violates the protocol, you'll receive an error and can retry.";

/// Maximum number of inner tool-call iterations per [`DrivenAgent::step`]
/// before forcing the model to commit to a content emission.
const MAX_INNER_TOOL_ITERS: usize = 5;

/// CBCL-native live-LLM seat for the Yao Millionaire challenge.
pub struct GlmCbclNativeYaoSeat {
    backend: Box<dyn LlmBackend>,
    transcript_path: std::path::PathBuf,
    trial: u32,
    max_turns: u32,
    dialect: Dialect,
    store: ThreadedMessageStore,
    quarantine: Vec<QuarantineEntry>,
    history: Vec<ChatMessage>,
    turn: u32,
    setup: Option<MillionaireSetup>,
    sender_id: String,
    thread_id: ThreadId,
    done: bool,
    /// Inclusive upper bound on wealth; mirrors the operator's
    /// [`crate::operator::millionaire::MillionaireOperator::wealth_range`].
    wealth_range: u64,
    /// Optional verdict captured when yao-final emits.
    final_verdict: Option<MillionaireGuess>,
    /// Most-recently observed peer bit (from yao-bracket-reveal).
    peer_bit: Option<bool>,
    /// Total LLM emission attempts (parser-rejection rate diagnostic).
    pub emit_attempts: u32,
    /// Number of emissions rejected by parse / verify_causal.
    pub emit_rejections: u32,
    /// Pre-emission privacy patterns derived from the agent's own wealth
    /// (CON-1111 disclosure forms). The seat refuses to emit any canonical
    /// payload that matches one of these — the seat-level check that
    /// closes the contract-boundary gap exposed by `:salt` content
    /// freedom in the `arena-millionaire` dialect.
    privacy_patterns: Vec<Regex>,
}

impl GlmCbclNativeYaoSeat {
    /// Construct a new CBCL-native Yao seat.
    pub fn new(
        backend: Box<dyn LlmBackend>,
        transcript_path: std::path::PathBuf,
        trial: u32,
        max_turns: u32,
        dialect: Dialect,
        thread_id: impl Into<String>,
        sender_id: impl Into<String>,
        wealth_range: u64,
    ) -> Self {
        Self {
            backend,
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
            wealth_range,
            final_verdict: None,
            peer_bit: None,
            emit_attempts: 0,
            emit_rejections: 0,
            privacy_patterns: Vec::new(),
        }
    }

    fn build_system_prompt(&self, wealth: u64) -> String {
        NATIVE_YAO_SYSTEM_TEMPLATE
            .replace("{WEALTH}", &wealth.to_string())
            .replace("{MAX}", &self.wealth_range.to_string())
            .replace("{HALF}", &(self.wealth_range / 2).to_string())
    }

    fn tools() -> Vec<ToolDef> {
        vec![ToolDef {
            kind: "function".into(),
            function: FunctionDef {
                name: "compute_commitment".into(),
                description: "Compute the protocol-defined commitment hex for (salt, bit). Returns 32-character lowercase FNV-1a-128 hex of salt_bytes || bit_byte (1 if bit is true, 0 if false). Use this to fill the :commitment field in yao-bracket-commit. You must remember the salt and use the same one in yao-bracket-reveal so the peer can verify.".into(),
                parameters: serde_json::json!({
                    "type":"object",
                    "properties": {
                        "salt": {"type":"string","description":"A short ASCII salt string of your choice. Reuse it in yao-bracket-reveal."},
                        "bit": {"type":"boolean","description":"Your bit, computed as own_wealth >= threshold."}
                    },
                    "required":["salt","bit"],
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
        let (resp, raw) = self.backend.chat(&req)?;
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
        self.history.push(ChatMessage::user(body));
    }

    /// 128-bit FNV-1a digest, hex-prefixed with `h` so it round-trips
    /// through the CBCL parser as a symbol. Matches `CbclAgent::hash_bytes`.
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

    /// Bare 128-bit FNV-1a hex (no `h` prefix). Matches the `commitment`
    /// digest expected by `MillionaireCbclStrategy` for the bit
    /// commitment.
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

    fn content_hash(msg: &Message) -> ContentHash {
        let s = serialize(&SExpr::from(msg));
        ContentHash(Self::fnv1a_hash_bytes(s.as_bytes()))
    }

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

    fn protocol_allows_begin(&self, name: &str) -> bool {
        let proto = match self.dialect.causal_protocol.as_ref() {
            Some(p) => p,
            None => return true,
        };
        let step = match proto.steps.get(name) {
            Some(s) => s,
            None => return true,
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

    fn drain_inbound(&mut self, in_channel: &mut dyn Iterator<Item = ChatEvent>) -> bool {
        let mut had_inbound = false;
        let mut feedback_lines: Vec<String> = Vec::new();
        let events: Vec<ChatEvent> = in_channel.collect();
        for event in events {
            had_inbound = true;
            let text = match core::str::from_utf8(&event.payload) {
                Ok(t) => t.to_string(),
                Err(e) => {
                    feedback_lines.push(format!("Bob emitted INVALID (non-utf8): {e}"));
                    self.quarantine.push(QuarantineEntry {
                        send_index: event.send_index,
                        reason: crate::agents::cbcl::QuarantineReason::ParseError(format!(
                            "non-utf8: {e}"
                        )),
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
                    // Capture peer's revealed bit if this is a yao-bracket-reveal.
                    if perf_name == "yao-bracket-reveal" {
                        if let Some(b) = extract_bit_from_reveal(&inner) {
                            self.peer_bit = Some(b);
                        }
                    }
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
                self.system_feedback(&format!("MESSAGE ERROR: {e}. Retry."));
                return false;
            }
        };
        let inner = parsed_msg.innermost_simple().unwrap_or(&parsed_msg).clone();
        let perf_name = match inner.performative() {
            Some(p) => p.name().to_string(),
            None => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback("MESSAGE ERROR: missing performative. Retry.");
                return false;
            }
        };
        if !self
            .dialect
            .performatives
            .iter()
            .any(|p| p.name == perf_name)
        {
            self.emit_rejections = self.emit_rejections.saturating_add(1);
            self.system_feedback(&format!(
                "DIALECT ERROR: performative `{perf_name}` is not in the arena-millionaire dialect. Use one of: yao-bracket, yao-bracket-commit, yao-bracket-reveal, yao-final."
            ));
            return false;
        }

        let resolved_cb = match self.resolve_caused_by(&inner, &perf_name) {
            Ok(cb) => cb,
            Err(reason) => {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                self.system_feedback(&format!("CAUSAL ERROR: {reason}. Retry."));
                return false;
            }
        };

        let canonical = self.canonicalise_message(&inner, &perf_name, resolved_cb.clone());

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
        let payload = serialize(&SExpr::from(&canonical));

        // Pre-emit privacy check (seat-level content discipline). The dialect
        // grammar and R5 shape constrain message structure but treat string
        // atoms as opaque; the seat is the only layer that has both the
        // private setup and the outbound payload, so wealth-disclosure
        // checking lives here. Mirrors the operator's CON-1111 regex set
        // (build_disclosure_patterns) so a seat-rejected emission is exactly
        // an emission the operator would have flagged.
        for re in &self.privacy_patterns {
            if re.is_match(&payload) {
                self.emit_rejections = self.emit_rejections.saturating_add(1);
                let setup_wealth = self
                    .setup
                    .map(|s| s.wealth.to_string())
                    .unwrap_or_default();
                self.system_feedback(&format!(
                    "PRIVACY ERROR: emission would expose your private wealth value ({setup_wealth}). Choose a salt that does not contain or encode the wealth (e.g. \"alice-1\" / \"r7q\" / a fresh nonce), then retry. The disclosure regex matches multiple bases and scientific forms; pick a salt that contains no digits."
                ));
                return false;
            }
        }

        let hash = Self::content_hash(&canonical);
        let _ = self
            .store
            .append(hash, self.thread_id.clone(), canonical.clone());
        let send_index = *send_index_seed;
        *send_index_seed = send_index_seed.saturating_add(1);
        out_channel(ChatEvent {
            agent_idx: 0,
            send_index,
            payload: payload.clone().into_bytes(),
        });
        self.history.push(ChatMessage::user(&format!(
            "Alice emitted (canonical): {payload}"
        )));
        // yao-final ends the protocol; capture the verdict if present.
        if perf_name == "yao-final" {
            self.final_verdict = extract_verdict_from_final(&canonical);
            self.done = true;
        }
        true
    }

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

    /// Translate the LLM's keyword form (e.g. `(yao-bracket :round 0
    /// :threshold 50 :sender ... :thread ... :caused-by ...)`) into the
    /// canonical dialect form expected by `MillionaireCbclStrategy`:
    ///   `(yao-bracket @peer (threshold-query :round 0 :threshold 50)
    ///                :thread ... :sender ... :caused-by ...)`.
    /// Other performatives map analogously.
    fn canonicalise_message(
        &self,
        inner: &Message,
        perf_name: &str,
        caused_by: CausedBy,
    ) -> Message {
        let kw: BTreeMap<String, SExpr> = match inner {
            Message::Simple { params, .. } => keywords_from_params(params),
            _ => BTreeMap::new(),
        };
        // If the LLM emitted dialect-native form, forward verbatim.
        let llm_content = inner.content().cloned();
        let dialect_content = match &llm_content {
            Some(SExpr::List(items)) if !items.is_empty() => match &items[0] {
                SExpr::Atom(Atom::Symbol(head))
                    if head == "threshold-query"
                        || head == "threshold-commitment"
                        || head == "threshold-answer"
                        || head == "richer-verdict" =>
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
                "yao-bracket" => {
                    let round = kw
                        .get("round")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Num(0)));
                    let threshold = kw
                        .get("threshold")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Num(0)));
                    kw_form(
                        "threshold-query",
                        &[("round", round), ("threshold", threshold)],
                    )
                }
                "yao-bracket-commit" => {
                    let round = kw
                        .get("round")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Num(0)));
                    let commitment = kw
                        .get("commitment")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Str("".into())));
                    kw_form(
                        "threshold-commitment",
                        &[("round", round), ("commitment", commitment)],
                    )
                }
                "yao-bracket-reveal" => {
                    let round = kw
                        .get("round")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Num(0)));
                    let bit = kw
                        .get("bit")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Bool(false)));
                    let salt = kw
                        .get("salt")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Str("".into())));
                    kw_form(
                        "threshold-answer",
                        &[("round", round), ("bit", bit), ("salt", salt)],
                    )
                }
                "yao-final" => {
                    let verdict = kw
                        .get("verdict")
                        .cloned()
                        .unwrap_or_else(|| SExpr::Atom(Atom::Symbol("unknown".to_string())));
                    kw_form("richer-verdict", &[("verdict", verdict)])
                }
                other => llm_content
                    .unwrap_or_else(|| SExpr::Atom(Atom::Symbol(other.to_string()))),
            }
        };

        let recipient = match perf_name {
            "yao-final" => Some("@operator".to_string()),
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

fn kw_form(head: &str, kvs: &[(&str, SExpr)]) -> SExpr {
    let mut items: Vec<SExpr> = vec![SExpr::Atom(Atom::Symbol(head.to_string()))];
    for (k, v) in kvs {
        items.push(SExpr::Atom(Atom::Keyword((*k).to_string())));
        items.push(v.clone());
    }
    SExpr::List(items)
}

/// Pull the boolean bit out of a yao-bracket-reveal canonical message.
fn extract_bit_from_reveal(msg: &Message) -> Option<bool> {
    let content = msg.content()?;
    let items = match content {
        SExpr::List(items) => items,
        _ => return None,
    };
    let mut iter = items.iter();
    let _ = iter.next(); // head: threshold-answer
    while let Some(item) = iter.next() {
        if let SExpr::Atom(Atom::Keyword(k)) = item {
            if let Some(v) = iter.next() {
                if k == "bit" {
                    return match v {
                        SExpr::Atom(Atom::Bool(b)) => Some(*b),
                        SExpr::Atom(Atom::Symbol(s)) => Some(matches!(
                            s.as_str(),
                            "true" | "1" | "yes"
                        )),
                        _ => None,
                    };
                }
            }
        }
    }
    None
}

/// Pull the verdict atom out of a yao-final canonical message.
fn extract_verdict_from_final(msg: &Message) -> Option<MillionaireGuess> {
    let content = msg.content()?;
    let items = match content {
        SExpr::List(items) => items,
        _ => return None,
    };
    let mut iter = items.iter();
    let _ = iter.next(); // head: richer-verdict
    while let Some(item) = iter.next() {
        if let SExpr::Atom(Atom::Keyword(k)) = item {
            if let Some(v) = iter.next() {
                if k == "verdict" {
                    let s = match v {
                        SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s)) => {
                            s.to_lowercase()
                        }
                        _ => return None,
                    };
                    return Some(match s.as_str() {
                        "richer" => MillionaireGuess::Richer,
                        "poorer" => MillionaireGuess::Poorer,
                        "equal" => MillionaireGuess::Equal,
                        _ => MillionaireGuess::Unknown,
                    });
                }
            }
        }
    }
    None
}

impl DrivenAgent for GlmCbclNativeYaoSeat {
    type Setup = MillionaireSetup;
    type Guess = MillionaireGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        let prompt = self.build_system_prompt(setup.wealth);
        self.history.push(ChatMessage::system(&prompt));
        self.privacy_patterns = build_disclosure_patterns(setup.wealth);
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
        if !had_inbound && self.turn == 0 && self.history.len() == 1 {
            self.history.push(ChatMessage::user(
                "Bob has connected. Begin the protocol by emitting a yao-bracket s-expression.",
            ));
        }

        let mut had_outbound = false;
        for _ in 0..MAX_INNER_TOOL_ITERS {
            let (tool_calls, content) = match self.call_all() {
                Ok(v) => v,
                Err(e) => {
                    eprintln!(
                        "[glm/cbcl_native_yao] trial {} turn {}: {}",
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
                for tc in tool_calls.into_iter() {
                    if tc.function.name == "compute_commitment" {
                        let args: serde_json::Value =
                            serde_json::from_str(&tc.function.arguments)
                                .unwrap_or(serde_json::Value::Null);
                        let salt = args
                            .get("salt")
                            .and_then(|v| v.as_str())
                            .unwrap_or("")
                            .to_string();
                        let bit = args
                            .get("bit")
                            .and_then(|v| v.as_bool())
                            .unwrap_or(false);
                        let mut buf = salt.as_bytes().to_vec();
                        buf.push(if bit { 1u8 } else { 0u8 });
                        let digest = Self::fnv1a_bare_hex(&buf);
                        self.tool_ack(&tc.id, &digest);
                    } else {
                        self.tool_ack(
                            &tc.id,
                            &format!(
                                "ignored: tool `{}` is not exposed by the native Yao seat. Emit CBCL s-expressions as chat content instead.",
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
        // 1. Prefer the verdict captured at yao-final emit time.
        if let Some(v) = self.final_verdict {
            return v;
        }
        // 2. Scan the store for our most-recent yao-final emission.
        if let Some(h) = self.latest_hash_of("yao-final") {
            if let Some(m) = self.store.lookup_in_thread(&h, &self.thread_id) {
                let inner = m.innermost_simple().unwrap_or(m);
                if let Some(v) = extract_verdict_from_final(inner) {
                    return v;
                }
            }
        }
        // 3. Fall back: derive verdict from own bit + observed peer bit.
        let own_wealth = self.setup.map(|s| s.wealth).unwrap_or(0);
        // Threshold defaults to wealth_range / 2 unless yao-bracket was emitted.
        let threshold = self
            .latest_hash_of("yao-bracket")
            .and_then(|h| self.store.lookup_in_thread(&h, &self.thread_id).cloned())
            .and_then(|m| extract_threshold(&m))
            .unwrap_or(self.wealth_range / 2);
        let own_bit = own_wealth >= threshold;
        match self.peer_bit {
            Some(peer_bit) => {
                if own_bit && !peer_bit {
                    MillionaireGuess::Richer
                } else if !own_bit && peer_bit {
                    MillionaireGuess::Poorer
                } else {
                    MillionaireGuess::Unknown
                }
            }
            None => MillionaireGuess::Unknown,
        }
    }
}

/// Pull the threshold integer out of a yao-bracket canonical message.
fn extract_threshold(msg: &Message) -> Option<u64> {
    let inner = msg.innermost_simple().unwrap_or(msg);
    let content = inner.content()?;
    let items = match content {
        SExpr::List(items) => items,
        _ => return None,
    };
    let mut iter = items.iter();
    let _ = iter.next(); // head: threshold-query
    while let Some(item) = iter.next() {
        if let SExpr::Atom(Atom::Keyword(k)) = item {
            if let Some(v) = iter.next() {
                if k == "threshold" {
                    return match v {
                        SExpr::Atom(Atom::Num(n)) => u64::try_from(*n).ok(),
                        _ => None,
                    };
                }
            }
        }
    }
    None
}

impl GlmCbclNativeYaoSeat {
    /// Read-only view of the quarantine list.
    pub fn quarantine(&self) -> &[QuarantineEntry] {
        &self.quarantine
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agents::cbcl::load_dialect;
    use std::path::PathBuf;

    const YAO_DIALECT_SRC: &str =
        include_str!("../../../../demo/dialects/millionaire.cbcl");

    fn make_seat(wealth: u64) -> GlmCbclNativeYaoSeat {
        let dialect = load_dialect(YAO_DIALECT_SRC).expect("dialect");
        let mut seat = GlmCbclNativeYaoSeat::new(
            Box::new(crate::glm::GlmClient::for_testing()),
            PathBuf::from("/tmp/test-yao-privacy.jsonl"),
            0,
            16,
            dialect,
            "yao-game",
            "alice",
            1_000_000_000,
        );
        // Drive ingest_setup directly so privacy patterns are populated.
        let setup = MillionaireSetup {
            agent_idx: 0,
            wealth,
        };
        <GlmCbclNativeYaoSeat as DrivenAgent>::ingest_setup(&mut seat, setup);
        seat
    }

    /// The salt-leak failure mode observed in trial 8 of the original
    /// N=20 run: the LLM derives its salt from the wealth value. The
    /// seat-level privacy check must reject this emission before it
    /// crosses the wire.
    #[test]
    fn privacy_check_rejects_wealth_in_salt() {
        let mut seat = make_seat(42);
        let mut emitted: Vec<ChatEvent> = Vec::new();
        let mut send_index_seed: u64 = 0;
        // Pre-condition: the LLM must have established the protocol
        // predecessors in the store before yao-bracket-reveal can verify.
        // We bypass that by directly emitting a yao-bracket and a
        // yao-bracket-commit with `:caused-by latest` so the third emission
        // (the wealth-bearing reveal) reaches the privacy check rather than
        // being rejected at the protocol layer.
        let pre_emissions = [
            "(yao-bracket :round 0 :threshold 500000000 :sender \"alice\" :thread \"yao-game\" :caused-by begin)",
            "(yao-bracket-commit :round 0 :commitment \"abcdef0123456789abcdef0123456789\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)",
        ];
        for body in pre_emissions {
            let mut out = |e: ChatEvent| emitted.push(e);
            let ok = seat.try_emit_assistant(body, &mut out, &mut send_index_seed);
            assert!(ok, "pre-emission `{body}` should succeed");
        }
        let pre_count = emitted.len();

        // The leaking emission: salt contains the wealth value.
        let leaky_reveal = "(yao-bracket-reveal :round 0 :bit false :salt \"alice-salt-42\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)";
        let mut out = |e: ChatEvent| emitted.push(e);
        let ok = seat.try_emit_assistant(leaky_reveal, &mut out, &mut send_index_seed);
        assert!(!ok, "wealth-bearing salt should be rejected");
        assert_eq!(
            emitted.len(),
            pre_count,
            "no ChatEvent should be emitted when the privacy check fires"
        );
        assert!(
            seat.emit_rejections >= 1,
            "rejection counter should advance"
        );
    }

    /// Sanity check: a clean salt (no wealth-encoding) passes the privacy
    /// check and emits normally.
    #[test]
    fn privacy_check_admits_clean_salt() {
        let mut seat = make_seat(42);
        let mut emitted: Vec<ChatEvent> = Vec::new();
        let mut send_index_seed: u64 = 0;
        let pre_emissions = [
            "(yao-bracket :round 0 :threshold 500000000 :sender \"alice\" :thread \"yao-game\" :caused-by begin)",
            "(yao-bracket-commit :round 0 :commitment \"abcdef0123456789abcdef0123456789\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)",
        ];
        for body in pre_emissions {
            let mut out = |e: ChatEvent| emitted.push(e);
            let _ = seat.try_emit_assistant(body, &mut out, &mut send_index_seed);
        }
        let pre_count = emitted.len();
        let clean_reveal = "(yao-bracket-reveal :round 0 :bit false :salt \"alice-rA9c\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)";
        let mut out = |e: ChatEvent| emitted.push(e);
        let ok = seat.try_emit_assistant(clean_reveal, &mut out, &mut send_index_seed);
        assert!(ok, "clean salt should be admitted");
        assert_eq!(emitted.len(), pre_count + 1, "exactly one new emission");
    }

    /// The privacy regex set is multi-base per CON-1111, so a hex-encoded
    /// wealth in the salt also fires the check.
    #[test]
    fn privacy_check_catches_hex_disclosure() {
        let mut seat = make_seat(255);
        let mut emitted: Vec<ChatEvent> = Vec::new();
        let mut send_index_seed: u64 = 0;
        let pre_emissions = [
            "(yao-bracket :round 0 :threshold 500000000 :sender \"alice\" :thread \"yao-game\" :caused-by begin)",
            "(yao-bracket-commit :round 0 :commitment \"abcdef0123456789abcdef0123456789\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)",
        ];
        for body in pre_emissions {
            let mut out = |e: ChatEvent| emitted.push(e);
            let _ = seat.try_emit_assistant(body, &mut out, &mut send_index_seed);
        }
        // Salt containing hex form of 255 (= 0xff) — the operator's regex
        // matches \b0xff\b, so the seat should reject before emit.
        let hex_leak = "(yao-bracket-reveal :round 0 :bit true :salt \"alice 0xff\" :sender \"alice\" :thread \"yao-game\" :caused-by latest)";
        let mut out = |e: ChatEvent| emitted.push(e);
        let pre_rejections = seat.emit_rejections;
        let ok = seat.try_emit_assistant(hex_leak, &mut out, &mut send_index_seed);
        assert!(!ok, "hex-encoded wealth should be rejected");
        assert!(seat.emit_rejections > pre_rejections);
    }
}
