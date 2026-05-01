//! adapter: per-operator dialect plumbing for live-LLM seats.
//!
//! A [`ProtocolAdapter`] captures everything that varies between operator
//! challenges (PSI, Yao's Millionaire, Auction, Dining, Ultimatum) when an
//! LLM is the seated agent under [`crate::llm::DisciplinedSeat`]:
//!
//! - the system prompt (which game, role, private input);
//! - the OpenAI-compatible tool definitions exposed to the model;
//! - the phase machine that constrains which tool is valid when;
//! - inbound message parsing (peer wire bytes → state mutation +
//!   structured user-turn line);
//! - canonical-form hashing and `:caused-by` resolution for the
//!   wire payloads emitted on the model's behalf;
//! - the final operator-bound guess.
//!
//! The seat (in [`crate::llm::seat`]) is fully generic over the adapter; it
//! handles only the LLM-side mechanics — chat-completions retry, transcript
//! append, history management, turn budget, send-index sequencing, and the
//! Protocol-vs-Utility tool-call inner-loop discipline.
//!
//! ## Tool kinds
//!
//! Some tools (`hash_element`, schema validators, lookup helpers) are
//! pure-utility: they advance the LLM's reasoning but do not put bytes on
//! the wire. The seat may dispatch many such tools per chat round before
//! the model commits to a protocol-advancing call. Conversely, the
//! protocol-advancing tools (`propose_salt`, `commit_set`, …) emit wire
//! bytes and end the inner loop. The adapter classifies its own tools via
//! [`ProtocolAdapter::classify_tool`].
//!
//! ## Object safety
//!
//! `ProtocolAdapter` carries associated types (`Setup`, `Guess`) and is
//! therefore not object-safe. The seat is generic over `A:
//! ProtocolAdapter`, not `dyn ProtocolAdapter`. Backend selection — the
//! orthogonal axis — uses `Box<dyn LlmBackend>` because `LlmBackend` *is*
//! object-safe. This split lets the CLI choose a backend at runtime
//! without carrying a backend generic on every seat type.

use crate::llm::{ChatMessage, ToolCall, ToolDef};

/// Per-operator dialect plumbing. See module docs for the design notes.
pub trait ProtocolAdapter: Send {
    /// Setup type issued by the operator (e.g. `PsiSetup`, `AuctionSetup`).
    type Setup: Clone + Send;
    /// Operator-bound guess submitted at the end of the game.
    type Guess: Clone + Send;

    /// Receive the operator's setup. Called once per game by the seat.
    fn ingest_setup(&mut self, setup: Self::Setup);

    /// Build the system prompt shown to the LLM at the start of the
    /// conversation. May reference internal state populated by
    /// [`Self::ingest_setup`].
    fn build_system_prompt(&self) -> String;

    /// OpenAI-compatible function-tool definitions exposed to the model.
    fn tools(&self) -> Vec<ToolDef>;

    /// Observe one inbound peer payload. Mutates internal protocol state
    /// (e.g. peer-salt tracking, peer-leaf accumulation, peer-hash
    /// indexing) and returns a structured user-turn line that the seat
    /// will fold into the next user message shown to the LLM.
    fn observe_inbound(&mut self, payload: &[u8]) -> String;

    /// User-turn text used when the seat is invoked at turn 0 with no
    /// inbound (the typical kick-off case for the focal seat).
    fn kickoff_prompt(&self) -> String;

    /// User-turn text used when the seat is invoked mid-protocol with no
    /// inbound — i.e. the LLM is being nudged to make progress on its
    /// current phase. Returning `None` means "the protocol is over,
    /// stop calling step()."
    fn idle_prompt(&self) -> Option<String>;

    /// Classify a tool by name as protocol-advancing (puts bytes on the
    /// wire, ends the seat's inner loop) or utility (pure-helper, may
    /// repeat per chat round).
    fn classify_tool(&self, tool_name: &str) -> ToolKind;

    /// Process one tool call. The adapter validates the call against its
    /// phase machine, mutates internal state, and — for protocol-
    /// advancing tools — emits zero or one wire payloads via the supplied
    /// `emit` closure. The returned [`ToolDispatch`] carries the
    /// `tool` reply body that the seat ack-s back to the LLM so the
    /// OpenAI tool-call contract is honoured.
    fn dispatch_tool(
        &mut self,
        tc: &ToolCall,
        emit: &mut dyn FnMut(Vec<u8>),
    ) -> ToolDispatch;

    /// Whether the protocol has run to completion. The seat polls this
    /// after each step to decide when to stop scheduling new chat calls.
    fn is_done(&self) -> bool;

    /// Final operator-bound guess. Called by the seat once the game is
    /// over.
    fn final_guess(&self) -> Self::Guess;
}

/// Classification of an LLM-emitted tool call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToolKind {
    /// Protocol-advancing call. The seat dispatches the first such call
    /// in a chat round, breaks the inner loop, and acks subsequent
    /// sibling protocol calls as ignored.
    Protocol,
    /// Pure-utility call (e.g. `hash_element`). The seat dispatches every
    /// utility call in a round and continues looping.
    Utility,
}

/// Outcome of one [`ProtocolAdapter::dispatch_tool`] call.
#[derive(Clone, Debug)]
pub struct ToolDispatch {
    /// Tool-reply body acked back to the LLM.
    pub ack: String,
}

/// Helper to build a [`ChatMessage`] tool reply for the given call id and
/// body. Re-exported for convenience in adapter implementations that
/// build their own intermediate ack messages.
#[doc(hidden)]
pub fn tool_reply(tool_call_id: &str, body: &str) -> ChatMessage {
    ChatMessage::tool(tool_call_id, body)
}
