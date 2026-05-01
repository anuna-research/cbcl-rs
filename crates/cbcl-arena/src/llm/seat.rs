//! seat: generic disciplined live-LLM seat.
//!
//! [`DisciplinedSeat`] drives an LLM through a turn-by-turn protocol under
//! the discipline of a [`ProtocolAdapter`]. It is generic over the
//! adapter (per-operator dialect plumbing) but uses a `Box<dyn
//! LlmBackend>` for the chat backend — backend selection is a runtime
//! axis, adapter selection is a compile-time axis. See the trait
//! [module docs](super::adapter) for the rationale.
//!
//! ## What the seat owns
//!
//! - The conversation [history](ChatMessage) buffer (system + user +
//!   assistant + tool messages, in OpenAI shape).
//! - Transcript-on-disk append (one JSONL row per chat round).
//! - The retry / max_turns budget.
//! - The send-index sequencing handed to outbound [`ChatEvent`]s.
//! - The Protocol-vs-Utility tool-call inner-loop discipline (drain
//!   utility tools, dispatch the first protocol tool, ignore sibling
//!   protocol tools).
//!
//! ## What the adapter owns
//!
//! Everything game-specific — phase machine, tool definitions, system
//! prompt, inbound parsing, canonical-form hashing, wire-payload
//! synthesis, final guess. See [`crate::llm::adapter`].
//!
//! The current `glm/disciplined.rs` (the original PSI-only seat) is
//! re-expressed as `DisciplinedSeat<PsiDisciplinedAdapter>` driving a
//! `Box<dyn LlmBackend>` (typically a [`crate::glm::GlmClient`]).

use std::path::PathBuf;

use rand::RngCore;

use crate::driver::{DrivenAgent, StepStatus};
use crate::operator::ChatEvent;

use super::{
    append_transcript, ChatMessage, ChatRequest, LlmBackend, ProtocolAdapter, ToolCall,
    ToolKind,
};

/// Maximum chat-completions rounds inside a single [`DrivenAgent::step`]
/// before forcing the seat to yield. The original PSI seat used 6; we
/// preserve that bound for byte-for-byte parity with existing transcripts.
const MAX_INNER_ROUNDS: u32 = 6;

/// Sampling temperature. The original PSI seat used 0.0 (deterministic
/// decoding within whatever non-determinism the provider permits). We
/// preserve that.
const TEMPERATURE: f32 = 0.0;

/// Max tokens budget per chat round. GLM-5.1 in particular burns
/// reasoning tokens before content; 4096 is the empirically safe value
/// (the seat's transcript will show empty content on smaller budgets).
const MAX_TOKENS: u32 = 4096;

/// Generic disciplined live-LLM seat.
///
/// The agent slot occupied by this seat is `0` by convention (matches the
/// existing `glm/disciplined.rs` seat) — the operator-side scoring code
/// reads `agent_idx == 0` for the focal LLM seat and `agent_idx == 1` for
/// the peer (deterministic CBCL agent or attacker pattern).
pub struct DisciplinedSeat<A: ProtocolAdapter> {
    backend: Box<dyn LlmBackend>,
    adapter: A,
    transcript_path: PathBuf,
    trial: u32,
    max_turns: u32,
    history: Vec<ChatMessage>,
    turn: u32,
    done: bool,
}

impl<A: ProtocolAdapter> DisciplinedSeat<A> {
    /// Construct a new seat. `transcript_path` is appended to one JSONL
    /// row per chat round; parent directories are created on demand.
    pub fn new(
        backend: Box<dyn LlmBackend>,
        adapter: A,
        transcript_path: PathBuf,
        trial: u32,
        max_turns: u32,
    ) -> Self {
        Self {
            backend,
            adapter,
            transcript_path,
            trial,
            max_turns,
            history: Vec::new(),
            turn: 0,
            done: false,
        }
    }

    /// Borrow the underlying adapter. Useful in tests for asserting on
    /// adapter-internal phase / state after a step.
    pub fn adapter(&self) -> &A {
        &self.adapter
    }

    /// Issue one chat round and append the assistant message into history.
    /// Returns the LLM's tool calls (possibly empty) for the seat's inner
    /// loop to dispatch.
    fn call_round(&mut self) -> Result<Vec<ToolCall>, String> {
        let req = ChatRequest {
            model: self.backend.model_id().to_string(),
            messages: self.history.clone(),
            tools: Some(self.adapter.tools()),
            tool_choice: Some("auto".into()),
            max_tokens: MAX_TOKENS,
            temperature: TEMPERATURE,
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
            None => return Ok(Vec::new()),
        };
        let content = choice.message.content.clone();
        let tcs = choice.message.tool_calls.clone().unwrap_or_default();
        self.history.push(ChatMessage {
            role: "assistant".into(),
            content,
            tool_calls: choice.message.tool_calls.clone(),
            tool_call_id: None,
        });
        Ok(tcs)
    }

    /// Append a `tool` reply to the conversation history.
    fn ack(&mut self, tool_call_id: &str, body: &str) {
        self.history
            .push(ChatMessage::tool(tool_call_id, body));
    }
}

impl<A: ProtocolAdapter> DrivenAgent for DisciplinedSeat<A> {
    type Setup = A::Setup;
    type Guess = A::Guess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.adapter.ingest_setup(setup);
        let prompt = self.adapter.build_system_prompt();
        self.history.push(ChatMessage::system(&prompt));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        _rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> StepStatus {
        // Drain inbound; each peer payload mutates adapter state and
        // contributes one structured line to the user-turn we'll show
        // the LLM.
        let mut had_inbound = false;
        let mut inbound_lines: Vec<String> = Vec::new();
        for ev in in_channel {
            had_inbound = true;
            inbound_lines.push(self.adapter.observe_inbound(&ev.payload));
        }

        if self.done {
            return StepStatus {
                had_inbound,
                had_outbound: false,
                is_done: true,
            };
        }

        // Build the user-turn shown to the LLM.
        let user_text = if !inbound_lines.is_empty() {
            inbound_lines.join("\n")
        } else if self.turn == 0 {
            self.adapter.kickoff_prompt()
        } else {
            match self.adapter.idle_prompt() {
                Some(s) => s,
                None => {
                    self.done = true;
                    return StepStatus {
                        had_inbound,
                        had_outbound: false,
                        is_done: true,
                    };
                }
            }
        };
        self.history.push(ChatMessage::user(&user_text));

        // Inner loop: drain utility tool calls (hash_element et al), then
        // break with the first protocol-advancing call. Sibling protocol
        // calls in the same chat round are acked as ignored — the OpenAI
        // contract requires every assistant tool_call to receive a
        // matching `tool` reply.
        let mut had_outbound = false;
        for _ in 0..MAX_INNER_ROUNDS {
            let tcs = match self.call_round() {
                Ok(v) => v,
                Err(e) => {
                    eprintln!(
                        "[llm/seat:{}] trial {} turn {}: {}",
                        self.backend.provider_tag(),
                        self.trial,
                        self.turn,
                        e
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

            if tcs.is_empty() {
                // The model produced text-only or yielded; surface
                // control to the driver.
                break;
            }

            let mut saw_protocol = false;
            let mut break_after = false;
            for tc in tcs {
                let kind = self.adapter.classify_tool(&tc.function.name);
                match kind {
                    ToolKind::Protocol if !saw_protocol => {
                        saw_protocol = true;
                        let mut local_emitted = false;
                        let dispatch = {
                            // Closure captures both `out_channel` and
                            // `send_index_seed` mutably. Each emit bumps
                            // the send-index and forwards a wire-shaped
                            // ChatEvent to the driver.
                            let mut emit = |bytes: Vec<u8>| {
                                local_emitted = true;
                                let send_index = *send_index_seed;
                                *send_index_seed = send_index_seed.saturating_add(1);
                                out_channel(ChatEvent {
                                    agent_idx: 0,
                                    send_index,
                                    payload: bytes,
                                });
                            };
                            self.adapter.dispatch_tool(&tc, &mut emit)
                        };
                        if local_emitted {
                            had_outbound = true;
                        }
                        self.ack(&tc.id, &dispatch.ack);
                        break_after = true;
                    }
                    ToolKind::Protocol => {
                        self.ack(
                            &tc.id,
                            "ignored: a prior protocol tool already executed in this turn",
                        );
                    }
                    ToolKind::Utility => {
                        // Utility tools never emit on the wire; pass a
                        // no-op emit closure so a misbehaving adapter
                        // can't smuggle bytes out.
                        let mut never = |_: Vec<u8>| {};
                        let dispatch = self.adapter.dispatch_tool(&tc, &mut never);
                        self.ack(&tc.id, &dispatch.ack);
                    }
                }
            }

            if break_after {
                break;
            }
            if self.turn >= self.max_turns {
                break;
            }
        }

        if self.adapter.is_done() {
            self.done = true;
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
        self.adapter.final_guess()
    }
}
