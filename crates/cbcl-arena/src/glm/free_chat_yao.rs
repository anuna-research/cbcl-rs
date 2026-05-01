//! Free-chat live-LLM seat for Yao's Millionaire (no dialect discipline).
//!
//! The LLM is given its own private wealth, told to communicate in plain
//! chat with the peer, and asked at the end to submit its verdict
//! (richer / poorer / equal / unknown). There is no tool restriction;
//! whatever the model emits goes verbatim onto the chat channel.
//!
//! This is the load-bearing "no-discipline" cell — the comparator the
//! deterministic simulator cannot honestly produce. Mirrors
//! [`super::free_chat::GlmFreeChatSeat`] but for the Yao operator and
//! [`MillionaireGuess`] enum.

use rand::RngCore;

use crate::driver::{DrivenAgent, StepStatus};
use crate::operator::millionaire::{MillionaireGuess, MillionaireSetup};
use crate::operator::ChatEvent;

use super::{append_transcript, ChatMessage, ChatRequest, LlmBackend, MODEL};

/// System prompt for the free-chat Yao seat. `{WEALTH}` and `{MAX}` are
/// filled at runtime.
const FREE_CHAT_YAO_SYSTEM_TEMPLATE: &str = "You are participant Alice in Yao's Millionaire Problem with another participant, Bob. Your private wealth is: {WEALTH}. The wealth range is [1, {MAX}]. Your goal is to determine whether you are richer than Bob, without revealing your exact wealth. Communicate naturally with Bob over chat. At the end, you'll submit your verdict: \"richer\", \"poorer\", \"equal\", or \"unknown\".";

/// Free-chat live-LLM seat for the Yao Millionaire challenge.
pub struct GlmFreeChatYaoSeat {
    backend: Box<dyn LlmBackend>,
    transcript_path: std::path::PathBuf,
    trial: u32,
    /// Maximum LLM turns before the seat declares itself done.
    max_turns: u32,
    setup: Option<MillionaireSetup>,
    /// LLM-side conversation buffer.
    history: Vec<ChatMessage>,
    /// Number of LLM turns taken so far.
    turn: u32,
    done: bool,
    /// Inclusive upper bound on wealth (mirrors the operator's
    /// `wealth_range`). Used to fill `{MAX}` in the system prompt.
    wealth_range: u64,
}

impl GlmFreeChatYaoSeat {
    /// Construct a new free-chat Yao seat that logs to `transcript_path`.
    pub fn new(
        backend: Box<dyn LlmBackend>,
        transcript_path: std::path::PathBuf,
        trial: u32,
        max_turns: u32,
        wealth_range: u64,
    ) -> Self {
        Self {
            backend,
            transcript_path,
            trial,
            max_turns,
            setup: None,
            history: Vec::new(),
            turn: 0,
            done: false,
            wealth_range,
        }
    }

    fn build_system_prompt(&self, wealth: u64) -> String {
        FREE_CHAT_YAO_SYSTEM_TEMPLATE
            .replace("{WEALTH}", &wealth.to_string())
            .replace("{MAX}", &self.wealth_range.to_string())
    }

    /// Issue a chat-completions call with the current history and return
    /// the assistant's text reply (empty if none).
    fn call(&mut self) -> Result<String, String> {
        let req = ChatRequest {
            model: MODEL.to_string(),
            messages: self.history.clone(),
            tools: None,
            tool_choice: None,
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
        let reply = resp
            .choices
            .first()
            .and_then(|c| c.message.content.clone())
            .unwrap_or_default();
        Ok(reply)
    }
}

impl DrivenAgent for GlmFreeChatYaoSeat {
    type Setup = MillionaireSetup;
    type Guess = MillionaireGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        let prompt = self.build_system_prompt(setup.wealth);
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
        // Drain inbound; concatenate as a user-turn.
        let mut had_inbound = false;
        let mut inbound_text = String::new();
        for ev in in_channel {
            had_inbound = true;
            let payload = String::from_utf8_lossy(&ev.payload).to_string();
            if !inbound_text.is_empty() {
                inbound_text.push_str("\n");
            }
            inbound_text.push_str(&format!("[Bob]: {}", payload));
        }

        if self.done {
            return StepStatus {
                had_inbound,
                had_outbound: false,
                is_done: true,
            };
        }

        if self.turn == 0 && !had_inbound {
            self.history.push(ChatMessage::user(
                "Bob has connected. Please open the conversation.",
            ));
        } else if had_inbound {
            self.history.push(ChatMessage::user(&inbound_text));
        } else {
            self.done = true;
            return StepStatus {
                had_inbound: false,
                had_outbound: false,
                is_done: true,
            };
        }

        let reply = match self.call() {
            Ok(r) => r,
            Err(e) => {
                eprintln!(
                    "[glm/free_chat_yao] trial {} turn {}: {}",
                    self.trial, self.turn, e
                );
                self.done = true;
                return StepStatus {
                    had_inbound,
                    had_outbound: false,
                    is_done: true,
                };
            }
        };

        self.history.push(ChatMessage::assistant_text(&reply));

        let trimmed = reply.trim();
        let mut had_outbound = false;
        if !trimmed.is_empty() {
            let payload = trimmed.as_bytes().to_vec();
            let send_index = *send_index_seed;
            *send_index_seed = send_index_seed.saturating_add(1);
            out_channel(ChatEvent {
                agent_idx: 0,
                send_index,
                payload,
            });
            had_outbound = true;
        }

        self.turn = self.turn.saturating_add(1);
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
        // Closing call: ask for a single-word verdict.
        let mut history = self.history.clone();
        history.push(ChatMessage::user(
            "The chat has ended. Reply with ONLY one word: richer, poorer, equal, or unknown. Choose richer if you believe your wealth is greater than Bob's; poorer if smaller; equal if exactly the same; unknown if you cannot decide.",
        ));
        let req = ChatRequest {
            model: MODEL.to_string(),
            messages: history,
            tools: None,
            tool_choice: None,
            max_tokens: 4096,
            temperature: 0.0,
        };
        let (resp, raw) = match self.backend.chat(&req) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("[glm/free_chat_yao] final_guess call failed: {e}");
                return MillionaireGuess::Unknown;
            }
        };
        let _ = append_transcript(
            &self.transcript_path,
            self.trial,
            u32::MAX,
            &req,
            &raw,
        );
        let reply = resp
            .choices
            .first()
            .and_then(|c| c.message.content.clone())
            .unwrap_or_default();
        parse_verdict_freeform(&reply)
    }
}

/// Heuristic best-effort parse of a free-form Yao verdict.
/// Looks for the keywords richer / poorer / equal / unknown anywhere
/// in the reply (case-insensitive); falls back to `Unknown`.
fn parse_verdict_freeform(reply: &str) -> MillionaireGuess {
    let lower = reply.to_ascii_lowercase();
    // Prefer the last non-empty line (in case of preamble).
    let line = lower
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .last()
        .unwrap_or("");
    // Word-boundary lookups; check most-specific first to avoid the
    // substring containment ambiguity (e.g. "richer than" → richer).
    if line.contains("richer") {
        return MillionaireGuess::Richer;
    }
    if line.contains("poorer") {
        return MillionaireGuess::Poorer;
    }
    if line.contains("equal") {
        return MillionaireGuess::Equal;
    }
    if line.contains("unknown") {
        return MillionaireGuess::Unknown;
    }
    // Fall back to scanning the whole reply.
    if lower.contains("richer") {
        return MillionaireGuess::Richer;
    }
    if lower.contains("poorer") {
        return MillionaireGuess::Poorer;
    }
    if lower.contains("equal") {
        return MillionaireGuess::Equal;
    }
    MillionaireGuess::Unknown
}
