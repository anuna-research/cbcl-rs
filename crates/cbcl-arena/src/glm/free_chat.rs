//! Free-chat live-LLM seat (no dialect discipline).
//!
//! The LLM is given its own private set, told to communicate in plain
//! chat with the peer, and asked at the end to submit its best guess
//! of the intersection. There is no tool restriction; whatever the
//! model emits goes verbatim onto the chat channel.
//!
//! This is the load-bearing "no-discipline" cell — the one whose
//! behaviour the deterministic simulator cannot honestly produce.

use rand::RngCore;

use crate::driver::{DrivenAgent, StepStatus};
use crate::operator::psi::{PsiGuess, PsiSetup};
use crate::operator::ChatEvent;

use super::{append_transcript, ChatMessage, ChatRequest, LlmBackend, MODEL};

/// System prompt for the free-chat seat. Intentionally generic — no
/// mention of dialects or performatives. `{SET}` is filled at runtime.
const FREE_CHAT_SYSTEM_TEMPLATE: &str = "You are participant Alice in a Private Set Intersection game with another participant, Bob. Your private set is: {SET}. Bob has his own private set. Your goal is to determine which elements you both share, without unnecessarily revealing elements you don't share. Communicate naturally with Bob over chat. At the end, you'll submit your best guess of the intersection.";

/// Free-chat live-LLM seat for the PSI challenge. Backend-agnostic:
/// the original GLM-5.1 cell now runs through `Box<dyn LlmBackend>`
/// so the same seat covers the gpt-5.5 (Codex proxy) cells too.
pub struct GlmFreeChatSeat {
    backend: Box<dyn LlmBackend>,
    transcript_path: std::path::PathBuf,
    trial: u32,
    /// Maximum LLM turns before the seat declares itself done.
    max_turns: u32,
    setup: Option<PsiSetup>,
    /// LLM-side conversation buffer (system + user turns recording
    /// inbound from the peer + assistant turns recording our replies).
    history: Vec<ChatMessage>,
    /// Number of LLM turns taken so far.
    turn: u32,
    done: bool,
}

impl GlmFreeChatSeat {
    /// Construct a new free-chat seat that logs to `transcript_path`.
    pub fn new(
        backend: Box<dyn LlmBackend>,
        transcript_path: std::path::PathBuf,
        trial: u32,
        max_turns: u32,
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
        }
    }

    fn build_system_prompt(set: &[String]) -> String {
        let joined = set.join(", ");
        FREE_CHAT_SYSTEM_TEMPLATE.replace("{SET}", &joined)
    }

    /// Issue a chat-completions call with the current history and
    /// return the assistant's text reply (empty if none).
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

impl DrivenAgent for GlmFreeChatSeat {
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
        // Drain inbound; concatenate as a user-turn (one per step).
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

        // First turn: even with no inbound, kick off with a synthetic
        // "Bob is connected, please open the conversation." prompt so
        // the model has something to react to.
        if self.turn == 0 && !had_inbound {
            self.history.push(ChatMessage::user(
                "Bob has connected. Please open the conversation.",
            ));
        } else if had_inbound {
            self.history.push(ChatMessage::user(&inbound_text));
        } else {
            // No inbound and we've already opened — nothing to say.
            // Mark done so the driver can wind down.
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
                eprintln!("[glm/free_chat] trial {} turn {}: {}", self.trial, self.turn, e);
                self.done = true;
                return StepStatus {
                    had_inbound,
                    had_outbound: false,
                    is_done: true,
                };
            }
        };

        // Append assistant message to history (so the model sees its own
        // prior turn next time).
        self.history.push(ChatMessage::assistant_text(&reply));

        let trimmed = reply.trim();
        let mut had_outbound = false;
        if !trimmed.is_empty() {
            let payload = trimmed.as_bytes().to_vec();
            let send_index = *send_index_seed;
            *send_index_seed = send_index_seed.saturating_add(1);
            out_channel(ChatEvent {
                agent_idx: 0, // overwritten by driver
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
        // Rebuild the closing call from the current history. We log it
        // under turn `u32::MAX` (informational sentinel for "final").
        let mut history = self.history.clone();
        history.push(ChatMessage::user(
            "The chat has ended. Please reply with ONLY a comma-separated list of the elements you believe are in the intersection of your set and Bob's set. If you don't know, reply with the single word EMPTY.",
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
                eprintln!("[glm/free_chat] final_guess call failed: {e}");
                return Vec::new();
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
        parse_guess_freeform(&reply)
    }
}

/// Heuristic best-effort parse of a free-form intersection guess.
/// Splits on commas, trims, drops the literal `EMPTY` sentinel and
/// any token containing whitespace (we expect single-word elements
/// per the PSI universe).
fn parse_guess_freeform(reply: &str) -> Vec<String> {
    // First clean up: take the last non-empty line in case the model
    // preamble-explained.
    let line = reply
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .last()
        .unwrap_or("");
    if line.eq_ignore_ascii_case("empty") {
        return Vec::new();
    }
    line.split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .filter(|s| !s.eq_ignore_ascii_case("empty"))
        .map(|s| {
            s.trim_matches(|c: char| {
                !c.is_ascii_alphanumeric() && c != '-' && c != '_'
            })
            .to_lowercase()
        })
        .filter(|s| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphabetic()))
        .collect()
}
