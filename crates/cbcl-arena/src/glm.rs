//! glm: Z.ai GLM-5.1 OpenAI-compatible HTTP client (live-LLM probe).
//!
//! Live-LLM probe of the PSI arena challenge. The deterministic simulator
//! in [`crate::measurement`] cannot honestly produce a behavioural claim
//! for "what the model would do" — its Vanilla agent is a hand-tuned
//! script and its CBCL agent's leak-rate is a structural (code-level)
//! property. This module implements the live cell that the simulator
//! cannot.
//!
//! ## Endpoint
//!
//! `https://api.z.ai/api/coding/paas/v4/chat/completions` (OpenAI-compat).
//! Auth: `Authorization: Bearer $ZAI_API_KEY`.
//!
//! ## HTTP backend
//!
//! We shell out to `/usr/bin/curl` rather than pulling in a workspace
//! dep (NFR-1112: no new deps). The system curl path is hard-coded to
//! avoid an `rtk` proxy in the user's `$PATH` mangling URLs.
//!
//! ## Reasoning-token budget
//!
//! GLM-5.1 burns reasoning tokens before emitting visible content; we
//! always set `max_tokens = 4096`. With smaller budgets the reply
//! field comes back empty.
//!
//! ## Determinism
//!
//! This module is **not** deterministic — that is its whole purpose.
//! The deterministic core (operator, agents, attackers, measurement)
//! does not depend on this module.

use serde::{Deserialize, Serialize};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

pub mod free_chat;
pub mod disciplined;

pub use disciplined::GlmDisciplinedSeat;
pub use free_chat::GlmFreeChatSeat;

/// Endpoint path (OpenAI-compatible chat-completions).
pub const ENDPOINT: &str = "https://api.z.ai/api/coding/paas/v4/chat/completions";
/// Model identifier.
pub const MODEL: &str = "glm-5.1";
/// System curl binary path (hard-coded to bypass any `rtk`/PATH proxy).
pub const CURL_BIN: &str = "/usr/bin/curl";

/// One chat message in the OpenAI-compatible schema.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChatMessage {
    /// Role: `system`, `user`, `assistant`, or `tool`.
    pub role: String,
    /// Message content (textual). For tool-call messages this may be empty.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content: Option<String>,
    /// Tool calls emitted by the assistant (only for `role == "assistant"`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_calls: Option<Vec<ToolCall>>,
    /// Tool-call id this message responds to (only for `role == "tool"`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_call_id: Option<String>,
}

impl ChatMessage {
    /// Construct a `system` message with the supplied prompt.
    pub fn system(content: &str) -> Self {
        Self {
            role: "system".into(),
            content: Some(content.into()),
            tool_calls: None,
            tool_call_id: None,
        }
    }
    /// Construct a `user` message.
    pub fn user(content: &str) -> Self {
        Self {
            role: "user".into(),
            content: Some(content.into()),
            tool_calls: None,
            tool_call_id: None,
        }
    }
    /// Construct an `assistant` message with content (no tool calls).
    pub fn assistant_text(content: &str) -> Self {
        Self {
            role: "assistant".into(),
            content: Some(content.into()),
            tool_calls: None,
            tool_call_id: None,
        }
    }
    /// Construct a `tool` reply for the given tool-call id.
    pub fn tool(tool_call_id: &str, content: &str) -> Self {
        Self {
            role: "tool".into(),
            content: Some(content.into()),
            tool_calls: None,
            tool_call_id: Some(tool_call_id.into()),
        }
    }
}

/// OpenAI-compatible function tool definition.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ToolDef {
    /// Always `"function"`.
    #[serde(rename = "type")]
    pub kind: String,
    /// Function spec.
    pub function: FunctionDef,
}

/// Function spec inside a [`ToolDef`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FunctionDef {
    /// Function name.
    pub name: String,
    /// Human-readable description shown to the LLM.
    pub description: String,
    /// JSONSchema object describing the function parameters.
    pub parameters: serde_json::Value,
}

/// Tool call emitted by the assistant.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ToolCall {
    /// Server-assigned id (echoed back in tool-result messages).
    pub id: String,
    /// Always `"function"`.
    #[serde(rename = "type")]
    pub kind: String,
    /// Function call payload.
    pub function: ToolCallFunction,
}

/// Inner function payload of a [`ToolCall`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ToolCallFunction {
    /// Function name.
    pub name: String,
    /// Function arguments (JSON-encoded as a string per OpenAI convention).
    pub arguments: String,
}

/// Chat-completions request body.
#[derive(Clone, Debug, Serialize)]
pub struct ChatRequest {
    /// Model identifier.
    pub model: String,
    /// Conversation so far.
    pub messages: Vec<ChatMessage>,
    /// Function tools available to the assistant.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tools: Option<Vec<ToolDef>>,
    /// `"auto"` / `"required"` / `"none"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_choice: Option<String>,
    /// Maximum tokens (must include reasoning budget for GLM-5.1).
    pub max_tokens: u32,
    /// Sampling temperature.
    pub temperature: f32,
}

/// Top-level chat-completions response.
#[derive(Clone, Debug, Deserialize)]
pub struct ChatResponse {
    /// Generated choices (we only ever inspect `[0]`).
    pub choices: Vec<Choice>,
    /// Token-accounting block.
    pub usage: Usage,
}

/// One generation choice.
#[derive(Clone, Debug, Deserialize)]
pub struct Choice {
    /// Why generation stopped (`stop`, `tool_calls`, `length`, ...).
    #[serde(default)]
    pub finish_reason: Option<String>,
    /// Choice index.
    #[serde(default)]
    pub index: u32,
    /// Generated assistant message.
    pub message: ChoiceMessage,
}

/// Assistant message inside a [`Choice`].
#[derive(Clone, Debug, Deserialize)]
pub struct ChoiceMessage {
    /// `"assistant"`.
    pub role: String,
    /// Reply text (may be empty when only tool calls were emitted).
    #[serde(default)]
    pub content: Option<String>,
    /// Reasoning (chain-of-thought) text — server-returned; we log but
    /// do not surface to downstream callers.
    #[serde(default)]
    pub reasoning_content: Option<String>,
    /// Tool calls emitted by the assistant.
    #[serde(default)]
    pub tool_calls: Option<Vec<ToolCall>>,
}

/// Usage block returned by Z.ai.
#[derive(Clone, Debug, Deserialize)]
pub struct Usage {
    /// Tokens spent on the prompt.
    #[serde(default)]
    pub prompt_tokens: u64,
    /// Tokens spent on the completion (incl. reasoning).
    #[serde(default)]
    pub completion_tokens: u64,
    /// Total tokens consumed.
    #[serde(default)]
    pub total_tokens: u64,
}

/// Live-LLM client backed by `/usr/bin/curl`.
pub struct GlmClient {
    api_key: String,
}

impl GlmClient {
    /// Construct a client by reading `ZAI_API_KEY` from the process
    /// environment. The key is stored in the struct but never logged.
    pub fn from_env() -> Result<Self, String> {
        let api_key = std::env::var("ZAI_API_KEY")
            .map_err(|_| "ZAI_API_KEY not set in environment".to_string())?;
        if api_key.trim().is_empty() {
            return Err("ZAI_API_KEY is empty".into());
        }
        Ok(Self { api_key })
    }

    /// Issue one chat-completions call. Retries once on transport/server
    /// error after a 5-second sleep, then propagates. Returns both the
    /// strongly-typed [`ChatResponse`] and the raw JSON value so callers
    /// can write the unmolested body to the transcript.
    pub fn chat(&self, req: &ChatRequest) -> Result<(ChatResponse, serde_json::Value), String> {
        match self.chat_once(req) {
            Ok(r) => Ok(r),
            Err(first) => {
                eprintln!("[glm] first attempt failed: {first}; retrying in 5s");
                std::thread::sleep(std::time::Duration::from_secs(5));
                self.chat_once(req).map_err(|second| {
                    format!("first error: {first}; retry error: {second}")
                })
            }
        }
    }

    fn chat_once(&self, req: &ChatRequest) -> Result<(ChatResponse, serde_json::Value), String> {
        let body = serde_json::to_string(req)
            .map_err(|e| format!("serialise request: {e}"))?;

        // Stream the body into curl over stdin to keep the API key off
        // the argv. Curl reads `@-` from stdin via `--data-binary @-`.
        let auth = format!("Authorization: Bearer {}", self.api_key);
        let mut child = Command::new(CURL_BIN)
            .arg("-sS")
            .arg("--fail-with-body")
            .arg("-X")
            .arg("POST")
            .arg(ENDPOINT)
            .arg("-H")
            .arg(&auth)
            .arg("-H")
            .arg("Content-Type: application/json")
            .arg("--data-binary")
            .arg("@-")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("spawn curl: {e}"))?;
        {
            let stdin = child.stdin.as_mut().ok_or("no stdin on curl")?;
            stdin
                .write_all(body.as_bytes())
                .map_err(|e| format!("write to curl stdin: {e}"))?;
        }
        let out = child
            .wait_with_output()
            .map_err(|e| format!("wait curl: {e}"))?;
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        let stderr = String::from_utf8_lossy(&out.stderr).to_string();
        if !out.status.success() {
            return Err(format!(
                "curl exit {:?}: stderr={stderr}; stdout={stdout}",
                out.status.code()
            ));
        }
        // Parse twice: once into a typed view, once into a raw `Value`
        // for transcript logging (so unknown fields survive).
        let raw: serde_json::Value = serde_json::from_str(&stdout)
            .map_err(|e| format!("parse response (raw): {e}; raw={stdout}"))?;
        let parsed: ChatResponse = serde_json::from_value(raw.clone())
            .map_err(|e| format!("parse response (typed): {e}; raw={stdout}"))?;
        Ok((parsed, raw))
    }
}

/// Append one JSONL row to the transcript file at `path`.
///
/// Each row is `{"ts": ..., "trial": ..., "turn": ..., "request": ...,
/// "response": ...}`. Creates parent directories on demand.
pub fn append_transcript(
    path: &Path,
    trial: u32,
    turn: u32,
    request: &ChatRequest,
    response_raw: &serde_json::Value,
) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("create transcript dir: {e}"))?;
    }
    let row = serde_json::json!({
        "ts": utc_now_iso(),
        "trial": trial,
        "turn": turn,
        "request": request,
        "response": response_raw,
    });
    let line = serde_json::to_string(&row)
        .map_err(|e| format!("serialise transcript row: {e}"))?;
    let mut f = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .map_err(|e| format!("open transcript: {e}"))?;
    writeln!(f, "{line}").map_err(|e| format!("write transcript: {e}"))?;
    Ok(())
}

/// Naive UTC timestamp. We avoid `chrono`/`time` deps (NFR-1112) and emit
/// `1970-01-01T00:00:00Z + N` seconds as `1970+Ns`. The transcript carries
/// trial/turn anyway; the timestamp is informational.
pub fn utc_now_iso() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    // Approximate ISO-8601-ish formatting: "epoch+<secs>s". Good enough
    // for after-the-fact correlation (REQ-1150 is not an SLA artefact).
    format!("epoch+{}s", secs)
}

/// Path under `crates/cbcl-arena/transcripts/` for a given cell + trial.
pub fn transcript_path(cell: &str, trial: u32) -> PathBuf {
    PathBuf::from(format!(
        "crates/cbcl-arena/transcripts/glm51-{}-{:03}.jsonl",
        cell, trial
    ))
}
