//! OpenAI chat-completions backend (`gpt-4.1`).
//!
//! Near-identity to [`crate::glm::GlmClient`]: the OpenAI chat-completions
//! schema is what our [`crate::llm::ChatRequest`] / [`crate::llm::ChatResponse`]
//! types are modelled on. The only deltas vs. GLM-5.1 are:
//!
//! - Endpoint: `https://api.openai.com/v1/chat/completions`.
//! - Model: `gpt-4.1`.
//! - Auth: `Authorization: Bearer ${OPENAI_API_KEY}`.
//!
//! `max_tokens` still works for `gpt-4.1` (only the o1-series requires
//! `max_completion_tokens`). We keep the existing field name.
//!
//! ## Determinism
//!
//! Like the other backends, this is **not** deterministic. The
//! deterministic core (operator, agents, attackers, measurement) does
//! not depend on this module.

use std::io::Write;
use std::process::{Command, Stdio};

use crate::glm::CURL_BIN;
use crate::llm::{ChatRequest, ChatResponse, LlmBackend};

/// Endpoint for OpenAI chat-completions.
pub const ENDPOINT: &str = "https://api.openai.com/v1/chat/completions";
/// Model identifier.
pub const MODEL: &str = "gpt-4.1";

/// OpenAI live-LLM backend.
pub struct OpenAIBackend {
    api_key: String,
    /// Model identifier — defaults to [`MODEL`] but can be overridden
    /// (e.g. for `gpt-4.1-mini` runs).
    model: String,
}

impl OpenAIBackend {
    /// Construct a backend by reading `OPENAI_API_KEY` from the process
    /// environment.
    pub fn from_env() -> Result<Self, String> {
        let api_key = std::env::var("OPENAI_API_KEY")
            .map_err(|_| "OPENAI_API_KEY not set in environment".to_string())?;
        if api_key.trim().is_empty() {
            return Err("OPENAI_API_KEY is empty".into());
        }
        Ok(Self {
            api_key,
            model: MODEL.to_string(),
        })
    }

    /// Override the default model identifier.
    pub fn with_model(mut self, model: impl Into<String>) -> Self {
        self.model = model.into();
        self
    }

    /// Issue one chat-completions call (no retry).
    fn chat_once(
        &self,
        req: &ChatRequest,
    ) -> Result<(ChatResponse, serde_json::Value), String> {
        // Override the request's model to ours; the request struct
        // carries the model name from the seat's MODEL constant which
        // may not match this provider.
        let mut req_local = req.clone();
        req_local.model = self.model.clone();

        let body = serde_json::to_string(&req_local)
            .map_err(|e| format!("serialise request: {e}"))?;

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
        let raw: serde_json::Value = serde_json::from_str(&stdout)
            .map_err(|e| format!("parse response (raw): {e}; raw={stdout}"))?;
        let parsed: ChatResponse = serde_json::from_value(raw.clone())
            .map_err(|e| format!("parse response (typed): {e}; raw={stdout}"))?;
        Ok((parsed, raw))
    }
}

impl LlmBackend for OpenAIBackend {
    fn chat(
        &self,
        req: &ChatRequest,
    ) -> Result<(ChatResponse, serde_json::Value), String> {
        match self.chat_once(req) {
            Ok(r) => Ok(r),
            Err(first) => {
                eprintln!("[openai] first attempt failed: {first}; retrying in 5s");
                std::thread::sleep(std::time::Duration::from_secs(5));
                self.chat_once(req)
                    .map_err(|second| format!("first error: {first}; retry error: {second}"))
            }
        }
    }
    fn provider_tag(&self) -> &'static str {
        "gpt"
    }
    fn model_id(&self) -> &str {
        &self.model
    }
}
