//! OpenAI Responses API backend via local Codex proxy (`gpt-5.5`).
//!
//! Implements [`LlmBackend`] over a locally-running
//! [`codex-responses-proxy`](https://github.com/David-Factor/codex-responses-proxy)
//! that forwards `/v1/responses` requests to the Codex backend used by the
//! `codex` CLI. Auth comes from `~/.codex/auth.json` (a working ChatGPT/Codex
//! login) and is owned entirely by the proxy; this backend never sees the
//! token.
//!
//! ## Why the proxy
//!
//! ChatGPT subscriptions don't include OpenAI API access. The proxy exposes
//! the Codex backend that powers the `codex` CLI as an OpenAI-compatible
//! Responses API on `127.0.0.1:8787`, letting us call `gpt-5.5` against the
//! subscription quota rather than a paid API key.
//!
//! Only `gpt-5.5` is exposed by the Codex backend on a ChatGPT account —
//! `gpt-5`, `gpt-5-codex`, `gpt-5-mini`, `o3-mini`, etc. all return
//! `"model is not supported when using Codex with a ChatGPT account"`.
//!
//! ## Schema translation
//!
//! Chat Completions ([`ChatRequest`]/[`ChatResponse`]) ↔ Responses API:
//!
//! - **`messages` → `input`**: each [`ChatMessage`](crate::llm::ChatMessage)
//!   becomes one item in the Responses `input` array. Plain text messages
//!   keep `{role, content}`. Assistant tool calls become a `function_call`
//!   item per [`ToolCall`](crate::llm::ToolCall). Role `tool` (a tool reply)
//!   becomes a `function_call_output` item using the matching `call_id`.
//! - **`tools` → `tools`**: Responses API tools are flattened (no nested
//!   `function: { ... }`); we translate `{type:"function", function:{name,
//!   description, parameters}}` → `{type:"function", name, description,
//!   parameters}`.
//! - **`max_tokens` / `temperature`**: dropped. The proxy strips
//!   `max_output_tokens` and `max_completion_tokens` because the Codex
//!   backend rejects them; we don't bother sending them. Temperature is
//!   forwarded if you want to keep it; we set it from the request for
//!   parity with the GLM run (which used `temperature: 0`).
//!
//! Responses API output → Chat Completions:
//!
//! - The `output` array is walked once. `message`-typed items contribute
//!   their `output_text` content to `choices[0].message.content`.
//!   `function_call` items become entries in `choices[0].message.tool_calls`
//!   (the proxy preserves `call_id`, `name`, and `arguments`).
//! - `finish_reason` is `"tool_calls"` if any function calls were emitted,
//!   else `"stop"`.
//! - `usage` translates `input_tokens`/`output_tokens`/`total_tokens` to
//!   the Chat Completions `prompt_tokens`/`completion_tokens`/`total_tokens`
//!   fields.
//!
//! ## Determinism
//!
//! Like all live-LLM backends, this is **not** deterministic. The
//! deterministic core (operator, agents, attackers, measurement) does not
//! depend on this module.

use std::io::Write;
use std::process::{Command, Stdio};

use crate::glm::CURL_BIN;
use crate::llm::{
    ChatRequest, ChatResponse, Choice, ChoiceMessage, LlmBackend, ToolCall, ToolCallFunction,
    Usage,
};

/// Endpoint exposed by the local proxy. The proxy listens on
/// `127.0.0.1:8787` by default.
pub const ENDPOINT: &str = "http://127.0.0.1:8787/v1/responses";
/// Model identifier (the only one exposed via the Codex backend on a
/// ChatGPT account).
pub const MODEL: &str = "gpt-5.5";

/// OpenAI Responses API backend, talking to the local Codex proxy.
pub struct CodexBackend {
    endpoint: String,
    model: String,
}

impl Default for CodexBackend {
    fn default() -> Self {
        Self {
            endpoint: ENDPOINT.to_string(),
            model: MODEL.to_string(),
        }
    }
}

impl CodexBackend {
    /// Construct a backend pointing at the default proxy address
    /// (`http://127.0.0.1:8787/v1/responses`) and model (`gpt-5.5`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Override the proxy endpoint (e.g. if you run the proxy on a
    /// non-default port).
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = endpoint.into();
        self
    }

    /// Override the model identifier.
    pub fn with_model(mut self, model: impl Into<String>) -> Self {
        self.model = model.into();
        self
    }

    /// Build the Responses API request body from a Chat Completions
    /// [`ChatRequest`].
    fn translate_request(&self, req: &ChatRequest) -> serde_json::Value {
        let mut input: Vec<serde_json::Value> = Vec::with_capacity(req.messages.len());
        for m in &req.messages {
            match m.role.as_str() {
                "system" | "user" => {
                    let content = m.content.clone().unwrap_or_default();
                    input.push(serde_json::json!({
                        "role": m.role,
                        "content": content,
                    }));
                }
                "assistant" => {
                    if let Some(text) = &m.content {
                        if !text.is_empty() {
                            input.push(serde_json::json!({
                                "role": "assistant",
                                "content": text,
                            }));
                        }
                    }
                    if let Some(calls) = &m.tool_calls {
                        for tc in calls {
                            input.push(serde_json::json!({
                                "type": "function_call",
                                "call_id": tc.id,
                                "name": tc.function.name,
                                "arguments": tc.function.arguments,
                            }));
                        }
                    }
                }
                "tool" => {
                    let call_id = m.tool_call_id.clone().unwrap_or_default();
                    let output = m.content.clone().unwrap_or_default();
                    input.push(serde_json::json!({
                        "type": "function_call_output",
                        "call_id": call_id,
                        "output": output,
                    }));
                }
                other => {
                    // Unknown role — pass through as user content for safety.
                    let content = m.content.clone().unwrap_or_default();
                    input.push(serde_json::json!({
                        "role": "user",
                        "content": format!("[{other}] {content}"),
                    }));
                }
            }
        }

        let mut body = serde_json::json!({
            "model": self.model,
            "input": input,
        });

        if let Some(tools) = &req.tools {
            let translated: Vec<serde_json::Value> = tools
                .iter()
                .map(|t| {
                    serde_json::json!({
                        "type": "function",
                        "name": t.function.name,
                        "description": t.function.description,
                        "parameters": t.function.parameters,
                    })
                })
                .collect();
            body["tools"] = serde_json::Value::Array(translated);
        }

        if let Some(choice) = &req.tool_choice {
            // "auto" / "required" / "none" are valid in the Responses API.
            body["tool_choice"] = serde_json::Value::String(choice.clone());
        }

        body
    }

    /// Translate the Responses API JSON into a Chat Completions
    /// [`ChatResponse`].
    fn translate_response(raw: &serde_json::Value) -> Result<ChatResponse, String> {
        let output = raw
            .get("output")
            .and_then(|v| v.as_array())
            .ok_or_else(|| {
                format!("Responses API: missing/non-array `output`; raw={raw}")
            })?;

        let mut text = String::new();
        let mut tool_calls: Vec<ToolCall> = Vec::new();

        for item in output {
            let kind = item.get("type").and_then(|v| v.as_str()).unwrap_or("");
            match kind {
                "message" => {
                    if let Some(content) = item.get("content").and_then(|v| v.as_array()) {
                        for c in content {
                            if c.get("type").and_then(|v| v.as_str()) == Some("output_text") {
                                if let Some(t) = c.get("text").and_then(|v| v.as_str()) {
                                    if !text.is_empty() {
                                        text.push('\n');
                                    }
                                    text.push_str(t);
                                }
                            }
                        }
                    }
                }
                "function_call" => {
                    let call_id = item
                        .get("call_id")
                        .and_then(|v| v.as_str())
                        .unwrap_or_default()
                        .to_string();
                    let name = item
                        .get("name")
                        .and_then(|v| v.as_str())
                        .unwrap_or_default()
                        .to_string();
                    let arguments = item
                        .get("arguments")
                        .and_then(|v| v.as_str())
                        .unwrap_or_default()
                        .to_string();
                    tool_calls.push(ToolCall {
                        id: call_id,
                        kind: "function".to_string(),
                        function: ToolCallFunction { name, arguments },
                    });
                }
                // "reasoning" and other item types are ignored — they're
                // server-side internals we don't surface.
                _ => {}
            }
        }

        let finish_reason = if tool_calls.is_empty() {
            "stop".to_string()
        } else {
            "tool_calls".to_string()
        };

        let usage = if let Some(u) = raw.get("usage") {
            Usage {
                prompt_tokens: u.get("input_tokens").and_then(|v| v.as_u64()).unwrap_or(0),
                completion_tokens: u
                    .get("output_tokens")
                    .and_then(|v| v.as_u64())
                    .unwrap_or(0),
                total_tokens: u.get("total_tokens").and_then(|v| v.as_u64()).unwrap_or(0),
            }
        } else {
            Usage {
                prompt_tokens: 0,
                completion_tokens: 0,
                total_tokens: 0,
            }
        };

        Ok(ChatResponse {
            choices: vec![Choice {
                finish_reason: Some(finish_reason),
                index: 0,
                message: ChoiceMessage {
                    role: "assistant".to_string(),
                    content: if text.is_empty() { None } else { Some(text) },
                    reasoning_content: None,
                    tool_calls: if tool_calls.is_empty() {
                        None
                    } else {
                        Some(tool_calls)
                    },
                },
            }],
            usage,
        })
    }

    /// Issue one Responses API call.
    fn chat_once(
        &self,
        req: &ChatRequest,
    ) -> Result<(ChatResponse, serde_json::Value), String> {
        let body_value = self.translate_request(req);
        let body = serde_json::to_string(&body_value)
            .map_err(|e| format!("serialise request: {e}"))?;

        let mut child = Command::new(CURL_BIN)
            .arg("-sS")
            .arg("--fail-with-body")
            .arg("-X")
            .arg("POST")
            .arg(&self.endpoint)
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
        let parsed = Self::translate_response(&raw)?;
        Ok((parsed, raw))
    }
}

impl LlmBackend for CodexBackend {
    fn chat(
        &self,
        req: &ChatRequest,
    ) -> Result<(ChatResponse, serde_json::Value), String> {
        match self.chat_once(req) {
            Ok(r) => Ok(r),
            Err(first) => {
                eprintln!("[codex] first attempt failed: {first}; retrying in 5s");
                std::thread::sleep(std::time::Duration::from_secs(5));
                self.chat_once(req)
                    .map_err(|second| format!("first error: {first}; retry error: {second}"))
            }
        }
    }
    fn provider_tag(&self) -> &'static str {
        "codex"
    }
    fn model_id(&self) -> &str {
        &self.model
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::llm::{ChatMessage, FunctionDef, ToolDef};

    #[test]
    fn translate_request_plain_chat() {
        let backend = CodexBackend::new();
        let req = ChatRequest {
            model: "ignored".to_string(),
            messages: vec![
                ChatMessage::system("you are a tester"),
                ChatMessage::user("hello"),
            ],
            tools: None,
            tool_choice: None,
            max_tokens: 4096,
            temperature: 0.0,
        };
        let body = backend.translate_request(&req);
        assert_eq!(body["model"], "gpt-5.5");
        let input = body["input"].as_array().unwrap();
        assert_eq!(input.len(), 2);
        assert_eq!(input[0]["role"], "system");
        assert_eq!(input[0]["content"], "you are a tester");
        assert_eq!(input[1]["role"], "user");
        assert_eq!(input[1]["content"], "hello");
        assert!(body.get("tools").is_none());
    }

    #[test]
    fn translate_request_with_tools() {
        let backend = CodexBackend::new();
        let req = ChatRequest {
            model: "ignored".to_string(),
            messages: vec![ChatMessage::user("ping")],
            tools: Some(vec![ToolDef {
                kind: "function".to_string(),
                function: FunctionDef {
                    name: "ping".to_string(),
                    description: "send a ping".to_string(),
                    parameters: serde_json::json!({"type": "object", "properties": {}}),
                },
            }]),
            tool_choice: Some("auto".to_string()),
            max_tokens: 4096,
            temperature: 0.0,
        };
        let body = backend.translate_request(&req);
        let tools = body["tools"].as_array().unwrap();
        assert_eq!(tools.len(), 1);
        assert_eq!(tools[0]["type"], "function");
        assert_eq!(tools[0]["name"], "ping");
        assert_eq!(tools[0]["description"], "send a ping");
        assert_eq!(body["tool_choice"], "auto");
    }

    #[test]
    fn translate_request_round_trips_tool_calls() {
        let backend = CodexBackend::new();
        let mut assistant = ChatMessage {
            role: "assistant".to_string(),
            content: Some("I will call the tool".to_string()),
            tool_calls: Some(vec![ToolCall {
                id: "call_123".to_string(),
                kind: "function".to_string(),
                function: ToolCallFunction {
                    name: "ping".to_string(),
                    arguments: "{}".to_string(),
                },
            }]),
            tool_call_id: None,
        };
        // suppress an "unused mut" warning when serde feature flags shift
        assistant.role = assistant.role.clone();

        let req = ChatRequest {
            model: "ignored".to_string(),
            messages: vec![
                ChatMessage::user("call ping"),
                assistant,
                ChatMessage::tool("call_123", "pong"),
            ],
            tools: None,
            tool_choice: None,
            max_tokens: 4096,
            temperature: 0.0,
        };
        let body = backend.translate_request(&req);
        let input = body["input"].as_array().unwrap();
        // Expect: user text, assistant text, function_call, function_call_output.
        assert_eq!(input.len(), 4);
        assert_eq!(input[0]["role"], "user");
        assert_eq!(input[1]["role"], "assistant");
        assert_eq!(input[1]["content"], "I will call the tool");
        assert_eq!(input[2]["type"], "function_call");
        assert_eq!(input[2]["call_id"], "call_123");
        assert_eq!(input[2]["name"], "ping");
        assert_eq!(input[2]["arguments"], "{}");
        assert_eq!(input[3]["type"], "function_call_output");
        assert_eq!(input[3]["call_id"], "call_123");
        assert_eq!(input[3]["output"], "pong");
    }

    #[test]
    fn translate_response_plain_text() {
        let raw = serde_json::json!({
            "output": [
                {
                    "type": "message",
                    "role": "assistant",
                    "content": [
                        {"type": "output_text", "text": "Hello, world."}
                    ]
                },
                {"type": "reasoning", "summary": []}
            ],
            "usage": {
                "input_tokens": 10,
                "output_tokens": 5,
                "total_tokens": 15
            }
        });
        let resp = CodexBackend::translate_response(&raw).unwrap();
        assert_eq!(resp.choices.len(), 1);
        assert_eq!(resp.choices[0].finish_reason.as_deref(), Some("stop"));
        assert_eq!(
            resp.choices[0].message.content.as_deref(),
            Some("Hello, world.")
        );
        assert!(resp.choices[0].message.tool_calls.is_none());
        assert_eq!(resp.usage.prompt_tokens, 10);
        assert_eq!(resp.usage.completion_tokens, 5);
        assert_eq!(resp.usage.total_tokens, 15);
    }

    #[test]
    fn translate_response_with_function_call() {
        let raw = serde_json::json!({
            "output": [
                {
                    "type": "message",
                    "role": "assistant",
                    "content": [{"type": "output_text", "text": "calling ping"}]
                },
                {
                    "type": "function_call",
                    "call_id": "fc_42",
                    "name": "ping",
                    "arguments": "{\"x\":1}"
                }
            ],
            "usage": {"input_tokens": 8, "output_tokens": 4, "total_tokens": 12}
        });
        let resp = CodexBackend::translate_response(&raw).unwrap();
        assert_eq!(resp.choices[0].finish_reason.as_deref(), Some("tool_calls"));
        assert_eq!(
            resp.choices[0].message.content.as_deref(),
            Some("calling ping")
        );
        let calls = resp.choices[0].message.tool_calls.as_ref().unwrap();
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].id, "fc_42");
        assert_eq!(calls[0].function.name, "ping");
        assert_eq!(calls[0].function.arguments, "{\"x\":1}");
    }

    #[test]
    fn translate_response_missing_output_is_error() {
        let raw = serde_json::json!({"detail": "boom"});
        let err = CodexBackend::translate_response(&raw).unwrap_err();
        assert!(err.contains("missing/non-array"));
    }
}
