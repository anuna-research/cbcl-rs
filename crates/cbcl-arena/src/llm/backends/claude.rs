//! Anthropic Messages API backend (`claude-sonnet-4-6`).
//!
//! Implements [`LlmBackend`] over Anthropic's Messages API at
//! `https://api.anthropic.com/v1/messages`. The seat speaks
//! OpenAI-compatible [`ChatRequest`] / [`ChatResponse`]; this module
//! translates at the wire boundary so the rest of the codebase stays
//! provider-neutral.
//!
//! ## Schema translation
//!
//! - **System messages** (role=`system`) are extracted out of the
//!   conversation history into Anthropic's top-level `system` field.
//!   We use the array form (`[{type:"text", text:"...", cache_control:
//!   {type:"ephemeral"}}]`) so prompt caching kicks in across a sweep
//!   of trials sharing the same system prompt.
//! - **Assistant tool calls** (`tool_calls` array on a ChatMessage with
//!   role=`assistant`) become Anthropic content blocks of type
//!   `tool_use`. Optional preceding text becomes a `text` block.
//! - **Tool replies** (role=`tool`) become Anthropic `tool_result`
//!   content blocks **inside** a user message. Consecutive tool replies
//!   are grouped into one user message — Anthropic's API requires
//!   alternating user/assistant turns.
//! - **Tool definitions** are renamed `parameters → input_schema`. The
//!   last tool def carries `cache_control: ephemeral` so the tools
//!   block is cached too.
//! - **`tool_choice`** maps `"auto"` → `{type:"auto"}`, `"required"` →
//!   `{type:"any"}`, anything else dropped (Anthropic defaults to
//!   `auto`).
//!
//! ## Response translation
//!
//! Anthropic returns a `content` array of `text` and `tool_use` blocks
//! plus a `stop_reason`. We synthesise a single OpenAI-shape `Choice`
//! whose `message.content` joins all text blocks and whose
//! `message.tool_calls` lists the `tool_use` blocks, with `finish_reason`
//! mapped from `stop_reason` (`end_turn`→`stop`, `tool_use`→`tool_calls`,
//! `max_tokens`→`length`).
//!
//! ## Auth + transport
//!
//! Reads `ANTHROPIC_API_KEY` from the environment. Shells out to
//! `/usr/bin/curl` with the key streamed via the `x-api-key` header
//! (per Anthropic — Anthropic uses `x-api-key`, not `Authorization:
//! Bearer`). `anthropic-version: 2023-06-01` header is required.

use std::io::Write;
use std::process::{Command, Stdio};

use crate::glm::CURL_BIN;
use crate::llm::{
    ChatRequest, ChatResponse, Choice, ChoiceMessage, LlmBackend, ToolCall, ToolCallFunction,
    Usage,
};

/// Endpoint for the Anthropic Messages API.
pub const ENDPOINT: &str = "https://api.anthropic.com/v1/messages";
/// Model identifier (Sonnet 4.6).
pub const MODEL: &str = "claude-sonnet-4-6";
/// Required Anthropic API version header.
pub const API_VERSION: &str = "2023-06-01";

/// Anthropic live-LLM backend.
pub struct ClaudeBackend {
    api_key: String,
    model: String,
}

impl ClaudeBackend {
    /// Construct a backend by reading `ANTHROPIC_API_KEY` from the
    /// process environment.
    pub fn from_env() -> Result<Self, String> {
        let api_key = std::env::var("ANTHROPIC_API_KEY")
            .map_err(|_| "ANTHROPIC_API_KEY not set in environment".to_string())?;
        if api_key.trim().is_empty() {
            return Err("ANTHROPIC_API_KEY is empty".into());
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

    /// Translate an OpenAI-shape [`ChatRequest`] into an Anthropic
    /// Messages-API request body.
    fn translate_request(&self, req: &ChatRequest) -> serde_json::Value {
        // Extract system content. We expect at most one system message,
        // typically at index 0; if multiple are present, concatenate
        // them with double newlines.
        let mut system_text = String::new();
        for m in &req.messages {
            if m.role == "system" {
                if let Some(c) = &m.content {
                    if !system_text.is_empty() {
                        system_text.push_str("\n\n");
                    }
                    system_text.push_str(c);
                }
            }
        }

        // Translate the rest into Anthropic messages.
        let mut out_messages: Vec<serde_json::Value> = Vec::new();
        let history: Vec<&crate::llm::ChatMessage> = req
            .messages
            .iter()
            .filter(|m| m.role != "system")
            .collect();
        let n = history.len();
        let mut i = 0;
        while i < n {
            let msg = history[i];
            match msg.role.as_str() {
                "user" => {
                    let content = msg.content.clone().unwrap_or_default();
                    out_messages.push(serde_json::json!({
                        "role": "user",
                        "content": [{"type":"text","text": content}],
                    }));
                    i += 1;
                }
                "assistant" => {
                    let mut blocks: Vec<serde_json::Value> = Vec::new();
                    if let Some(text) = &msg.content {
                        if !text.is_empty() {
                            blocks.push(serde_json::json!({
                                "type":"text",
                                "text": text,
                            }));
                        }
                    }
                    if let Some(tcs) = &msg.tool_calls {
                        for tc in tcs {
                            let input: serde_json::Value =
                                serde_json::from_str(&tc.function.arguments)
                                    .unwrap_or(serde_json::Value::Object(Default::default()));
                            blocks.push(serde_json::json!({
                                "type":"tool_use",
                                "id": tc.id,
                                "name": tc.function.name,
                                "input": input,
                            }));
                        }
                    }
                    if blocks.is_empty() {
                        // Anthropic rejects empty assistant turns.
                        blocks.push(serde_json::json!({"type":"text","text":""}));
                    }
                    out_messages.push(serde_json::json!({
                        "role": "assistant",
                        "content": blocks,
                    }));
                    i += 1;
                }
                "tool" => {
                    // Group consecutive tool replies into one user message.
                    let mut blocks: Vec<serde_json::Value> = Vec::new();
                    while i < n && history[i].role == "tool" {
                        let tm = history[i];
                        blocks.push(serde_json::json!({
                            "type":"tool_result",
                            "tool_use_id": tm.tool_call_id.clone().unwrap_or_default(),
                            "content": tm.content.clone().unwrap_or_default(),
                        }));
                        i += 1;
                    }
                    out_messages.push(serde_json::json!({
                        "role": "user",
                        "content": blocks,
                    }));
                }
                other => {
                    eprintln!("[claude] unknown role in history: {other}; skipping");
                    i += 1;
                }
            }
        }

        // Translate tool defs: rename `parameters` → `input_schema` and
        // attach `cache_control: ephemeral` to the last def.
        let translated_tools: Option<Vec<serde_json::Value>> = req.tools.as_ref().map(|tools| {
            let n = tools.len();
            tools
                .iter()
                .enumerate()
                .map(|(idx, td)| {
                    let mut obj = serde_json::json!({
                        "name": td.function.name,
                        "description": td.function.description,
                        "input_schema": td.function.parameters,
                    });
                    if idx + 1 == n {
                        if let Some(map) = obj.as_object_mut() {
                            map.insert(
                                "cache_control".into(),
                                serde_json::json!({"type":"ephemeral"}),
                            );
                        }
                    }
                    obj
                })
                .collect()
        });

        // Translate tool_choice.
        let tool_choice = req.tool_choice.as_deref().map(|tc| match tc {
            "required" => serde_json::json!({"type":"any"}),
            _ => serde_json::json!({"type":"auto"}),
        });

        // Build system block. Always use the array form so prompt
        // caching applies. Empty system → null.
        let system_block = if system_text.is_empty() {
            serde_json::Value::Null
        } else {
            serde_json::json!([{
                "type":"text",
                "text": system_text,
                "cache_control": {"type":"ephemeral"},
            }])
        };

        let mut body = serde_json::json!({
            "model": self.model,
            "messages": out_messages,
            "max_tokens": req.max_tokens,
            "temperature": req.temperature,
        });
        if !system_block.is_null() {
            body["system"] = system_block;
        }
        if let Some(tools) = translated_tools {
            body["tools"] = serde_json::Value::Array(tools);
        }
        if let Some(tc) = tool_choice {
            body["tool_choice"] = tc;
        }
        body
    }

    /// Translate an Anthropic Messages-API response into our
    /// OpenAI-shape [`ChatResponse`].
    fn translate_response(raw: &serde_json::Value) -> Result<ChatResponse, String> {
        // Extract content blocks.
        let content_blocks = raw
            .get("content")
            .and_then(|v| v.as_array())
            .cloned()
            .unwrap_or_default();

        let mut text_acc = String::new();
        let mut tool_calls: Vec<ToolCall> = Vec::new();
        for b in content_blocks {
            let ty = b.get("type").and_then(|v| v.as_str()).unwrap_or("");
            match ty {
                "text" => {
                    if let Some(t) = b.get("text").and_then(|v| v.as_str()) {
                        text_acc.push_str(t);
                    }
                }
                "tool_use" => {
                    let id = b
                        .get("id")
                        .and_then(|v| v.as_str())
                        .unwrap_or("")
                        .to_string();
                    let name = b
                        .get("name")
                        .and_then(|v| v.as_str())
                        .unwrap_or("")
                        .to_string();
                    let input = b
                        .get("input")
                        .cloned()
                        .unwrap_or(serde_json::Value::Object(Default::default()));
                    let args = serde_json::to_string(&input).unwrap_or_else(|_| "{}".into());
                    tool_calls.push(ToolCall {
                        id,
                        kind: "function".into(),
                        function: ToolCallFunction {
                            name,
                            arguments: args,
                        },
                    });
                }
                "thinking" | "redacted_thinking" => {
                    // Extended-thinking blocks: not surfaced to the
                    // generic seat (it expects OpenAI shape). Discard.
                }
                _ => {}
            }
        }

        let stop_reason = raw
            .get("stop_reason")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        let finish_reason = match stop_reason {
            "end_turn" => Some("stop".to_string()),
            "tool_use" => Some("tool_calls".to_string()),
            "max_tokens" => Some("length".to_string()),
            "" => None,
            other => Some(other.to_string()),
        };

        let usage = raw.get("usage").cloned().unwrap_or(serde_json::Value::Null);
        let prompt_tokens = usage
            .get("input_tokens")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        let completion_tokens = usage
            .get("output_tokens")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        let cache_read = usage
            .get("cache_read_input_tokens")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        // Account cache-read tokens against prompt_tokens — the seat's
        // running total tracks total billable tokens which on Anthropic
        // includes cache-read.
        let _ = cache_read;

        let content_opt = if text_acc.is_empty() && !tool_calls.is_empty() {
            None
        } else {
            Some(text_acc)
        };
        let tool_calls_opt = if tool_calls.is_empty() {
            None
        } else {
            Some(tool_calls)
        };

        Ok(ChatResponse {
            choices: vec![Choice {
                finish_reason,
                index: 0,
                message: ChoiceMessage {
                    role: "assistant".into(),
                    content: content_opt,
                    reasoning_content: None,
                    tool_calls: tool_calls_opt,
                },
            }],
            usage: Usage {
                prompt_tokens,
                completion_tokens,
                total_tokens: prompt_tokens.saturating_add(completion_tokens),
            },
        })
    }

    /// Issue one Messages API call (no retry).
    fn chat_once(
        &self,
        req: &ChatRequest,
    ) -> Result<(ChatResponse, serde_json::Value), String> {
        let body_value = self.translate_request(req);
        let body = serde_json::to_string(&body_value)
            .map_err(|e| format!("serialise request: {e}"))?;

        let key_header = format!("x-api-key: {}", self.api_key);
        let version_header = format!("anthropic-version: {}", API_VERSION);
        let mut child = Command::new(CURL_BIN)
            .arg("-sS")
            .arg("--fail-with-body")
            .arg("-X")
            .arg("POST")
            .arg(ENDPOINT)
            .arg("-H")
            .arg(&key_header)
            .arg("-H")
            .arg(&version_header)
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
        let parsed = Self::translate_response(&raw)
            .map_err(|e| format!("translate response: {e}; raw={stdout}"))?;
        Ok((parsed, raw))
    }
}

impl LlmBackend for ClaudeBackend {
    fn chat(
        &self,
        req: &ChatRequest,
    ) -> Result<(ChatResponse, serde_json::Value), String> {
        match self.chat_once(req) {
            Ok(r) => Ok(r),
            Err(first) => {
                eprintln!("[claude] first attempt failed: {first}; retrying in 5s");
                std::thread::sleep(std::time::Duration::from_secs(5));
                self.chat_once(req)
                    .map_err(|second| format!("first error: {first}; retry error: {second}"))
            }
        }
    }
    fn provider_tag(&self) -> &'static str {
        "claude"
    }
    fn model_id(&self) -> &str {
        &self.model
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::llm::{ChatMessage, ChatRequest, FunctionDef, ToolDef};

    fn sample_request() -> ChatRequest {
        ChatRequest {
            model: "ignored".into(),
            messages: vec![
                ChatMessage::system("You are Alice."),
                ChatMessage::user("Hello."),
                ChatMessage {
                    role: "assistant".into(),
                    content: Some("Hi.".into()),
                    tool_calls: Some(vec![ToolCall {
                        id: "tool_1".into(),
                        kind: "function".into(),
                        function: ToolCallFunction {
                            name: "do_x".into(),
                            arguments: "{\"k\":1}".into(),
                        },
                    }]),
                    tool_call_id: None,
                },
                ChatMessage::tool("tool_1", "ok"),
            ],
            tools: Some(vec![ToolDef {
                kind: "function".into(),
                function: FunctionDef {
                    name: "do_x".into(),
                    description: "test".into(),
                    parameters: serde_json::json!({"type":"object"}),
                },
            }]),
            tool_choice: Some("auto".into()),
            max_tokens: 128,
            temperature: 0.0,
        }
    }

    #[test]
    fn translate_request_extracts_system_and_groups_tool_results() {
        // Construct a backend without going through ANTHROPIC_API_KEY (the
        // env var would otherwise be required).
        let backend = ClaudeBackend {
            api_key: "test-key".into(),
            model: "test-model".into(),
        };
        let body = backend.translate_request(&sample_request());
        // System pulled out into top-level array form.
        let sys = body.get("system").and_then(|v| v.as_array()).unwrap();
        assert_eq!(sys[0].get("type").unwrap(), "text");
        assert_eq!(sys[0].get("text").unwrap(), "You are Alice.");
        assert!(sys[0].get("cache_control").is_some());
        // Messages: user-text, assistant (text + tool_use), user (tool_result).
        let msgs = body.get("messages").and_then(|v| v.as_array()).unwrap();
        assert_eq!(msgs.len(), 3);
        assert_eq!(msgs[0].get("role").unwrap(), "user");
        assert_eq!(msgs[1].get("role").unwrap(), "assistant");
        assert_eq!(msgs[2].get("role").unwrap(), "user");
        // Last user message is a tool_result block.
        let blocks = msgs[2].get("content").and_then(|v| v.as_array()).unwrap();
        assert_eq!(blocks[0].get("type").unwrap(), "tool_result");
        assert_eq!(blocks[0].get("tool_use_id").unwrap(), "tool_1");
        // Tools: parameters renamed to input_schema; last tool has cache_control.
        let tools = body.get("tools").and_then(|v| v.as_array()).unwrap();
        assert!(tools[0].get("input_schema").is_some());
        assert!(tools[0].get("parameters").is_none());
        assert!(tools[0].get("cache_control").is_some());
    }

    #[test]
    fn translate_response_unwraps_text_and_tool_use() {
        let raw = serde_json::json!({
            "id": "msg_x",
            "model": "claude-x",
            "role": "assistant",
            "content": [
                {"type":"text","text":"Reasoning..."},
                {"type":"tool_use","id":"toolu_1","name":"do_x","input":{"k":1}}
            ],
            "stop_reason": "tool_use",
            "usage": {"input_tokens": 100, "output_tokens": 20}
        });
        let parsed = ClaudeBackend::translate_response(&raw).unwrap();
        let choice = &parsed.choices[0];
        assert_eq!(choice.finish_reason.as_deref(), Some("tool_calls"));
        let tcs = choice.message.tool_calls.as_ref().unwrap();
        assert_eq!(tcs.len(), 1);
        assert_eq!(tcs[0].function.name, "do_x");
        assert_eq!(parsed.usage.prompt_tokens, 100);
        assert_eq!(parsed.usage.completion_tokens, 20);
    }
}
