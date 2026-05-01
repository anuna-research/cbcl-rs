//! backends: per-provider [`LlmBackend`](crate::llm::LlmBackend) implementations.
//!
//! - [`claude`] — Anthropic Messages API (`claude-sonnet-4-6`).
//! - [`openai`] — OpenAI chat-completions API (`gpt-4.1`).
//! - [`codex`] — OpenAI Responses API via local Codex proxy (`gpt-5.5`).
//!
//! The legacy GLM-5.1 backend lives at [`crate::glm::GlmClient`] (with
//! its alias `GlmBackend`); these new modules add the remaining
//! providers used by `IMPL-arena-evals`'s tab:mcp-attacks columns.
//!
//! All backends shell out to `/usr/bin/curl` (NFR-1112: no new deps)
//! and retry once on transport / 5xx errors before propagating.

pub mod claude;
pub mod codex;
pub mod openai;

pub use claude::ClaudeBackend;
pub use codex::CodexBackend;
pub use openai::OpenAIBackend;
