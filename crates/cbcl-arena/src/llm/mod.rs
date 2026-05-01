//! llm: provider-neutral live-LLM façade.
//!
//! Houses the per-operator [`ProtocolAdapter`] trait, the per-provider
//! [`LlmBackend`] implementations, and the generic [`DisciplinedSeat`]
//! type that these compose into. The original PSI-only `GlmDisciplinedSeat`
//! at [`crate::glm::disciplined`] is now a thin alias over
//! `DisciplinedSeat<PsiDisciplinedAdapter>`; see that module for the
//! constructor that builds the seat against a [`crate::glm::GlmClient`].
//!
//! ## Module map
//!
//! - [`adapter`] — `ProtocolAdapter` trait + `ToolKind` / `ToolDispatch`.
//! - [`seat`] — generic `DisciplinedSeat<A>` (object-safe `Box<dyn
//!   LlmBackend>` for the backend axis).
//! - [`adapters`] — per-operator adapter impls (currently only PSI;
//!   Yao / Auction / Dining / Ultimatum land under
//!   `IMPL-arena-evals`).
//!
//! Provider-neutral types ([`ChatRequest`], [`ChatResponse`],
//! [`ChatMessage`], [`ToolDef`], [`ToolCall`], …) and the [`LlmBackend`]
//! trait itself currently live in [`crate::glm`] and are re-exported
//! here. Once the trait-extraction wave finishes, `crate::glm` becomes
//! the inverse shim.
//!
//! ## Object safety
//!
//! [`LlmBackend`] is object-safe so the active backend can be selected
//! at runtime (`Box<dyn LlmBackend>`). [`ProtocolAdapter`] carries
//! associated `Setup` / `Guess` types and is therefore generic on the
//! seat (`DisciplinedSeat<A>`), not `dyn`. The split lets the CLI
//! choose a backend at runtime without forcing every seat to carry a
//! backend generic.
//!
//! ```
//! use cbcl_arena::llm::LlmBackend;
//! fn _take(_b: Box<dyn LlmBackend>) {}
//! ```

pub mod adapter;
pub mod adapters;
pub mod backends;
pub mod seat;

pub use adapter::{tool_reply, ProtocolAdapter, ToolDispatch, ToolKind};
pub use adapters::{
    AuctionDisciplinedAdapter, DiningDisciplinedAdapter, PsiDisciplinedAdapter,
    YaoDisciplinedAdapter,
};
pub use backends::{ClaudeBackend, CodexBackend, OpenAIBackend};
pub use seat::DisciplinedSeat;

pub use crate::glm::{
    append_transcript, transcript_path, utc_now_iso, ChatMessage, ChatRequest, ChatResponse,
    Choice, ChoiceMessage, FunctionDef, GlmBackend, GlmClient, LlmBackend, ToolCall,
    ToolCallFunction, ToolDef, Usage, CURL_BIN, ENDPOINT, MODEL,
};
