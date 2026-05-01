//! PSI disciplined live-LLM seat (legacy alias over the generic seat).
//!
//! `GlmDisciplinedSeat` is the historical name of the PSI-only seat that
//! exposed the dialect's five performatives as OpenAI-style function
//! tools. Under [`crate::llm`]'s trait-protocol-adapter refactor it is
//! now a type alias for the generic
//! [`DisciplinedSeat`]`<`[`PsiDisciplinedAdapter`]`>` driving a
//! `Box<dyn LlmBackend>` (typically a [`crate::glm::GlmClient`]).
//!
//! Use [`new_glm_disciplined_seat`] to build one — preserves the
//! original `GlmDisciplinedSeat::new(client, path, trial, max_turns)`
//! call site shape (the inherent-impl form is no longer available
//! because the underlying type is a generic alias).

use std::path::PathBuf;

use crate::llm::{DisciplinedSeat, LlmBackend, PsiDisciplinedAdapter};

use super::GlmClient;

/// Disciplined PSI live-LLM seat. Type alias over the generic
/// [`DisciplinedSeat`] parameterised by [`PsiDisciplinedAdapter`].
pub type GlmDisciplinedSeat = DisciplinedSeat<PsiDisciplinedAdapter>;

/// Construct a disciplined PSI seat against any [`LlmBackend`].
/// Conventional thread / sender labels are `("psi-game", "alice")`,
/// matching the existing transcripts.
pub fn new_disciplined_seat(
    backend: Box<dyn LlmBackend>,
    transcript_path: PathBuf,
    trial: u32,
    max_turns: u32,
) -> GlmDisciplinedSeat {
    DisciplinedSeat::new(
        backend,
        PsiDisciplinedAdapter::new("psi-game", "alice"),
        transcript_path,
        trial,
        max_turns,
    )
}

/// GLM-flavoured wrapper over [`new_disciplined_seat`] kept as the
/// historical entry point. New callers should use
/// [`new_disciplined_seat`] with a `Box<dyn LlmBackend>` directly.
pub fn new_glm_disciplined_seat(
    client: GlmClient,
    transcript_path: PathBuf,
    trial: u32,
    max_turns: u32,
) -> GlmDisciplinedSeat {
    new_disciplined_seat(Box::new(client), transcript_path, trial, max_turns)
}
