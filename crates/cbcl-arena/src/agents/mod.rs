//! agents: CBCL-disciplined and Vanilla NL-chat agent strategies
//! (REQ-1120 / REQ-1121).
//!
//! At the time of this commit only the CBCL-disciplined agent (`REQ-1120` /
//! `CON-1120`) is implemented; the Vanilla NL-chat agent (`REQ-1121`) is
//! scheduled for a subsequent IMPL wave.
//!
//! ## Trait surface
//!
//! The [`Agent`] trait below mirrors the interface declared in CON-1100. It
//! is hosted here rather than in [`crate::common`] for the duration of the
//! parallel-implementation wave that produced this file: `common.rs` is being
//! authored independently and is left untouched per the IMPL coordination
//! plan. When `common.rs` lands these definitions should move there and be
//! re-exported from this module.

use rand::RngCore;

pub mod cbcl;
pub mod vanilla;

/// Per-challenge agent interface (CON-1100).
///
/// `play` is the agent's per-game entry point. The driver passes the
/// agent-specific private setup, an inbound channel iterator yielding chat
/// events authored by other seats, and an outbound `FnMut` callback the
/// agent invokes to send chat events. The agent returns its
/// operator-bound guess at end-of-game.
pub trait Agent {
    /// Per-agent private setup payload (e.g. PSI: the agent's set).
    type Setup;
    /// Chat-transcript event type carried over the chat channel.
    type ChatEvent;
    /// Operator-bound guess type submitted at end-of-game.
    type Guess;

    /// Run one game from start to operator-bound submission.
    fn play(
        &mut self,
        setup: Self::Setup,
        in_channel: &mut dyn Iterator<Item = Self::ChatEvent>,
        out_channel: &mut dyn FnMut(Self::ChatEvent),
        rng: &mut dyn RngCore,
    ) -> Self::Guess;
}
