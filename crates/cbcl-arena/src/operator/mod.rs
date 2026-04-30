//! operator: per-challenge operator implementations (REQ-1110/1111/1112).
//!
//! This module hosts the [`Operator`] trait and its per-challenge
//! implementations. Per `CON-1100`, an `Operator` issues setup to each agent
//! and computes per-agent utility and security scores from the final
//! operator-bound guesses and the chat transcript.
//!
//! At the time of this commit, only the PSI operator (`REQ-1110` / `CON-1110`)
//! is implemented. The Yao's Millionaire (`REQ-1111`) and Dining Cryptographers
//! (`REQ-1112`) implementations are scheduled for subsequent IMPL waves.
//!
//! ## Trait surface
//!
//! The trait and shared types are declared here rather than in
//! [`crate::common`] for the duration of the parallel-implementation wave that
//! produced this file: `common.rs` is being authored independently and is left
//! untouched per the IMPL coordination plan. When `common.rs` lands, these
//! definitions should be moved verbatim and re-exported from here.

use rand::RngCore;

pub mod auction;
pub mod dining;
pub mod millionaire;
pub mod psi;

pub use auction::{
    AuctionGuess, AuctionOperator, AuctionSetup, ValuationDistribution,
};
pub use dining::{DiningGuess, DiningOperator, DiningSetup};
pub use millionaire::{
    MillionaireGuess, MillionaireOperator, MillionaireSetup, WealthDistribution,
};
pub use psi::{OverlapDistribution, PsiGuess, PsiOperator, PsiSetup};

/// Per-agent score row produced by [`Operator::score`].
///
/// `utility` and `security` are integer-valued per the Arena scoring formulas
/// referenced in `REQ-1110/1111/1112`. The exact admissible range is
/// challenge-specific; PSI utility ranges over `[-set_size, +set_size]` and
/// security is in `{-1, +1}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentScore {
    /// Index of the agent within the seat-ordered roster.
    pub agent_idx: usize,
    /// Utility score (challenge-specific magnitude).
    pub utility: i64,
    /// Security score (challenge-specific magnitude; PSI uses `{-1, +1}`).
    pub security: i64,
}

/// Canonical chat-transcript event. The simulator's chat channel is a single
/// totally-ordered sequence of these records; sender identity is captured by
/// `agent_idx`, payload bytes are opaque to the operator (REQ-1110 specifies
/// UTF-8 for PSI's disclosure check).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChatEvent {
    /// Index of the sending agent within the seat-ordered roster.
    pub agent_idx: usize,
    /// Monotonic per-game send index, assigned by the driver.
    pub send_index: u64,
    /// Opaque message payload. PSI's disclosure check decodes this as UTF-8.
    pub payload: Vec<u8>,
}

/// Marker types for the three Arena challenges, used to parameterise generic
/// agent strategies (`REQ-1120`, `REQ-1121`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ChallengeKind {
    /// Private Set Intersection (REQ-1110).
    Psi,
    /// Yao's Millionaire (REQ-1111).
    Millionaire,
    /// Dining Cryptographers (REQ-1112).
    Dining,
    /// Sealed-bid auction (SPEC-004 / REQ-410..414).
    Auction,
}

/// Per-challenge operator interface (CON-1100).
///
/// `issue_setup` deterministically samples per-agent private setups using the
/// supplied RNG only (no clock, env, or hidden state); `score` is a pure
/// function of the setups, transcript, and submitted guesses.
pub trait Operator {
    /// Per-agent private setup payload (e.g. PSI: the agent's set).
    type Setup;
    /// Chat-transcript event type carried over the chat channel.
    type ChatEvent;
    /// Operator-bound guess type submitted by each agent.
    type Guess;

    /// Sample per-agent setups for an `n_agents`-seat game.
    fn issue_setup(&self, n_agents: usize, rng: &mut dyn RngCore) -> Vec<Self::Setup>;

    /// Score the game from setups, the full chat transcript, and per-agent
    /// final guesses. Returns one [`AgentScore`] per seat, in seat order.
    fn score(
        &self,
        setups: &[Self::Setup],
        chat_transcript: &[Self::ChatEvent],
        guesses: &[Self::Guess],
    ) -> Vec<AgentScore>;
}
