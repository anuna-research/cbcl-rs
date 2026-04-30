//! attackers: per-challenge attack-pattern registry (REQ-1130 / REQ-1131).
//!
//! Each challenge has three families:
//!
//! - **Honest-cooperative** — a single benign reference pattern.
//! - **Malicious-published** — 4–6 patterns each citing a public Arena
//!   game ID at SPEC-011's freeze date (2026-04-30).
//! - **Malicious-novel** — 4–6 originally-authored patterns, each
//!   documented under `crates/cbcl-arena/attackers/novel/<chal>-<name>.md`.
//!
//! Patterns implement [`AttackPattern`] (CON-1130). Patterns are
//! deterministic given setup + transcript history + a seeded RNG.

use rand::RngCore;

use crate::operator::ChatEvent;
use crate::operator::dining::{DiningGuess, DiningSetup};
use crate::operator::millionaire::{MillionaireGuess, MillionaireSetup};
use crate::operator::psi::{PsiGuess, PsiSetup};

pub mod psi;
pub mod millionaire;
pub mod dining;

/// Category of an attacker pattern (REQ-1130).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AttackCategory {
    /// Benign reference pattern (no attack).
    Honest,
    /// Citation-grounded pattern reproducing a published Arena attack.
    Published,
    /// Originally-authored pattern.
    Novel,
}

/// Per-challenge interface for an attacker (CON-1130).
///
/// `Setup` is the operator-issued private setup payload. `Guess` is the
/// operator-bound submission type. Implementations are deterministic given
/// the supplied RNG.
pub trait AttackPattern {
    /// Per-challenge private setup payload.
    type Setup;
    /// Operator-bound guess type.
    type Guess;

    /// Pattern's stable display name (e.g. `"direct-ask"`).
    fn name(&self) -> &'static str;

    /// Pattern category.
    fn category(&self) -> AttackCategory;

    /// Citation for `Published` patterns; `None` for `Honest` and `Novel`.
    fn source_citation(&self) -> Option<&'static str>;

    /// Ingest the operator's setup. Called once at game start.
    fn ingest_setup(&mut self, setup: Self::Setup);

    /// Per-step entry point. Given an inbound iterator and an outbound
    /// emission callback, advance the attacker. Returns `true` when the
    /// attacker has nothing more to do.
    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> bool;

    /// Final operator-bound guess.
    fn final_guess(&self) -> Self::Guess;
}

// -----------------------------------------------------------------------
// Per-challenge object-safe trait aliases.
//
// `AttackPattern` is generic over `Setup` / `Guess` and so is not
// directly object-safe. We narrow it per-challenge so that the registry
// can store `Box<dyn ChallengePattern>` slots (CON-1130).
// -----------------------------------------------------------------------

/// Object-safe per-challenge attacker pattern for PSI.
pub trait PsiPattern:
    AttackPattern<Setup = PsiSetup, Guess = PsiGuess> + Send
{
}
impl<T> PsiPattern for T where
    T: AttackPattern<Setup = PsiSetup, Guess = PsiGuess> + Send
{
}

/// Object-safe per-challenge attacker pattern for Yao's Millionaire.
pub trait MillionairePattern:
    AttackPattern<Setup = MillionaireSetup, Guess = MillionaireGuess> + Send
{
}
impl<T> MillionairePattern for T where
    T: AttackPattern<Setup = MillionaireSetup, Guess = MillionaireGuess> + Send
{
}

/// Object-safe per-challenge attacker pattern for Dining Cryptographers.
pub trait DiningPattern:
    AttackPattern<Setup = DiningSetup, Guess = DiningGuess> + Send
{
}
impl<T> DiningPattern for T where
    T: AttackPattern<Setup = DiningSetup, Guess = DiningGuess> + Send
{
}

/// Per-challenge slot of patterns grouped by category (CON-1130).
pub struct PerChallenge<T: ?Sized> {
    /// Honest-cooperative reference patterns (typically exactly one).
    pub honest: Vec<Box<T>>,
    /// Malicious-published patterns; each carries a citation.
    pub published: Vec<Box<T>>,
    /// Malicious-novel patterns; each documented under
    /// `crates/cbcl-arena/attackers/novel/<chal>-<name>.md`.
    pub novel: Vec<Box<T>>,
}

impl<T: ?Sized> Default for PerChallenge<T> {
    fn default() -> Self {
        Self { honest: Vec::new(), published: Vec::new(), novel: Vec::new() }
    }
}

/// Top-level attacker registry (CON-1130). Each per-challenge slot is
/// populated by the corresponding `<chal>::registry()` constructor.
pub struct AttackerRegistry {
    /// PSI attack patterns.
    pub psi: PerChallenge<dyn PsiPattern>,
    /// Yao's Millionaire attack patterns.
    pub millionaire: PerChallenge<dyn MillionairePattern>,
    /// Dining Cryptographers attack patterns.
    pub dining: PerChallenge<dyn DiningPattern>,
}

/// Construct the full attacker registry. Each per-challenge submodule
/// owns its own population — see [`millionaire::registry`] etc.
pub fn registry() -> AttackerRegistry {
    AttackerRegistry {
        psi: psi::registry(),
        millionaire: millionaire::registry(),
        dining: dining::registry(),
    }
}
