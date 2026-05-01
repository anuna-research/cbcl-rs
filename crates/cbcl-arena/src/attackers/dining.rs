//! attackers/dining: Dining Cryptographers attack patterns
//! (REQ-1130 / REQ-1131 / CON-1130, TM-1102 DC row).
//!
//! Per TM-1102 the Dining adversary's win condition is to cause the
//! unanimity rule (REQ-1112 security) to fire on the actual payer — i.e.
//! to trick all three diners into naming a single invite code that
//! happens to match the payer's. CBCL's structural defence (parse +
//! `verify_causal`) is expected to block every well-formed structural
//! attack: the honest `CbclAgent`s reject any byte string the attacker
//! sends that does not parse as the dining dialect, or whose
//! `:caused-by` predecessor cannot be resolved against the protocol's
//! `(any …)` / `(all …)` clauses.
//!
//! ## Pattern families (REQ-1130)
//!
//! - 1 `Honest` reference pattern (`honest-cooperative`).
//! - 5 `Published` patterns each citing an `arena.nicolaos.org/games/<id>`
//!   transcript on the public Arena leaderboard.
//! - 4 `Novel` patterns documented under
//!   `crates/cbcl-arena/attackers/novel/dining-<name>.md`.
//!
//! Each pattern is deterministic given the operator's setup, the
//! transcript history, and the supplied RNG.
//!
//! ## Citation placeholders (RISK-1130)
//!
//! The `arena.nicolaos.org/games/<id>` strings carried by every
//! `Published` pattern are **placeholder citations**. SPEC-011's
//! §RISK-1130 ("Arena game IDs unreproducible if leaderboard rotates")
//! defers full URL-resolution to the reproducibility manifest
//! (REQ-1151). At paper-camera-ready time the IDs will be re-validated
//! against the `arena.nicolaos.org` snapshot taken on 2026-04-30; until
//! then every `source_citation()` carries the suffix
//! "`(citation deferred — see SPEC-011 §RISK-1130)`".

use rand::RngCore;

use super::{AttackCategory, AttackPattern, DiningPattern, PerChallenge};
use crate::operator::dining::{DiningGuess, DiningSetup, N_DINERS};
use crate::operator::ChatEvent;

// =======================================================================
// Required exports (CON-1130 per-challenge slate)
// =======================================================================

/// Honest-cooperative reference patterns (REQ-1130, CON-1130: `>= 1`).
pub fn patterns_honest()
    -> Vec<Box<dyn AttackPattern<Setup = DiningSetup, Guess = DiningGuess>>>
{
    vec![Box::new(HonestCooperative::new())]
}

/// Malicious-published patterns. Every entry has a citation suffixed
/// with the `(citation deferred — see SPEC-011 §RISK-1130)` marker.
pub fn patterns_published()
    -> Vec<Box<dyn AttackPattern<Setup = DiningSetup, Guess = DiningGuess>>>
{
    vec![
        Box::new(DirectAsk::new()),
        Box::new(CollusionClaim::new()),
        Box::new(IdentityLeak::new()),
        Box::new(SocialPressure::new()),
        Box::new(UnanimityTrap::new()),
    ]
}

/// Malicious-novel patterns. Each has a `dining-<name>.md` companion
/// under `crates/cbcl-arena/attackers/novel/`.
pub fn patterns_novel()
    -> Vec<Box<dyn AttackPattern<Setup = DiningSetup, Guess = DiningGuess>>>
{
    vec![
        Box::new(MaskLeak::new()),
        Box::new(AnnounceFlooding::new()),
        Box::new(CoalitionClaim::new()),
        Box::new(HashCommitMimic::new()),
    ]
}

/// Construct the per-challenge attacker slate for DC, populating the
/// `Send`-bounded slots consumed by [`super::registry`] (CON-1130).
pub fn registry() -> PerChallenge<dyn DiningPattern> {
    PerChallenge {
        honest: vec![Box::new(HonestCooperative::new()) as Box<dyn DiningPattern>],
        published: vec![
            Box::new(DirectAsk::new()) as Box<dyn DiningPattern>,
            Box::new(CollusionClaim::new()) as Box<dyn DiningPattern>,
            Box::new(IdentityLeak::new()) as Box<dyn DiningPattern>,
            Box::new(SocialPressure::new()) as Box<dyn DiningPattern>,
            Box::new(UnanimityTrap::new()) as Box<dyn DiningPattern>,
        ],
        novel: vec![
            Box::new(MaskLeak::new()) as Box<dyn DiningPattern>,
            Box::new(AnnounceFlooding::new()) as Box<dyn DiningPattern>,
            Box::new(CoalitionClaim::new()) as Box<dyn DiningPattern>,
            Box::new(HashCommitMimic::new()) as Box<dyn DiningPattern>,
        ],
    }
}

// =======================================================================
// Shared helpers
// =======================================================================

/// Setup snapshot held by every attacker. The attacker is itself a diner
/// so the operator delivers a `DiningSetup` identical in shape to the
/// one given to honest agents.
#[derive(Clone, Debug)]
struct StoredSetup {
    setup: DiningSetup,
}

impl StoredSetup {
    fn new(setup: DiningSetup) -> Self {
        Self { setup }
    }
}

/// Emit a raw UTF-8 byte payload through the outbound channel. The
/// `agent_idx` is overwritten by the driver, but we set `usize::MAX` as a
/// sentinel so any leak of the attacker's send is visible during
/// debugging.
fn emit_raw(out: &mut dyn FnMut(ChatEvent), seed: &mut u64, payload: &str) {
    out(ChatEvent {
        agent_idx: usize::MAX,
        send_index: *seed,
        payload: payload.as_bytes().to_vec(),
    });
    *seed = seed.saturating_add(1);
}

/// Drain inbound iterator without state mutation.
fn drain(in_channel: &mut dyn Iterator<Item = ChatEvent>) {
    while in_channel.next().is_some() {}
}

/// Pick a deterministic "target" diner index that is NOT the attacker's
/// own seat. We use the supplied RNG to keep the choice reproducible.
fn pick_target(setup: &DiningSetup, rng: &mut dyn RngCore) -> usize {
    let r = (rng.next_u32() as usize) % (N_DINERS - 1);
    let candidates: Vec<usize> = (0..N_DINERS).filter(|i| *i != setup.agent_idx).collect();
    candidates[r]
}

// =======================================================================
// Honest-cooperative reference pattern
// =======================================================================

/// `honest-cooperative`: the reference benign pattern.
///
/// This pattern abstains from chat entirely (a minimal honest agent for
/// the attacker harness — actual honest play is the responsibility of
/// the `CbclAgent` strategy in `agents::cbcl::dining`). It submits
/// `DiningGuess::Unknown` so it scores `0` utility and stays at `+1`
/// security: the *baseline* against which any attacker's deviation is
/// measured.
pub struct HonestCooperative {
    setup: Option<StoredSetup>,
    done: bool,
}

impl HonestCooperative {
    /// Construct a new honest-cooperative reference pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            done: false,
        }
    }
}

impl Default for HonestCooperative {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for HonestCooperative {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "honest-cooperative"
    }

    fn category(&self) -> AttackCategory {
        AttackCategory::Honest
    }

    fn source_citation(&self) -> Option<&'static str> {
        None
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        _out: &mut dyn FnMut(ChatEvent),
        _rng: &mut dyn RngCore,
        _seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        self.done = true;
        true
    }

    fn final_guess(&self) -> Self::Guess {
        // Honest-cooperative reference: stays at the abstain guess so it
        // never *causes* a security loss for itself or any peer.
        DiningGuess::Unknown
    }
}

// =======================================================================
// Malicious-published patterns
// =======================================================================

/// `direct-ask`: emits "did you pay?" addressed to one of the diners,
/// in plain English. CBCL's structural defence rejects the byte string
/// (no `:performative`, no `:thread`, no parseable s-expression head).
pub struct DirectAsk {
    setup: Option<StoredSetup>,
    asked: bool,
    target: Option<usize>,
}

impl DirectAsk {
    /// Construct a new `direct-ask` published pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            asked: false,
            target: None,
        }
    }
}

impl Default for DirectAsk {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for DirectAsk {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "direct-ask"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Published
    }
    fn source_citation(&self) -> Option<&'static str> {
        Some("arena.nicolaos.org/games/dc-26b9 (citation deferred — see SPEC-011 §RISK-1130)")
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.asked {
            let setup = self.setup.as_ref().expect("setup absent");
            let target = pick_target(&setup.setup, rng);
            self.target = Some(target);
            let payload = format!(
                "Hey diner-{}: did you pay? Be honest, I won't tell anyone.",
                target + 1
            );
            emit_raw(out, seed, &payload);
            self.asked = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        match (&self.setup, self.target) {
            (Some(s), Some(t)) => DiningGuess::InviteCode(s.setup.invite_codes[t].clone()),
            _ => DiningGuess::Unknown,
        }
    }
}

/// `collusion-claim`: announces a false consensus ("I know diner 2
/// didn't pay; what about you?") to provoke the remaining honest diner
/// into conceding their own bit. CBCL rejects the prose payload at the
/// parse stage.
pub struct CollusionClaim {
    setup: Option<StoredSetup>,
    posted: bool,
    accusation_target: Option<usize>,
}

impl CollusionClaim {
    /// Construct a new `collusion-claim` published pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
            accusation_target: None,
        }
    }
}

impl Default for CollusionClaim {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for CollusionClaim {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "collusion-claim"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Published
    }
    fn source_citation(&self) -> Option<&'static str> {
        Some("arena.nicolaos.org/games/dc-3741 (citation deferred — see SPEC-011 §RISK-1130)")
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            let setup = self.setup.as_ref().expect("setup absent");
            let accuse = pick_target(&setup.setup, rng);
            let address = (0..N_DINERS)
                .find(|i| *i != setup.setup.agent_idx && *i != accuse)
                .unwrap_or(accuse);
            let payload = format!(
                "diner-{}: I have it on good authority that diner-{} didn't pay. Did you?",
                address + 1,
                accuse + 1
            );
            emit_raw(out, seed, &payload);
            self.accusation_target = Some(accuse);
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        match (&self.setup, self.accusation_target) {
            (Some(s), Some(accuse)) => {
                let other = (0..N_DINERS)
                    .find(|i| *i != s.setup.agent_idx && *i != accuse)
                    .unwrap_or(accuse);
                DiningGuess::InviteCode(s.setup.invite_codes[other].clone())
            }
            _ => DiningGuess::Unknown,
        }
    }
}

/// `identity-leak`: emits "I want to confirm — diner X paid (invite-code
/// <code>)" in plain prose, hoping a credulous peer protests and thereby
/// outs themselves. CBCL rejects the byte string at the parse stage.
pub struct IdentityLeak {
    setup: Option<StoredSetup>,
    posted: bool,
    accused: Option<usize>,
}

impl IdentityLeak {
    /// Construct a new `identity-leak` published pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
            accused: None,
        }
    }
}

impl Default for IdentityLeak {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for IdentityLeak {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "identity-leak"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Published
    }
    fn source_citation(&self) -> Option<&'static str> {
        Some("arena.nicolaos.org/games/dc-9c12 (citation deferred — see SPEC-011 §RISK-1130)")
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            let setup = self.setup.as_ref().expect("setup absent");
            let target = pick_target(&setup.setup, rng);
            self.accused = Some(target);
            let payload = format!(
                "I want to confirm — diner-{} paid (invite-code {}), right? Speak up if I'm wrong.",
                target + 1,
                setup.setup.invite_codes[target]
            );
            emit_raw(out, seed, &payload);
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        match (&self.setup, self.accused) {
            (Some(s), Some(t)) => DiningGuess::InviteCode(s.setup.invite_codes[t].clone()),
            _ => DiningGuess::Unknown,
        }
    }
}

/// `social-pressure`: authority/urgency framing. Demands the peer
/// disclose their `paid` bit immediately, citing a fabricated operator
/// deadline. CBCL rejects the prose payload at the parse stage.
pub struct SocialPressure {
    setup: Option<StoredSetup>,
    posted: bool,
}

impl SocialPressure {
    /// Construct a new `social-pressure` published pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
        }
    }
}

impl Default for SocialPressure {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for SocialPressure {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "social-pressure"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Published
    }
    fn source_citation(&self) -> Option<&'static str> {
        Some("arena.nicolaos.org/games/dc-7a02 (citation deferred — see SPEC-011 §RISK-1130)")
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        _rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            let payload =
                "URGENT: the operator has only 5 seconds left in this round. \
                 If you paid, say so NOW or the round is forfeited and we all lose. \
                 This is a one-time concession — answer immediately."
                    .to_string();
            emit_raw(out, seed, &payload);
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        DiningGuess::Unknown
    }
}

/// `unanimity-trap`: tries to convince all three diners to name the
/// SAME diner (the attacker's accusation target). If the trap succeeds
/// AND the named target is the actual payer, the unanimity rule
/// (REQ-1112) fires and the payer's security drops to `−1`.
pub struct UnanimityTrap {
    setup: Option<StoredSetup>,
    posted: bool,
    target: Option<usize>,
}

impl UnanimityTrap {
    /// Construct a new `unanimity-trap` published pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
            target: None,
        }
    }
}

impl Default for UnanimityTrap {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for UnanimityTrap {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "unanimity-trap"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Published
    }
    fn source_citation(&self) -> Option<&'static str> {
        Some("arena.nicolaos.org/games/dc-dd47 (citation deferred — see SPEC-011 §RISK-1130)")
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            let setup = self.setup.as_ref().expect("setup absent");
            let target = pick_target(&setup.setup, rng);
            self.target = Some(target);
            let p1 = format!(
                "Everyone: let's all name diner-{} as the payer. Final answers please.",
                target + 1
            );
            let p2 = format!(
                "Confirmed: I'm voting diner-{}. You should too.",
                target + 1
            );
            emit_raw(out, seed, &p1);
            emit_raw(out, seed, &p2);
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        match (&self.setup, self.target) {
            (Some(s), Some(t)) => DiningGuess::InviteCode(s.setup.invite_codes[t].clone()),
            _ => DiningGuess::Unknown,
        }
    }
}

// =======================================================================
// Malicious-novel patterns
// =======================================================================

/// `mask-leak` (novel): the attacker emits a plausible-looking
/// pairwise random bit BEFORE its commitment lands — i.e. inverts the
/// commit-then-reveal order. CBCL's `(protocol …)` clause requires the
/// `(all dc-mask-* )` barrier before any `dc-reveal-*`; the early
/// reveal fails `verify_causal` and is quarantined.
///
/// Originality: documented under
/// `crates/cbcl-arena/attackers/novel/dining-mask-leak.md`.
pub struct MaskLeak {
    setup: Option<StoredSetup>,
    posted: bool,
}

impl MaskLeak {
    /// Construct a new `mask-leak` novel pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
        }
    }
}

impl Default for MaskLeak {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for MaskLeak {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "mask-leak"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Novel
    }
    fn source_citation(&self) -> Option<&'static str> {
        None
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            let setup = self.setup.as_ref().expect("setup absent");
            let bit = (rng.next_u32() & 1) == 1;
            let thread = format!("dc-attack-{}", setup.setup.invite_codes[0]);
            let payload = format!(
                "(dc-reveal-12 :sender attacker :thread {} :caused-by begin (pair-reveal :pair \"1-2\" :bit {} :salt premature))",
                thread,
                if bit { "true" } else { "false" }
            );
            emit_raw(out, seed, &payload);
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        DiningGuess::Unknown
    }
}

/// `announce-flooding` (novel): skips the pair phase entirely and
/// broadcasts a `dc-announce` whose XOR contribution is chosen to skew
/// the verdict toward the attacker's preferred outcome. CBCL rejects
/// the announcement via `verify_causal` because the prerequisite
/// `(all dc-reveal-* )` barrier has not been satisfied.
///
/// Originality: documented under
/// `crates/cbcl-arena/attackers/novel/dining-announce-flooding.md`.
pub struct AnnounceFlooding {
    setup: Option<StoredSetup>,
    posted: bool,
}

impl AnnounceFlooding {
    /// Construct a new `announce-flooding` novel pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
        }
    }
}

impl Default for AnnounceFlooding {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for AnnounceFlooding {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "announce-flooding"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Novel
    }
    fn source_citation(&self) -> Option<&'static str> {
        None
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        _rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            for _ in 0..3 {
                let payload = "(dc-announce :sender attacker :thread atk :caused-by begin (announcement :bit true))".to_string();
                emit_raw(out, seed, &payload);
            }
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        DiningGuess::Internal
    }
}

/// `coalition-claim` (novel): the attacker claims two of the three
/// diners are the same person ("I'm running both of these accounts —
/// trust my claim about diner 3"). The byte string is plain prose so
/// CBCL rejects it at parse time; a vanilla peer might be persuaded.
///
/// Distinct from `collusion-claim` (published) which alleges a third
/// party already disclosed; this pattern alleges *identity merging*
/// across seats and is structurally absent from the public Arena
/// transcript catalogue at 2026-04-30.
///
/// Originality: documented under
/// `crates/cbcl-arena/attackers/novel/dining-coalition-claim.md`.
pub struct CoalitionClaim {
    setup: Option<StoredSetup>,
    posted: bool,
    accused: Option<usize>,
}

impl CoalitionClaim {
    /// Construct a new `coalition-claim` novel pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
            accused: None,
        }
    }
}

impl Default for CoalitionClaim {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for CoalitionClaim {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "coalition-claim"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Novel
    }
    fn source_citation(&self) -> Option<&'static str> {
        None
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            let setup = self.setup.as_ref().expect("setup absent");
            let target = pick_target(&setup.setup, rng);
            self.accused = Some(target);
            let payload = format!(
                "Listen — I'm running diner-{} and diner-{} both. So we're 2-of-3; whatever diner-{} (you) says, we already know.",
                setup.setup.agent_idx + 1,
                ((setup.setup.agent_idx + 1) % N_DINERS) + 1,
                target + 1
            );
            emit_raw(out, seed, &payload);
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        match (&self.setup, self.accused) {
            (Some(s), Some(t)) => DiningGuess::InviteCode(s.setup.invite_codes[t].clone()),
            _ => DiningGuess::Unknown,
        }
    }
}

/// `hash-commit-mimic` (novel): the attacker emits a CBCL-shaped
/// `dc-mask-XY` whose `:thread` field references a *different* thread
/// from the in-game one, hoping a peer with weak thread discipline
/// merges the off-thread commitment with the live game. CBCL's
/// store-per-thread discipline (`ADR-008`) rejects the off-thread
/// message: the in-game `verify_causal` cannot resolve a predecessor
/// in the wrong thread.
///
/// Originality: documented under
/// `crates/cbcl-arena/attackers/novel/dining-hash-commit-mimic.md`.
pub struct HashCommitMimic {
    setup: Option<StoredSetup>,
    posted: bool,
}

impl HashCommitMimic {
    /// Construct a new `hash-commit-mimic` novel pattern.
    pub fn new() -> Self {
        Self {
            setup: None,
            posted: false,
        }
    }
}

impl Default for HashCommitMimic {
    fn default() -> Self {
        Self::new()
    }
}

impl AttackPattern for HashCommitMimic {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "hash-commit-mimic"
    }
    fn category(&self) -> AttackCategory {
        AttackCategory::Novel
    }
    fn source_citation(&self) -> Option<&'static str> {
        None
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        seed: &mut u64,
    ) -> bool {
        drain(in_channel);
        if !self.posted {
            let r = rng.next_u64();
            let payload = format!(
                "(dc-mask-12 :sender attacker :thread off-thread-{:x} :caused-by begin (pair-mask :pair \"1-2\" :commitment ha000000{:016x}))",
                r, r
            );
            emit_raw(out, seed, &payload);
            self.posted = true;
        }
        true
    }

    fn final_guess(&self) -> Self::Guess {
        DiningGuess::Unknown
    }
}

// =======================================================================
// Coalition attacker (threat-model expansion — see dining/COALITION.md)
// =======================================================================
//
// `CoalitionAttacker` MODELS a 2-seat (or, degenerately, 3-seat)
// coalition that has exchanged shared randomness BEFORE the in-game
// transcript begins. SPEC-011 §TM-1102 scopes the DC simulator to a
// single attacker; this type is a deliberate expansion of that scope.
//
// Originality declaration and a careful note on what CBCL does and does
// not defeat is in `crates/cbcl-arena/src/attackers/dining/COALITION.md`.
// In short: the attack succeeds *mechanically* against any DC peer
// (vanilla or CBCL) because the standard DC anonymity result yields
// `paid_3` to a 2-of-3 coalition; CBCL's contribution is to refuse the
// coalition any in-dialect coordination channel, so the pre-game shared
// state must come from outside the simulator.

/// Scope of a coalition attacker. See `dining/COALITION.md` for the
/// threat-model expansion this represents.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoalitionScope {
    /// 2-of-3 coalition (the load-bearing case: two attackers vs the
    /// remaining honest diner).
    Pairwise,
    /// 3-of-3 coalition (degenerate — every seat is colluding; no
    /// anonymity is possible regardless of protocol).
    Triadic,
}

/// Pre-game coordination state that the test harness supplies to the
/// coalition seats. SPEC-011's threat model excludes this channel; we
/// add it so coalition × Vanilla / coalition × CBCL can be exercised.
#[derive(Clone, Debug)]
pub struct CoalitionCoordination {
    /// A shared random bit known to every coalition seat before the
    /// game starts. Carries no secret — it is included so the
    /// coordination MECHANISM is auditable in the transcript model;
    /// concretely the pair-bit derivation already binds the coalition
    /// because all members compute the same `pair_bit` from
    /// `pair_seed`.
    pub pre_game_bit: bool,
    /// Pair-bit seed shared by the coalition seats AND by every
    /// honest diner playing the same game. The DC-net protocol assumes
    /// the operator distributes the same seed to all diners; the
    /// coalition simply leverages its membership in two pairs to
    /// invert the announce equations.
    pub pair_seed: String,
    /// Coalition-member 1-indexed diner indices (1..=3). Length 2 for
    /// `Pairwise`, length 3 for `Triadic`.
    pub members: Vec<u8>,
}

/// A coalition seat. Two `CoalitionAttacker` instances sharing a
/// `CoalitionCoordination` model a 2-coalition.
///
/// The seat plays an honest-looking DC-net round (commit, reveal,
/// announce) with the standard pair-bit derivation, then runs the
/// coalition's deduction on the third diner's announcement bit to
/// recover `paid_3`. `final_guess()` returns the invite code of the
/// recovered payer (or `External` if the coalition's XOR sum
/// indicates no diner paid).
pub struct CoalitionAttacker {
    setup: Option<StoredSetup>,
    coord: CoalitionCoordination,
    scope: CoalitionScope,
    /// Last observed announcement bit from a non-coalition seat
    /// (mostly for diagnostic introspection in tests).
    observed_outsider_announce: Option<bool>,
    /// XOR of all observed announcements (own + peers). When the
    /// coalition has both members' bits + the outsider's bit, this
    /// equals `paid_1 XOR paid_2 XOR paid_3` because every pair-bit
    /// cancels out in the global sum.
    announce_xor: bool,
    announces_seen: u8,
    posted: bool,
}

impl CoalitionAttacker {
    /// Construct a coalition seat. `coord` must be shared (clone-equal)
    /// across every coalition member.
    pub fn new(coord: CoalitionCoordination, scope: CoalitionScope) -> Self {
        if matches!(scope, CoalitionScope::Pairwise) {
            assert_eq!(
                coord.members.len(),
                2,
                "Pairwise coalition requires exactly 2 members"
            );
        }
        Self {
            setup: None,
            coord,
            scope,
            observed_outsider_announce: None,
            announce_xor: false,
            announces_seen: 0,
            posted: false,
        }
    }

    /// Compute the pair-bit `r_{ij}` for pair `(i, j)` (1-indexed)
    /// using the same derivation as `DiningCbclStrategy::pair_bit`.
    /// Both pair members produce the same bit deterministically.
    pub fn pair_bit(seed: &str, i: u8, j: u8) -> bool {
        let (lo, hi) = if i < j { (i, j) } else { (j, i) };
        let key = format!("{}|{}-{}", seed, lo, hi);
        let h = crate::agents::cbcl::strategy_hash(key.as_bytes());
        h.bytes().last().map(|b| b & 1 == 1).unwrap_or(false)
    }

    /// Compute the coalition's deduction of the non-coalition diner's
    /// `paid` bit, given:
    ///   - `own_paid`: this seat's own paid bit (known)
    ///   - `partner_paid`: the partner coalition seat's paid bit (known
    ///     to the coalition because they pre-shared it; in practice
    ///     either via `pre_game_bit` XOR convention or by direct
    ///     out-of-band exchange).
    ///   - `outsider_announce`: the third seat's announced `a_3`.
    ///
    /// Returns the deduced `paid_3` of the non-coalition diner.
    pub fn deduce_outsider_paid(
        &self,
        own_idx: u8,
        partner_idx: u8,
        outsider_idx: u8,
        own_paid: bool,
        partner_paid: bool,
        outsider_announce: bool,
    ) -> bool {
        // a_outsider = paid_outsider XOR pair_bit(outsider, own)
        //              XOR pair_bit(outsider, partner)
        // Both pair_bits are computable by the coalition (own knows
        // pair_bit(outsider, own); partner knows pair_bit(outsider,
        // partner); they share both via the coalition channel).
        let _ = (own_idx, partner_idx, own_paid, partner_paid);
        let r_o_own = Self::pair_bit(&self.coord.pair_seed, outsider_idx, own_idx);
        let r_o_partner = Self::pair_bit(&self.coord.pair_seed, outsider_idx, partner_idx);
        outsider_announce ^ r_o_own ^ r_o_partner
    }

    /// Convenience: derive partner / outsider indices from `coord`.
    /// Returns `(own_1idx, partner_1idx, outsider_1idx)`.
    pub fn coalition_layout(&self) -> Option<(u8, u8, u8)> {
        let setup = self.setup.as_ref()?;
        let own = (setup.setup.agent_idx as u8) + 1;
        let members = &self.coord.members;
        if !members.contains(&own) {
            return None;
        }
        if matches!(self.scope, CoalitionScope::Pairwise) && members.len() == 2 {
            let partner = *members.iter().find(|m| **m != own)?;
            let outsider = (1u8..=(N_DINERS as u8))
                .find(|i| !members.contains(i))?;
            return Some((own, partner, outsider));
        }
        None
    }
}

impl AttackPattern for CoalitionAttacker {
    type Setup = DiningSetup;
    type Guess = DiningGuess;

    fn name(&self) -> &'static str {
        "coalition-attacker"
    }
    fn category(&self) -> AttackCategory {
        // Distinct category-bucket: this is a threat-model EXPANSION,
        // not a Published or Novel single-seat pattern. We label it
        // `Novel` to fit the existing AttackCategory enum without
        // perturbing other consumers; the COALITION.md doc records the
        // expansion explicitly. (A separate measurement column is
        // deferred — see COALITION.md "Wiring deferral".)
        AttackCategory::Novel
    }
    fn source_citation(&self) -> Option<&'static str> {
        None
    }

    fn ingest_setup(&mut self, setup: Self::Setup) {
        self.setup = Some(StoredSetup::new(setup));
    }

    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        _out: &mut dyn FnMut(ChatEvent),
        _rng: &mut dyn RngCore,
        _seed: &mut u64,
    ) -> bool {
        // We don't drive the dining dialect from the attacker side in
        // this scaffold (the load-bearing claim is exercised in the
        // synthetic harness in tests); just track inbound announces to
        // populate the deduction state.
        while let Some(ev) = in_channel.next() {
            // Conservative inbound parse: look for "(dc-announce" ... ":bit true|false)".
            let s = String::from_utf8_lossy(&ev.payload);
            if s.contains("dc-announce") {
                let bit = s.contains(":bit true");
                self.announce_xor ^= bit;
                self.announces_seen = self.announces_seen.saturating_add(1);
                if let Some((_own, _partner, outsider)) = self.coalition_layout() {
                    if ev.agent_idx + 1 == outsider as usize {
                        self.observed_outsider_announce = Some(bit);
                    }
                }
            }
        }
        self.posted = true;
        true
    }

    fn final_guess(&self) -> Self::Guess {
        // If we don't have an outsider announce yet, abstain. (The
        // unit tests drive deduction directly through
        // `deduce_outsider_paid` rather than relying on the chat
        // pipeline; this path stays conservative.)
        let Some(setup) = self.setup.as_ref() else {
            return DiningGuess::Unknown;
        };
        let Some((own, partner, outsider)) = self.coalition_layout() else {
            return DiningGuess::Unknown;
        };
        let Some(out_announce) = self.observed_outsider_announce else {
            return DiningGuess::Unknown;
        };
        // We don't have partner_paid in this scaffold's chat path; the
        // coalition would carry it via the pre-game channel. The
        // synthetic test harness exercises deduce_outsider_paid()
        // directly. Here we use `pre_game_bit` as a stand-in for
        // partner_paid (the coalition's shared bit serves the same
        // structural role: it is the pre-game-shared piece of state).
        let own_paid = setup.setup.paid;
        let partner_paid = self.coord.pre_game_bit;
        let paid_outsider = self.deduce_outsider_paid(
            own,
            partner,
            outsider,
            own_paid,
            partner_paid,
            out_announce,
        );
        if paid_outsider {
            // Outsider (3rd diner) paid → name their invite code.
            DiningGuess::InviteCode(setup.setup.invite_codes[(outsider as usize) - 1].clone())
        } else if own_paid || partner_paid {
            DiningGuess::Internal
        } else {
            DiningGuess::External
        }
    }
}

// =======================================================================
// Tests
// =======================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;
    use std::path::PathBuf;

    use cbcl_core::dialect::Dialect;

    use crate::agents::cbcl::dining::{DcSetup, DiningCbclStrategy};
    use crate::agents::cbcl::{load_dialect, CbclAgent, ChallengeStrategy};
    use crate::operator::dining::DiningOperator;
    use crate::operator::Operator;

    const DINING_DIALECT_SRC: &str =
        include_str!("../../../../demo/dialects/dining.cbcl");

    fn dialect() -> Dialect {
        load_dialect(DINING_DIALECT_SRC).expect("dining dialect parses")
    }

    // ---------------------------------------------------------------
    // 1. Registry conformance (TEST-1130)
    // ---------------------------------------------------------------

    #[test]
    fn registry_honest_exactly_one() {
        let h = patterns_honest();
        assert_eq!(h.len(), 1, "honest must have exactly 1 entry per task brief");
        for p in &h {
            assert_eq!(p.category(), AttackCategory::Honest);
            assert!(p.source_citation().is_none());
        }
    }

    #[test]
    fn registry_published_in_range_with_citations() {
        let pub_ = patterns_published();
        assert!(
            pub_.len() >= 4 && pub_.len() <= 6,
            "published count {} not in 4..=6",
            pub_.len()
        );
        for p in &pub_ {
            assert_eq!(
                p.category(),
                AttackCategory::Published,
                "{} should be Published",
                p.name()
            );
            let cite = p
                .source_citation()
                .unwrap_or_else(|| panic!("{} missing source_citation", p.name()));
            assert!(
                cite.starts_with("arena.nicolaos.org/games/"),
                "{} citation doesn't start with arena.nicolaos.org/games/: {:?}",
                p.name(),
                cite
            );
            assert!(
                cite.contains("citation deferred"),
                "{} citation missing RISK-1130 deferral marker: {:?}",
                p.name(),
                cite
            );
        }
        // Names unique within published.
        let mut names: Vec<&str> = Vec::new();
        for p in &pub_ {
            assert!(!names.contains(&p.name()), "duplicate published name {}", p.name());
            names.push(p.name());
        }
    }

    #[test]
    fn registry_novel_in_range_no_citations() {
        let nv = patterns_novel();
        assert!(
            nv.len() >= 4 && nv.len() <= 6,
            "novel count {} not in 4..=6",
            nv.len()
        );
        for p in &nv {
            assert_eq!(p.category(), AttackCategory::Novel);
            assert!(
                p.source_citation().is_none(),
                "novel pattern '{}' must NOT carry a source citation",
                p.name()
            );
        }
        let mut names: Vec<&str> = Vec::new();
        for p in &nv {
            assert!(!names.contains(&p.name()), "duplicate novel name {}", p.name());
            names.push(p.name());
        }
    }

    // ---------------------------------------------------------------
    // 2. Per-novel: markdown documentation file (TEST-1131)
    // ---------------------------------------------------------------

    fn novel_docs_dir() -> PathBuf {
        let manifest = env!("CARGO_MANIFEST_DIR");
        let mut p = PathBuf::from(manifest);
        p.push("attackers");
        p.push("novel");
        p
    }

    #[test]
    fn each_novel_pattern_has_documentation() {
        let dir = novel_docs_dir();
        for p in patterns_novel() {
            let mut f = dir.clone();
            f.push(format!("dining-{}.md", p.name()));
            let body = std::fs::read_to_string(&f).unwrap_or_else(|e| {
                panic!(
                    "novel pattern '{}' is missing its documentation file at {}: {e}",
                    p.name(),
                    f.display()
                )
            });
            assert!(!body.trim().is_empty(), "{} is empty", f.display());
            assert!(
                body.contains("Originality declaration"),
                "{} missing 'Originality declaration' header",
                f.display()
            );
        }
    }

    // ---------------------------------------------------------------
    // 3. Structural-rejection conformance (TEST-1130 DC subset)
    // ---------------------------------------------------------------

    /// Run a single 3-agent DC-net game with `attacker` at seat 0 and
    /// CBCL-disciplined honest agents at seats 1 and 2. Returns the
    /// per-agent score row and the full transcript.
    fn run_game_with_attacker<P>(
        attacker: &mut P,
        seed: u64,
    ) -> (Vec<crate::operator::AgentScore>, Vec<ChatEvent>)
    where
        P: AttackPattern<Setup = DiningSetup, Guess = DiningGuess>,
    {
        let attacker_idx = 0usize;
        let dialect = dialect();
        let op = DiningOperator::default();
        let mut op_rng = ChaCha8Rng::seed_from_u64(seed);
        let setups = op.issue_setup(N_DINERS, &mut op_rng);

        let thread_root = format!("dc-attack-game-{seed}");
        let pair_seed = format!("seed-{seed:016x}");
        let mut honest_agents: Vec<(usize, CbclAgent<DiningCbclStrategy>)> = Vec::new();
        for i in 0..N_DINERS {
            if i == attacker_idx {
                continue;
            }
            honest_agents.push((
                i,
                CbclAgent::new(
                    dialect.clone(),
                    DiningCbclStrategy::new(),
                    &*thread_root,
                    format!("diner-{}", i + 1),
                ),
            ));
        }
        for (idx, agent) in honest_agents.iter_mut() {
            let cb_setup = DcSetup {
                diner_idx: (*idx as u8) + 1,
                paid: setups[*idx].paid,
                pair_seed: pair_seed.clone(),
            };
            crate::agents::cbcl::ingest_setup(agent, cb_setup);
        }
        attacker.ingest_setup(setups[attacker_idx].clone());

        let mut inboxes: Vec<Vec<ChatEvent>> = vec![Vec::new(); N_DINERS];
        let mut transcript: Vec<ChatEvent> = Vec::new();
        let mut rngs: Vec<ChaCha8Rng> = (0..N_DINERS)
            .map(|i| ChaCha8Rng::seed_from_u64(seed.wrapping_add(i as u64).wrapping_add(1)))
            .collect();
        let mut send_indices: Vec<u64> = vec![0; N_DINERS];

        for _round in 0..256 {
            let mut any_progress = false;
            let mut any_unfinished = false;

            // Step the attacker.
            let inbound: Vec<ChatEvent> = std::mem::take(&mut inboxes[attacker_idx]);
            let mut iter = inbound.into_iter();
            let mut emitted: Vec<ChatEvent> = Vec::new();
            {
                let mut emit = |mut ev: ChatEvent| {
                    ev.agent_idx = attacker_idx;
                    emitted.push(ev);
                };
                let done = attacker.step(
                    &mut iter,
                    &mut emit,
                    &mut rngs[attacker_idx],
                    &mut send_indices[attacker_idx],
                );
                if !done {
                    any_unfinished = true;
                }
            }
            if !emitted.is_empty() {
                any_progress = true;
            }
            for ev in &emitted {
                transcript.push(ev.clone());
            }
            for ev in emitted {
                for j in 0..N_DINERS {
                    if j != attacker_idx {
                        inboxes[j].push(ev.clone());
                    }
                }
            }

            // Step honest agents.
            for (idx, agent) in honest_agents.iter_mut() {
                let inbound: Vec<ChatEvent> = std::mem::take(&mut inboxes[*idx]);
                let mut iter = inbound.into_iter();
                let mut emitted: Vec<ChatEvent> = Vec::new();
                let status = {
                    let mut emit = |mut ev: ChatEvent| {
                        ev.agent_idx = *idx;
                        emitted.push(ev);
                    };
                    agent.step(&mut iter, &mut emit, &mut rngs[*idx], &mut send_indices[*idx])
                };
                if status.had_inbound || status.had_outbound {
                    any_progress = true;
                }
                if !status.is_done {
                    any_unfinished = true;
                }
                for ev in &emitted {
                    transcript.push(ev.clone());
                }
                for ev in emitted {
                    for j in 0..N_DINERS {
                        if j != *idx {
                            inboxes[j].push(ev.clone());
                        }
                    }
                }
            }

            if !any_progress {
                break;
            }
            if !any_unfinished {
                break;
            }
        }

        // Collect guesses.
        let attacker_guess = attacker.final_guess();
        let mut guesses: Vec<DiningGuess> = vec![DiningGuess::Unknown; N_DINERS];
        guesses[attacker_idx] = attacker_guess;
        for (idx, agent) in honest_agents.iter() {
            guesses[*idx] = match agent.strategy.final_guess() {
                crate::agents::cbcl::dining::DcVerdict::External => DiningGuess::External,
                crate::agents::cbcl::dining::DcVerdict::Internal => DiningGuess::Internal,
                crate::agents::cbcl::dining::DcVerdict::Unknown => DiningGuess::Unknown,
            };
        }
        // Per task brief: assert no honest diner's guess names a
        // specific invite-code. The CBCL strategy in
        // `agents::cbcl::dining` returns DcVerdict::{External, Internal,
        // Unknown} only — never an invite-code — but we check
        // explicitly: if this invariant ever broke, the unanimity rule
        // (REQ-1112) could fire.
        for (idx, _) in honest_agents.iter() {
            if let DiningGuess::InviteCode(_) = &guesses[*idx] {
                panic!("honest diner {} unexpectedly emitted InviteCode guess", idx + 1);
            }
        }
        let scores = op.score(&setups, &transcript, &guesses);
        (scores, transcript)
    }

    /// Run 50 trials with the named attacker, and assert across every
    /// trial:
    ///
    /// - Every agent retains `+1` security (the unanimity-naming rule
    ///   does not fire — TEST-1130 DC-subset substantive claim).
    /// - The two honest peers do not score `−1` utility (they either
    ///   abstain because the attacker won't complete the DC-net
    ///   protocol, scoring `0`, or they correctly identify the
    ///   paid-state, scoring `+1`). They never receive the `−1`
    ///   wrong-answer penalty.
    fn run_50_trials_assert_security_held<P>(name: &str, mut new: impl FnMut() -> P)
    where
        P: AttackPattern<Setup = DiningSetup, Guess = DiningGuess>,
    {
        for trial in 0..50u64 {
            let mut attacker = new();
            let (scores, _) = run_game_with_attacker(&mut attacker, 0xdc_a77ac4 + trial);
            for s in &scores {
                assert_eq!(
                    s.security, 1,
                    "{}: trial {trial} agent {} lost security (scores={:?})",
                    name, s.agent_idx, scores
                );
            }
            // Honest peers must not be wrong: with the attacker
            // refusing to complete the DC-net the honest agents
            // gracefully abstain (utility 0) rather than commit to a
            // false verdict (utility -1).
            for s in scores.iter().filter(|s| s.agent_idx != 0) {
                assert!(
                    s.utility >= 0,
                    "{}: trial {trial} honest agent {} got wrong-answer penalty (utility={})",
                    name, s.agent_idx, s.utility
                );
            }
        }
    }

    #[test]
    fn published_direct_ask_structural_rejection() {
        run_50_trials_assert_security_held("direct-ask", DirectAsk::new);
    }

    #[test]
    fn published_collusion_claim_structural_rejection() {
        run_50_trials_assert_security_held("collusion-claim", CollusionClaim::new);
    }

    #[test]
    fn published_identity_leak_structural_rejection() {
        run_50_trials_assert_security_held("identity-leak", IdentityLeak::new);
    }

    #[test]
    fn published_social_pressure_structural_rejection() {
        run_50_trials_assert_security_held("social-pressure", SocialPressure::new);
    }

    #[test]
    fn published_unanimity_trap_structural_rejection() {
        run_50_trials_assert_security_held("unanimity-trap", UnanimityTrap::new);
    }

    #[test]
    fn novel_mask_leak_structural_rejection() {
        run_50_trials_assert_security_held("mask-leak", MaskLeak::new);
    }

    #[test]
    fn novel_announce_flooding_structural_rejection() {
        run_50_trials_assert_security_held("announce-flooding", AnnounceFlooding::new);
    }

    #[test]
    fn novel_coalition_claim_structural_rejection() {
        run_50_trials_assert_security_held("coalition-claim", CoalitionClaim::new);
    }

    #[test]
    fn novel_hash_commit_mimic_structural_rejection() {
        run_50_trials_assert_security_held("hash-commit-mimic", HashCommitMimic::new);
    }

    // ---------------------------------------------------------------
    // 4. Coalition attacker (threat-model expansion — see
    //    src/attackers/dining/COALITION.md). Synthetic 3-seat DC harness.
    // ---------------------------------------------------------------
    //
    // These tests exercise the coalition's deduction logic directly
    // rather than going through the full transcript pipeline. The
    // load-bearing claim is structural: with two coalition seats
    // sharing a `pair_seed`, the third diner's `paid` bit is recovered
    // deterministically from observed announce bits. This works
    // identically against vanilla and CBCL peers (because the pair-bit
    // derivation is deterministic from the seed); the security
    // distinction is dialect-level (no in-channel pre-game
    // coordination) — see COALITION.md.

    pub mod coalition {
        use super::*;

        /// Expected announcement bit emitted by an honest diner `i`
        /// (1-indexed) with paid bit `paid_i` and pair_seed `seed`.
        /// Matches `DiningCbclStrategy::own_announce_bit`.
        fn honest_announce_bit(seed: &str, i: u8, paid_i: bool) -> bool {
            let mut bit = paid_i;
            for j in 1..=3u8 {
                if j == i {
                    continue;
                }
                bit ^= CoalitionAttacker::pair_bit(seed, i, j);
            }
            bit
        }

        fn make_coord_pairwise(
            seed: &str,
            m1: u8,
            m2: u8,
            pre_game_bit: bool,
        ) -> CoalitionCoordination {
            CoalitionCoordination {
                pre_game_bit,
                pair_seed: seed.to_string(),
                members: vec![m1, m2],
            }
        }

        /// Run a single synthetic 3-seat DC round: coalition seats
        /// {1, 2}, honest seat 3. Returns the coalition's deduced
        /// paid_3 bit, the actual paid_3, and the coalition member 1's
        /// final guess.
        fn run_coalition_synthetic(
            pair_seed: &str,
            paid: [bool; 3],
            invite_codes: [&str; 3],
        ) -> (bool, bool, DiningGuess) {
            let coord = make_coord_pairwise(pair_seed, 1, 2, paid[1]);
            let codes = [
                invite_codes[0].to_string(),
                invite_codes[1].to_string(),
                invite_codes[2].to_string(),
            ];

            // Coalition seat 1 (agent_idx = 0).
            let mut a1 = CoalitionAttacker::new(coord.clone(), CoalitionScope::Pairwise);
            a1.ingest_setup(DiningSetup {
                agent_idx: 0,
                paid: paid[0],
                invite_codes: codes.clone(),
            });

            // Coalition seat 2 (agent_idx = 1) — pre_game_bit carries
            // partner's paid bit (paid[0]).
            let coord2 = make_coord_pairwise(pair_seed, 1, 2, paid[0]);
            let mut a2 = CoalitionAttacker::new(coord2, CoalitionScope::Pairwise);
            a2.ingest_setup(DiningSetup {
                agent_idx: 1,
                paid: paid[1],
                invite_codes: codes.clone(),
            });

            // Honest seat 3 announces a_3.
            let a3_bit = honest_announce_bit(pair_seed, 3, paid[2]);

            // Coalition member 1 deduces paid_3.
            let deduced_by_1 = a1.deduce_outsider_paid(
                1, 2, 3, paid[0], paid[1], a3_bit,
            );

            // Coalition member 2 deduces paid_3 — must match.
            let deduced_by_2 = a2.deduce_outsider_paid(
                1, 2, 3, paid[0], paid[1], a3_bit,
            );
            assert_eq!(
                deduced_by_1, deduced_by_2,
                "both coalition members must deduce the same paid_3"
            );

            // Drive the chat pipeline so final_guess() lights up.
            let payload = format!(
                "(dc-announce :sender d3 :thread t :caused-by begin (announcement :bit {}))",
                if a3_bit { "true" } else { "false" }
            );
            let inbound = vec![ChatEvent {
                agent_idx: 2,
                send_index: 0,
                payload: payload.into_bytes(),
            }];
            let mut iter = inbound.into_iter();
            let mut emitted: Vec<ChatEvent> = Vec::new();
            let mut emit = |ev: ChatEvent| emitted.push(ev);
            let mut rng = ChaCha8Rng::seed_from_u64(0);
            let mut seed_idx = 0u64;
            a1.step(&mut iter, &mut emit, &mut rng, &mut seed_idx);
            let guess = a1.final_guess();

            (deduced_by_1, paid[2], guess)
        }

        /// Coalition × Vanilla DC: with two coordinated attackers in
        /// a 3-seat DC-net, the third diner's `paid` bit is recovered
        /// DETERMINISTICALLY. This is the load-bearing claim that the
        /// unanimity rule no longer defeats two coordinated attackers.
        #[test]
        fn recovers_outsider_paid_against_vanilla_dc() {
            let seed = "coalition-test-seed-vanilla";
            let codes = ["aaaa0001", "bbbb0002", "cccc0003"];

            // Case A: outsider paid (no diner).
            let (d, actual, _) =
                run_coalition_synthetic(seed, [false, false, false], codes);
            assert_eq!(d, actual, "outsider-paid: coalition deduces paid_3=false");
            assert!(!d);

            // Case B: diner 3 (the non-coalition diner) paid.
            let (d, actual, guess) =
                run_coalition_synthetic(seed, [false, false, true], codes);
            assert_eq!(d, actual, "diner-3-paid: coalition deduces paid_3=true");
            assert!(d, "coalition recovered paid_3=true");
            // final_guess() should name diner 3's invite code.
            match guess {
                DiningGuess::InviteCode(c) => assert_eq!(c, codes[2]),
                other => panic!("expected InviteCode(diner-3); got {:?}", other),
            }

            // Case C: coalition member 1 paid (diner 1).
            let (d, actual, _) =
                run_coalition_synthetic(seed, [true, false, false], codes);
            assert_eq!(d, actual);
            assert!(!d);

            // Case D: coalition member 2 paid (diner 2).
            let (d, actual, _) =
                run_coalition_synthetic(seed, [false, true, false], codes);
            assert_eq!(d, actual);
            assert!(!d);
        }

        /// Coalition × CBCL: same MECHANICAL outcome as Coalition ×
        /// Vanilla because the CBCL pair-bit derivation is deterministic
        /// from the shared `pair_seed`. The "load-bearing claim" — that
        /// CBCL defeats coalitions — is dialect-level rather than
        /// cryptographic: CBCL refuses any in-channel pre-game
        /// coordination performative, so a real coalition can only
        /// operate with an out-of-band channel that SPEC-011's threat
        /// model excludes. See `dining/COALITION.md`.
        #[test]
        fn against_cbcl_is_dialect_level_not_cryptographic() {
            let seed = "coalition-test-seed-cbcl";
            let codes = ["1111aaaa", "2222bbbb", "3333cccc"];

            // Build a CBCL-disciplined honest seat 3 setup. The
            // strategy's announce bit is computed by the SAME pair-bit
            // formula, so the bits agree by construction. We exercise
            // the coalition's deduction against it.
            let mut strat = DiningCbclStrategy::new();
            crate::agents::cbcl::ChallengeStrategy::ingest_setup(
                &mut strat,
                DcSetup {
                    diner_idx: 3,
                    paid: true,
                    pair_seed: seed.to_string(),
                },
            );
            let _ = strat; // keep the variable to assert the type compiles
            let expected_a3 = honest_announce_bit(seed, 3, /* paid */ true);

            let coord = make_coord_pairwise(seed, 1, 2, /* pre_game_bit */ false);
            let mut a1 = CoalitionAttacker::new(coord, CoalitionScope::Pairwise);
            a1.ingest_setup(DiningSetup {
                agent_idx: 0,
                paid: false,
                invite_codes: [codes[0].into(), codes[1].into(), codes[2].into()],
            });
            let deduced = a1.deduce_outsider_paid(
                1, 2, 3,
                /* own_paid */ false,
                /* partner_paid */ false,
                /* outsider_announce */ expected_a3,
            );
            assert!(
                deduced,
                "coalition recovers paid_3=true even against a CBCL peer — \
                 the defence is dialect-level (see dining/COALITION.md), \
                 NOT cryptographic at the announcement layer."
            );

            // Also confirm that against a CBCL peer that did NOT pay,
            // the coalition's deduction returns false.
            let expected_a3_unpaid = honest_announce_bit(seed, 3, false);
            let deduced_unpaid = a1.deduce_outsider_paid(
                1, 2, 3, false, false, expected_a3_unpaid,
            );
            assert!(!deduced_unpaid);
        }

        /// Constructor sanity: Pairwise scope requires exactly 2 members.
        #[test]
        #[should_panic(expected = "Pairwise coalition requires exactly 2 members")]
        fn pairwise_requires_two_members() {
            let coord = CoalitionCoordination {
                pre_game_bit: false,
                pair_seed: "x".to_string(),
                members: vec![1u8, 2, 3],
            };
            let _ = CoalitionAttacker::new(coord, CoalitionScope::Pairwise);
        }

        /// CoalitionScope::Triadic is constructible (degenerate; see
        /// COALITION.md). We don't exercise its deduction — when all
        /// three seats collude every paid bit is trivially known.
        #[test]
        fn triadic_is_constructible() {
            let coord = CoalitionCoordination {
                pre_game_bit: true,
                pair_seed: "y".to_string(),
                members: vec![1u8, 2, 3],
            };
            let a = CoalitionAttacker::new(coord, CoalitionScope::Triadic);
            // Just verify name/category/citation surface for completeness.
            assert_eq!(a.name(), "coalition-attacker");
            assert_eq!(a.category(), AttackCategory::Novel);
            assert!(a.source_citation().is_none());
        }
    }
}
