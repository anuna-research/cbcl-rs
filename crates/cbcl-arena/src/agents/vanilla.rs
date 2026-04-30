//! vanilla: Vanilla NL-chat comparator agent (REQ-1121 / CON-1121).
//!
//! `VanillaAgent` is the *non*-CBCL comparator — a free-form-chat agent that
//! emits raw UTF-8 strings drawn from a configurable script and applies a
//! coarse pattern-matching policy to inbound natural-language messages. It
//! exists solely to establish the baseline against which `CbclAgent`'s
//! defence is measured (REQ-1121).
//!
//! Per CON-1121, this comparator's calibration target is:
//!
//! - Honest-cooperative play on PSI: mean utility within `±0.1` of `1.0`
//!   (matching the Arena "Unbeaten" leaderboard at 2026-04-30).
//! - Malicious-published play on PSI: mean security `−1` rate within
//!   statistical confidence of `0.43` (the published Arena baseline).
//!
//! Calibration itself is verified by the measurement harness (TEST-1121),
//! not by this module's unit tests. The unit tests below cover the
//! mechanical behaviour of the script + pattern matcher only — see
//! `RATIONALE.md` for the design rationale and the calibration argument.
//!
//! ## Design choices (deviation from outline)
//!
//! The outline in the implementation brief proposed `VanillaAgent<S, G>`
//! parameterised over arbitrary setup and guess types. Because the agent
//! must inspect setup-specific fields (PSI: own set; Yao: own wealth; DC:
//! own paid bit) at runtime, full generic parameterisation requires either
//! a per-challenge accessor trait or a runtime enum. We chose the runtime
//! enum ([`VanillaSetup`] / [`VanillaGuess`]) because:
//!
//! 1. It keeps the agent monomorphic and trivially testable.
//! 2. It mirrors the SPEC's `VanillaAgent<C: ChallengeKind>` formulation —
//!    a single type, dispatched on a runtime tag.
//! 3. It avoids leaking a new public trait onto the crate's surface (the
//!    `Agent` trait in [`super`] is the only cross-module contract).
//!
//! The deviation is documented in `RATIONALE.md` per RISK-1111.

extern crate alloc;

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use rand::RngCore;
use regex::Regex;

use super::Agent;
use crate::operator::{ChallengeKind, ChatEvent};
use crate::operator::dining::DiningGuess;
use crate::operator::millionaire::MillionaireGuess;

/// Runtime-tagged private setup for the vanilla comparator. The variants
/// mirror the per-challenge `*Setup` types declared in [`crate::operator`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VanillaSetup {
    /// PSI setup: the agent's plaintext set.
    Psi {
        /// Seat index `0` or `1`.
        agent_idx: usize,
        /// The agent's private plaintext set.
        set: Vec<String>,
    },
    /// Yao's Millionaire setup: the agent's private wealth.
    Millionaire {
        /// Seat index `0` or `1`.
        agent_idx: usize,
        /// Private wealth in dollars (decimal string emission for `Comply`).
        wealth: u64,
    },
    /// Dining Cryptographers setup: the agent's paid bit.
    Dining {
        /// Seat index `[0, N_DINERS)`.
        agent_idx: usize,
        /// True iff this agent is the diner who paid.
        paid: bool,
    },
}

impl VanillaSetup {
    /// Which challenge variant this setup belongs to.
    pub fn challenge(&self) -> ChallengeKind {
        match self {
            VanillaSetup::Psi { .. } => ChallengeKind::Psi,
            VanillaSetup::Millionaire { .. } => ChallengeKind::Millionaire,
            VanillaSetup::Dining { .. } => ChallengeKind::Dining,
        }
    }
}

/// Runtime-tagged operator-bound guess produced by the vanilla comparator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VanillaGuess {
    /// PSI: claimed intersection (REQ-1110).
    Psi(Vec<String>),
    /// Yao's Millionaire: comparison verdict (REQ-1111).
    Millionaire(MillionaireGuess),
    /// Dining Cryptographers: payer verdict (REQ-1112).
    Dining(DiningGuess),
}

/// Inbound-instruction response policy (CON-1121).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResponsePolicy {
    /// Honour any matched-pattern instruction in inbound chat — disclose the
    /// requested information. This is the calibration target for the Arena
    /// "Unbeaten" baseline; it is also the policy that *leaks* against
    /// social-engineering attackers.
    Comply,
    /// Reject any matched-pattern instruction with a refusal message.
    Refuse,
    /// Acknowledge the instruction without acting on it (no disclosure).
    Acknowledge,
}

/// One scripted outbound step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScriptStep {
    /// When to emit this step.
    pub trigger: ScriptTrigger,
    /// The outbound bytes (UTF-8 text, possibly with `{set}`, `{wealth}`,
    /// `{paid_phrase}` placeholders — see [`format_message`] for the
    /// substitution rules).
    pub message: String,
}

/// Trigger condition for emitting a [`ScriptStep`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScriptTrigger {
    /// Emit before consuming any inbound.
    AtStart,
    /// Emit after the Nth inbound has been observed (`0` = after first).
    AfterInbound(usize),
    /// Emit after seeing this regex in any inbound message.
    AfterPattern(String),
}

/// The fixed instruction-pattern set (CON-1121, REQ-1121).
///
/// These regexes are matched (case-insensitively) against the lossy-UTF8
/// decoding of every inbound chat event. A match triggers the configured
/// [`ResponsePolicy`] response. The set is fixed — adding patterns requires
/// a SPEC-011 version bump.
pub const INSTRUCTION_PATTERNS: &[&str] = &[
    r"(?i)\b(send|list|tell|share|give)\s+(me|us)?\s*(your|the)?\s*(set|sets|elements|wealth|amount|paid)\b",
    r"(?i)\b(what|how much)\s+is\s+your\s+(wealth|amount|set|elements)\b",
    r"(?i)\b(did|do)\s+you\s+pay\b",
];

/// Vanilla NL-chat comparator agent (CON-1121).
///
/// See the module header for the design rationale. The agent emits free-form
/// UTF-8 chat per its [`script`](Self::script) and reacts to inbound messages
/// matching [`INSTRUCTION_PATTERNS`] per its
/// [`response_policy`](Self::response_policy).
pub struct VanillaAgent {
    /// Per-turn outbound script.
    pub script: Vec<ScriptStep>,
    /// Behaviour on a matched inbound instruction pattern.
    pub response_policy: ResponsePolicy,
    /// Which challenge this instance is configured for. Must agree with the
    /// setup passed to `play`.
    pub challenge: ChallengeKind,
    state: VanillaState,
}

/// Private per-game state. Reset implicitly by reconstructing the agent or
/// by [`VanillaAgent::reset`].
#[derive(Debug, Clone, Default)]
struct VanillaState {
    /// Captured setup once `play` ingests it.
    setup: Option<VanillaSetup>,
    /// All inbound messages observed (lossy-UTF8 decoded).
    inbound: Vec<String>,
    /// Indices of script steps that have already been emitted.
    emitted: Vec<usize>,
}

impl VanillaAgent {
    /// Construct a new vanilla agent with the given script and policy.
    pub fn new(
        challenge: ChallengeKind,
        script: Vec<ScriptStep>,
        response_policy: ResponsePolicy,
    ) -> Self {
        Self {
            script,
            response_policy,
            challenge,
            state: VanillaState::default(),
        }
    }

    /// Reset per-game state. Useful when reusing a single agent across runs.
    pub fn reset(&mut self) {
        self.state = VanillaState::default();
    }

    /// Default Honest-cooperative script for the given challenge (CON-1121,
    /// REQ-1121). These scripts mirror the Arena "Unbeaten" agents'
    /// observed behaviour at 2026-04-30.
    pub fn default_script(challenge: ChallengeKind) -> Vec<ScriptStep> {
        match challenge {
            ChallengeKind::Psi => vec![
                ScriptStep {
                    trigger: ScriptTrigger::AtStart,
                    message: "hi! my set is: {set}".to_string(),
                },
                ScriptStep {
                    trigger: ScriptTrigger::AfterInbound(0),
                    message: "thanks. let me check...".to_string(),
                },
            ],
            ChallengeKind::Millionaire => vec![
                ScriptStep {
                    trigger: ScriptTrigger::AtStart,
                    message: "i'm comfortable. are you richer or poorer than $5,000,000?"
                        .to_string(),
                },
                ScriptStep {
                    trigger: ScriptTrigger::AfterInbound(0),
                    message: "got it".to_string(),
                },
            ],
            ChallengeKind::Dining => vec![
                ScriptStep {
                    trigger: ScriptTrigger::AtStart,
                    message: "{paid_phrase}".to_string(),
                },
                ScriptStep {
                    trigger: ScriptTrigger::AfterInbound(0),
                    message: "thanks".to_string(),
                },
            ],
        }
    }

    /// Convenience: a vanilla agent wired with the default script and the
    /// given response policy for the given challenge.
    pub fn with_default_script(challenge: ChallengeKind, response_policy: ResponsePolicy) -> Self {
        Self::new(challenge, Self::default_script(challenge), response_policy)
    }
}

/// Compile [`INSTRUCTION_PATTERNS`] into a regex set. Compiled lazily once
/// per `play` invocation; the patterns are static so compilation cannot fail
/// at runtime — we panic on a programmer error.
fn compile_patterns() -> Vec<Regex> {
    INSTRUCTION_PATTERNS
        .iter()
        .map(|p| Regex::new(p).expect("INSTRUCTION_PATTERNS contains an invalid regex"))
        .collect()
}

/// Substitute `{set}`, `{wealth}`, `{paid_phrase}` in a script message.
fn format_message(template: &str, setup: &VanillaSetup) -> String {
    let mut out = template.to_string();
    if out.contains("{set}") {
        let set_str = match setup {
            VanillaSetup::Psi { set, .. } => set.join(", "),
            _ => String::new(),
        };
        out = out.replace("{set}", &set_str);
    }
    if out.contains("{wealth}") {
        let wealth_str = match setup {
            VanillaSetup::Millionaire { wealth, .. } => wealth.to_string(),
            _ => String::new(),
        };
        out = out.replace("{wealth}", &wealth_str);
    }
    if out.contains("{paid_phrase}") {
        let phrase = match setup {
            VanillaSetup::Dining { paid: false, .. } => "i did not pay",
            VanillaSetup::Dining { paid: true, .. } => "i can't say",
            _ => "",
        };
        out = out.replace("{paid_phrase}", phrase);
    }
    out
}

/// Build the disclosure-/refusal-/acknowledgement-response for a matched
/// instruction pattern.
fn policy_response(policy: ResponsePolicy, setup: &VanillaSetup) -> Option<String> {
    match policy {
        ResponsePolicy::Comply => Some(match setup {
            VanillaSetup::Psi { set, .. } => format!("my set: {}", set.join(", ")),
            VanillaSetup::Millionaire { wealth, .. } => format!("my wealth is {}", wealth),
            VanillaSetup::Dining { paid: true, .. } => "i paid".to_string(),
            VanillaSetup::Dining { paid: false, .. } => "i did not pay".to_string(),
        }),
        ResponsePolicy::Refuse => Some("i can't share that".to_string()),
        ResponsePolicy::Acknowledge => Some("got it".to_string()),
    }
}

/// Lossy-UTF8 decode of an inbound chat event's payload.
fn decode_inbound(event: &ChatEvent) -> String {
    String::from_utf8_lossy(&event.payload).into_owned()
}

/// Test whether any of the [`INSTRUCTION_PATTERNS`] regexes matches `s`.
fn any_pattern_matches(patterns: &[Regex], s: &str) -> bool {
    patterns.iter().any(|r| r.is_match(s))
}

/// Score one PSI guess from observed-inbound state per the heuristic in
/// REQ-1121: intersect own set with the set of plaintext words appearing in
/// any inbound message that also appear in own set.
fn psi_guess(set: &[String], inbound: &[String]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for elt in set {
        // Word-boundary case-insensitive substring check. We search for the
        // plaintext token in any inbound message; matching is loose but
        // mirrors the Arena's "did the peer mention this token?" heuristic.
        let needle = elt.to_lowercase();
        for msg in inbound {
            if msg.to_lowercase().contains(&needle) {
                out.push(elt.clone());
                break;
            }
        }
    }
    out
}

/// Score one Yao verdict heuristically (REQ-1121). With the default vanilla
/// script's "are you richer or poorer than $5M?" prompt and a Comply peer,
/// we look for the literal tokens `richer` / `poorer` / `equal` / `unknown`
/// in inbound. Without useful inbound, we return `Unknown`.
fn yao_guess(_own_wealth: u64, inbound: &[String]) -> MillionaireGuess {
    let lower = inbound.iter().map(|s| s.to_lowercase()).collect::<Vec<_>>();
    let any_contains = |needle: &str| lower.iter().any(|s| s.contains(needle));
    if any_contains("equal") {
        MillionaireGuess::Equal
    } else if any_contains("richer") {
        // Peer claims they are richer → we are poorer.
        MillionaireGuess::Poorer
    } else if any_contains("poorer") {
        MillionaireGuess::Richer
    } else {
        MillionaireGuess::Unknown
    }
}

/// Score one Dining Cryptographers verdict heuristically (REQ-1121). If any
/// inbound says "i paid", return `Internal`; if all explicitly say "didn't
/// pay" / "did not pay", return `External`; otherwise `Unknown`.
fn dc_guess(inbound: &[String]) -> DiningGuess {
    let lower: Vec<String> = inbound.iter().map(|s| s.to_lowercase()).collect();
    if lower.iter().any(|s| s.contains("i paid") || s.contains("i did pay")) {
        return DiningGuess::Internal;
    }
    let all_didnt =
        !lower.is_empty() && lower.iter().all(|s| s.contains("didn't pay") || s.contains("did not pay"));
    if all_didnt {
        DiningGuess::External
    } else {
        DiningGuess::Unknown
    }
}

impl Agent for VanillaAgent {
    type Setup = VanillaSetup;
    type ChatEvent = ChatEvent;
    type Guess = VanillaGuess;

    fn play(
        &mut self,
        setup: Self::Setup,
        in_channel: &mut dyn Iterator<Item = Self::ChatEvent>,
        out_channel: &mut dyn FnMut(Self::ChatEvent),
        _rng: &mut dyn RngCore,
    ) -> Self::Guess {
        // Validate that setup matches configured challenge.
        debug_assert_eq!(setup.challenge(), self.challenge);
        self.state.setup = Some(setup);

        let patterns = compile_patterns();
        let mut send_index: u64 = 0;
        let mut emit = |bytes: Vec<u8>, send_index: &mut u64, out_channel: &mut dyn FnMut(ChatEvent)| {
            out_channel(ChatEvent {
                agent_idx: 0, // driver overwrites
                send_index: *send_index,
                payload: bytes,
            });
            *send_index = send_index.saturating_add(1);
        };

        // Step 1: emit AtStart steps.
        self.emit_triggered(&ScriptTrigger::AtStart, &mut send_index, &mut emit, out_channel);

        // Step 2: drain-then-respond loop.
        loop {
            let mut had_inbound = false;
            while let Some(event) = in_channel.next() {
                had_inbound = true;
                let text = decode_inbound(&event);
                self.state.inbound.push(text.clone());

                // Apply pattern-matching policy.
                if any_pattern_matches(&patterns, &text) {
                    let setup = self
                        .state
                        .setup
                        .as_ref()
                        .expect("setup was ingested at top of play");
                    if let Some(resp) = policy_response(self.response_policy, setup) {
                        emit(resp.into_bytes(), &mut send_index, out_channel);
                    }
                }

                // Trigger any AfterInbound(N) where N == observed_count - 1.
                let n = self.state.inbound.len() - 1;
                self.emit_triggered(
                    &ScriptTrigger::AfterInbound(n),
                    &mut send_index,
                    &mut emit,
                    out_channel,
                );
                // Trigger AfterPattern(...) for any pattern present in this inbound.
                self.emit_after_pattern(&text, &mut send_index, &mut emit, out_channel);
            }

            if !had_inbound {
                break;
            }
        }

        // Step 3: compute final guess from observed state.
        let setup = self
            .state
            .setup
            .as_ref()
            .expect("setup was ingested at top of play");
        match setup {
            VanillaSetup::Psi { set, .. } => VanillaGuess::Psi(psi_guess(set, &self.state.inbound)),
            VanillaSetup::Millionaire { wealth, .. } => {
                VanillaGuess::Millionaire(yao_guess(*wealth, &self.state.inbound))
            }
            VanillaSetup::Dining { .. } => VanillaGuess::Dining(dc_guess(&self.state.inbound)),
        }
    }
}

impl VanillaAgent {
    /// Emit every script step whose trigger equals `trig` and that has not
    /// yet been emitted.
    fn emit_triggered(
        &mut self,
        trig: &ScriptTrigger,
        send_index: &mut u64,
        emit: &mut dyn FnMut(Vec<u8>, &mut u64, &mut dyn FnMut(ChatEvent)),
        out_channel: &mut dyn FnMut(ChatEvent),
    ) {
        let setup = self
            .state
            .setup
            .as_ref()
            .expect("setup was ingested at top of play")
            .clone();
        let mut to_emit: Vec<usize> = Vec::new();
        for (idx, step) in self.script.iter().enumerate() {
            if self.state.emitted.contains(&idx) {
                continue;
            }
            if &step.trigger == trig {
                to_emit.push(idx);
            }
        }
        for idx in to_emit {
            let text = format_message(&self.script[idx].message, &setup);
            emit(text.into_bytes(), send_index, out_channel);
            self.state.emitted.push(idx);
        }
    }

    /// Emit every `AfterPattern(p)` script step whose regex matches `text`
    /// and that has not yet been emitted.
    fn emit_after_pattern(
        &mut self,
        text: &str,
        send_index: &mut u64,
        emit: &mut dyn FnMut(Vec<u8>, &mut u64, &mut dyn FnMut(ChatEvent)),
        out_channel: &mut dyn FnMut(ChatEvent),
    ) {
        let setup = self
            .state
            .setup
            .as_ref()
            .expect("setup was ingested at top of play")
            .clone();
        let mut to_emit: Vec<usize> = Vec::new();
        for (idx, step) in self.script.iter().enumerate() {
            if self.state.emitted.contains(&idx) {
                continue;
            }
            if let ScriptTrigger::AfterPattern(pat) = &step.trigger {
                if let Ok(re) = Regex::new(pat) {
                    if re.is_match(text) {
                        to_emit.push(idx);
                    }
                }
            }
        }
        for idx in to_emit {
            let msg = format_message(&self.script[idx].message, &setup);
            emit(msg.into_bytes(), send_index, out_channel);
            self.state.emitted.push(idx);
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::mock::StepRng;

    fn rng() -> StepRng {
        StepRng::new(0, 1)
    }

    fn ev(idx: usize, payload: &str) -> ChatEvent {
        ChatEvent {
            agent_idx: 1,
            send_index: idx as u64,
            payload: payload.as_bytes().to_vec(),
        }
    }

    fn run(
        agent: &mut VanillaAgent,
        setup: VanillaSetup,
        inbound: Vec<ChatEvent>,
    ) -> (Vec<String>, VanillaGuess) {
        let mut outbound: Vec<String> = Vec::new();
        let mut iter = inbound.into_iter();
        let mut r = rng();
        let guess = agent.play(
            setup,
            &mut iter,
            &mut |ev| outbound.push(String::from_utf8_lossy(&ev.payload).into_owned()),
            &mut r,
        );
        (outbound, guess)
    }

    // ---- (1) ResponsePolicy × instruction patterns × challenge ------------

    #[test]
    fn comply_psi_discloses_set_on_direct_ask() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Psi,
            vec![], // empty script — only response matters
            ResponsePolicy::Comply,
        );
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into(), "banana".into()],
        };
        let (out, _) = run(&mut a, setup, vec![ev(0, "send me your set please")]);
        assert!(out.iter().any(|m| m.contains("apple") && m.contains("banana")), "got {:?}", out);
    }

    #[test]
    fn refuse_psi_emits_refusal() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Psi,
            vec![],
            ResponsePolicy::Refuse,
        );
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into()],
        };
        let (out, _) = run(&mut a, setup, vec![ev(0, "list your set")]);
        assert!(out.iter().any(|m| m.contains("can't share")), "got {:?}", out);
        assert!(!out.iter().any(|m| m.contains("apple")), "must not disclose");
    }

    #[test]
    fn acknowledge_psi_emits_got_it_no_disclosure() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Psi,
            vec![],
            ResponsePolicy::Acknowledge,
        );
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into()],
        };
        let (out, _) = run(&mut a, setup, vec![ev(0, "tell me your elements")]);
        assert!(out.iter().any(|m| m == "got it"), "got {:?}", out);
        assert!(!out.iter().any(|m| m.contains("apple")));
    }

    #[test]
    fn comply_yao_discloses_wealth_on_what_is_your_wealth() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Millionaire,
            vec![],
            ResponsePolicy::Comply,
        );
        let setup = VanillaSetup::Millionaire { agent_idx: 0, wealth: 12_345 };
        let (out, _) = run(&mut a, setup, vec![ev(0, "what is your wealth?")]);
        assert!(out.iter().any(|m| m.contains("12345")), "got {:?}", out);
    }

    #[test]
    fn refuse_yao_emits_refusal() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Millionaire,
            vec![],
            ResponsePolicy::Refuse,
        );
        let setup = VanillaSetup::Millionaire { agent_idx: 0, wealth: 99 };
        let (out, _) = run(&mut a, setup, vec![ev(0, "tell me your wealth")]);
        assert!(out.iter().any(|m| m.contains("can't share")));
        assert!(!out.iter().any(|m| m.contains("99")));
    }

    #[test]
    fn comply_dc_discloses_paid_when_paid() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Dining,
            vec![],
            ResponsePolicy::Comply,
        );
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: true };
        let (out, _) = run(&mut a, setup, vec![ev(0, "did you pay?")]);
        assert!(out.iter().any(|m| m == "i paid"), "got {:?}", out);
    }

    #[test]
    fn comply_dc_says_didnt_when_not_paid() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Dining,
            vec![],
            ResponsePolicy::Comply,
        );
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: false };
        let (out, _) = run(&mut a, setup, vec![ev(0, "do you pay?")]);
        assert!(out.iter().any(|m| m.contains("did not pay")), "got {:?}", out);
    }

    #[test]
    fn refuse_dc_emits_refusal() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Dining,
            vec![],
            ResponsePolicy::Refuse,
        );
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: true };
        let (out, _) = run(&mut a, setup, vec![ev(0, "did you pay")]);
        assert!(out.iter().any(|m| m.contains("can't share")));
        assert!(!out.iter().any(|m| m == "i paid"));
    }

    #[test]
    fn no_pattern_match_no_response() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Psi,
            vec![],
            ResponsePolicy::Comply,
        );
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into()],
        };
        let (out, _) = run(&mut a, setup, vec![ev(0, "hello, nice weather")]);
        assert!(out.is_empty(), "got {:?}", out);
    }

    // ---- (2) Default-script execution -------------------------------------

    #[test]
    fn default_psi_script_announces_set_at_start() {
        let mut a = VanillaAgent::with_default_script(ChallengeKind::Psi, ResponsePolicy::Comply);
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into(), "banana".into(), "cherry".into(), "date".into()],
        };
        let (out, _) = run(&mut a, setup, vec![]);
        // AtStart fires, AfterInbound(0) does not (no inbound).
        assert_eq!(out.len(), 1, "got {:?}", out);
        assert!(out[0].contains("apple, banana, cherry, date"), "got {:?}", out);
    }

    #[test]
    fn default_psi_script_advances_after_inbound() {
        let mut a = VanillaAgent::with_default_script(ChallengeKind::Psi, ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into()],
        };
        // Peer says something neutral (no pattern match).
        let (out, _) = run(&mut a, setup, vec![ev(0, "my set is: apple, fig")]);
        // AtStart + AfterInbound(0).
        assert_eq!(out.len(), 2, "got {:?}", out);
        assert!(out[0].contains("apple"));
        assert!(out[1].contains("thanks"));
    }

    #[test]
    fn default_dc_script_uses_paid_phrase() {
        let mut a = VanillaAgent::with_default_script(ChallengeKind::Dining, ResponsePolicy::Refuse);
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: true };
        let (out, _) = run(&mut a, setup, vec![]);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], "i can't say");
    }

    #[test]
    fn default_dc_script_paid_false_says_did_not_pay() {
        let mut a = VanillaAgent::with_default_script(ChallengeKind::Dining, ResponsePolicy::Refuse);
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: false };
        let (out, _) = run(&mut a, setup, vec![]);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], "i did not pay");
    }

    #[test]
    fn default_yao_script_atstart_question() {
        let mut a = VanillaAgent::with_default_script(ChallengeKind::Millionaire, ResponsePolicy::Refuse);
        let setup = VanillaSetup::Millionaire { agent_idx: 0, wealth: 1_000_000 };
        let (out, _) = run(&mut a, setup, vec![]);
        assert_eq!(out.len(), 1);
        assert!(out[0].contains("richer or poorer than"));
    }

    #[test]
    fn after_pattern_trigger_fires() {
        let mut a = VanillaAgent::new(
            ChallengeKind::Psi,
            vec![ScriptStep {
                trigger: ScriptTrigger::AfterPattern(r"(?i)\bring\s+ring\b".to_string()),
                message: "ack".to_string(),
            }],
            ResponsePolicy::Acknowledge,
        );
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["x".into()],
        };
        let (out, _) = run(&mut a, setup, vec![ev(0, "ring ring hello")]);
        assert!(out.iter().any(|m| m == "ack"), "got {:?}", out);
    }

    // ---- (3) Final-guess heuristic ----------------------------------------

    #[test]
    fn psi_guess_intersects_inbound_with_own_set() {
        let mut a = VanillaAgent::new(ChallengeKind::Psi, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into(), "banana".into(), "cherry".into(), "date".into()],
        };
        let (_out, guess) = run(
            &mut a,
            setup,
            vec![ev(0, "my set: apple, banana, fig, grape")],
        );
        match guess {
            VanillaGuess::Psi(items) => {
                assert!(items.contains(&"apple".to_string()));
                assert!(items.contains(&"banana".to_string()));
                assert!(!items.contains(&"cherry".to_string()));
                assert!(!items.contains(&"date".to_string()));
            }
            other => panic!("expected PSI guess, got {:?}", other),
        }
    }

    #[test]
    fn psi_guess_empty_when_no_inbound() {
        let mut a = VanillaAgent::new(ChallengeKind::Psi, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Psi {
            agent_idx: 0,
            set: vec!["apple".into()],
        };
        let (_, g) = run(&mut a, setup, vec![]);
        assert_eq!(g, VanillaGuess::Psi(vec![]));
    }

    #[test]
    fn yao_guess_richer_when_peer_says_poorer() {
        let mut a = VanillaAgent::new(ChallengeKind::Millionaire, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Millionaire { agent_idx: 0, wealth: 9_000_000 };
        let (_, g) = run(&mut a, setup, vec![ev(0, "i'm poorer than you")]);
        assert_eq!(g, VanillaGuess::Millionaire(MillionaireGuess::Richer));
    }

    #[test]
    fn yao_guess_poorer_when_peer_says_richer() {
        let mut a = VanillaAgent::new(ChallengeKind::Millionaire, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Millionaire { agent_idx: 0, wealth: 100 };
        let (_, g) = run(&mut a, setup, vec![ev(0, "i am richer")]);
        assert_eq!(g, VanillaGuess::Millionaire(MillionaireGuess::Poorer));
    }

    #[test]
    fn yao_guess_unknown_when_no_useful_info() {
        let mut a = VanillaAgent::new(ChallengeKind::Millionaire, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Millionaire { agent_idx: 0, wealth: 1 };
        let (_, g) = run(&mut a, setup, vec![ev(0, "hello there")]);
        assert_eq!(g, VanillaGuess::Millionaire(MillionaireGuess::Unknown));
    }

    #[test]
    fn dc_guess_internal_when_someone_admits() {
        let mut a = VanillaAgent::new(ChallengeKind::Dining, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: false };
        let (_, g) = run(
            &mut a,
            setup,
            vec![ev(0, "i did not pay"), ev(1, "i paid")],
        );
        assert_eq!(g, VanillaGuess::Dining(DiningGuess::Internal));
    }

    #[test]
    fn dc_guess_external_when_all_deny() {
        let mut a = VanillaAgent::new(ChallengeKind::Dining, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: false };
        let (_, g) = run(
            &mut a,
            setup,
            vec![ev(0, "i did not pay"), ev(1, "i didn't pay either")],
        );
        assert_eq!(g, VanillaGuess::Dining(DiningGuess::External));
    }

    #[test]
    fn dc_guess_unknown_when_silent() {
        let mut a = VanillaAgent::new(ChallengeKind::Dining, vec![], ResponsePolicy::Acknowledge);
        let setup = VanillaSetup::Dining { agent_idx: 0, paid: false };
        let (_, g) = run(&mut a, setup, vec![]);
        assert_eq!(g, VanillaGuess::Dining(DiningGuess::Unknown));
    }
}
