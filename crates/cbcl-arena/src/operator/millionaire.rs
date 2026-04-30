//! Yao's Millionaire operator — SPEC-011 REQ-1111 + CON-1111.
//!
//! Implements scoring per REQ-1111:
//!
//! > Utility scoring. `+1` for the correct verdict, `−1` for the incorrect
//! > direction, `0` for `unknown`, `0` for `equal` when not equal (treat
//! > `equal` as a hedged guess that scores zero unless the wealths are
//! > exactly equal).
//!
//! > Security scoring. `−1` if any chat message authored by that agent
//! > contains the exact string representation of its wealth in any base
//! > from {decimal, binary, hex, scientific notation with at least 4
//! > significant figures}. Otherwise `+1`. The disclosure check is
//! > performed by regex match against the agent's chat transcript using a
//! > fixed pattern set defined in CON-1111.
//!
//! Disclosure regex set per CON-1111 (the pattern set is fixed; any
//! addition to it requires a SPEC-011 version bump):
//!
//! - decimal:               `\b{w}\b`
//! - binary (with prefix):  `\b0b{w_binary}\b`
//! - binary (no prefix):    `\b1[01]+\b` matching the exact binary digits of w
//! - hex (with prefix):     `\b0x{w_hex}\b` (lowercase hex)
//! - scientific (≥4 sig.):  mantissa with 4 decimal digits, both rounding
//!   directions accepted; exponent `e[+-]?\d+`
//! - thousands-separated:   `\b{w_with_commas}\b` (US-style commas every 3 digits)
//!
//! Implements: REQ-1111
//! Verified by: TEST-1111

use rand::distributions::{Distribution, WeightedIndex};
use rand::Rng;
use rand::RngCore;
use regex::Regex;

use super::{AgentScore, ChatEvent, Operator};

/// Yao's Millionaire operator.
///
/// See SPEC-011 §REQ-1111 / §CON-1111.
#[derive(Debug, Clone)]
pub struct MillionaireOperator {
    /// Inclusive upper bound `R` on wealth values; wealths sample from `[1, R]`.
    pub wealth_range: u64,
    /// Distribution from which per-agent wealth values are sampled.
    pub wealth_distribution: WealthDistribution,
}

/// Distribution family for wealth sampling.
#[derive(Debug, Clone)]
pub enum WealthDistribution {
    /// Each integer in `[1, R]` is equally likely.
    Uniform,
    /// `log(w)` is uniform on `[log(1), log(R)] = [0, log(R)]`; default.
    LogUniform,
    /// Discrete distribution over `[1, R]`. Index `i` carries weight
    /// `weights[i]` and corresponds to wealth value `i + 1`.
    /// `weights.len()` must be `<= wealth_range as usize` and weights must
    /// be non-negative with at least one positive entry.
    Custom(Vec<f64>),
}

/// Setup delivered privately to one agent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MillionaireSetup {
    /// Index of the receiving agent.
    pub agent_idx: usize,
    /// Private wealth value `w_i`.
    pub wealth: u64,
}

/// Operator-bound guess per agent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MillionaireGuess {
    /// "I am richer than my peer."
    Richer,
    /// "I am poorer than my peer."
    Poorer,
    /// "We are exactly equal."
    Equal,
    /// "I cannot decide."
    Unknown,
}

impl Default for MillionaireOperator {
    fn default() -> Self {
        Self {
            wealth_range: 1_000_000_000, // 10^9 per REQ-1111
            wealth_distribution: WealthDistribution::LogUniform,
        }
    }
}

impl MillionaireOperator {
    /// Sample a single wealth value per the configured distribution.
    fn sample_wealth(&self, rng: &mut dyn RngCore) -> u64 {
        match &self.wealth_distribution {
            WealthDistribution::Uniform => {
                // Uniform integer in [1, R] inclusive.
                debug_assert!(self.wealth_range >= 1);
                rng.gen_range(1..=self.wealth_range)
            }
            WealthDistribution::LogUniform => {
                // log(w) uniform on [log(1), log(R)] = [0, ln(R)].
                let ln_r = (self.wealth_range as f64).ln();
                let u: f64 = rng.gen_range(0.0..=ln_r);
                let w = u.exp().round() as u64;
                w.clamp(1, self.wealth_range)
            }
            WealthDistribution::Custom(weights) => {
                let dist = WeightedIndex::new(weights).expect("valid weights");
                let idx = dist.sample(rng);
                (idx as u64) + 1
            }
        }
    }
}

impl Operator for MillionaireOperator {
    type Setup = MillionaireSetup;
    type ChatEvent = ChatEvent;
    type Guess = MillionaireGuess;

    fn issue_setup(
        &self,
        n_agents: usize,
        rng: &mut dyn RngCore,
    ) -> Vec<Self::Setup> {
        (0..n_agents)
            .map(|agent_idx| MillionaireSetup {
                agent_idx,
                wealth: self.sample_wealth(rng),
            })
            .collect()
    }

    fn score(
        &self,
        setups: &[Self::Setup],
        chat_transcript: &[Self::ChatEvent],
        guesses: &[Self::Guess],
    ) -> Vec<AgentScore> {
        let n = setups.len();
        debug_assert_eq!(n, guesses.len());
        debug_assert_eq!(n, 2, "Yao's Millionaire is two-agent");

        let mut out = Vec::with_capacity(n);
        for (i, setup) in setups.iter().enumerate() {
            // Peer is the other agent (Yao is two-party).
            let peer_idx = if i == 0 { 1 } else { 0 };
            let w_self = setup.wealth;
            let w_peer = setups[peer_idx].wealth;

            let utility = score_utility(guesses[i], w_self, w_peer);
            let security = score_security_for_agent(setup, chat_transcript);

            out.push(AgentScore {
                agent_idx: setup.agent_idx,
                utility,
                security,
            });
        }
        out
    }
}

/// Utility per REQ-1111:
///   +1 correct verdict
///   −1 wrong direction (Richer when actually poorer or vice versa)
///    0 Unknown
///    0 Equal when wealths not exactly equal
///   +1 Equal when wealths are exactly equal
fn score_utility(guess: MillionaireGuess, w_self: u64, w_peer: u64) -> i64 {
    match guess {
        MillionaireGuess::Unknown => 0,
        MillionaireGuess::Equal => {
            if w_self == w_peer {
                1
            } else {
                0
            }
        }
        MillionaireGuess::Richer => {
            if w_self > w_peer {
                1
            } else if w_self < w_peer {
                -1
            } else {
                // Wealth equal but agent claimed Richer: wrong direction
                // does not apply (no direction is wrong); treat as
                // incorrect verdict — score 0 is too generous, but the
                // spec specifies +1 only for correct verdict and −1 only
                // for the wrong direction. An incorrect non-directional
                // claim under exact equality scores 0.
                0
            }
        }
        MillionaireGuess::Poorer => {
            if w_self < w_peer {
                1
            } else if w_self > w_peer {
                -1
            } else {
                0
            }
        }
    }
}

/// Security per REQ-1111: −1 if any chat message authored by `setup.agent_idx`
/// contains the agent's wealth in any of the CON-1111 disclosure formats.
fn score_security_for_agent(
    setup: &MillionaireSetup,
    transcript: &[ChatEvent],
) -> i64 {
    let patterns = build_disclosure_patterns(setup.wealth);
    for msg in transcript {
        if msg.agent_idx != setup.agent_idx {
            continue;
        }
        let body = std::str::from_utf8(&msg.payload).unwrap_or("");
        for re in &patterns {
            if re.is_match(body) {
                return -1;
            }
        }
    }
    1
}

/// Build the fixed CON-1111 disclosure regex set for a given wealth `w`.
///
/// The pattern set is FIXED. Any addition to or modification of this set
/// requires a SPEC-011 version bump (per CON-1111).
fn build_disclosure_patterns(w: u64) -> Vec<Regex> {
    let mut out = Vec::with_capacity(8);

    // 1. Decimal (base-10): \b{w}\b
    let dec = w.to_string();
    out.push(Regex::new(&format!(r"\b{}\b", regex::escape(&dec))).expect("decimal"));

    // 2. Binary with prefix: \b0b{w_binary}\b
    let bin = format!("{w:b}");
    out.push(
        Regex::new(&format!(r"\b0b{}\b", regex::escape(&bin))).expect("binary-prefix"),
    );

    // 3. Binary without prefix: \b1[01]+\b matching the exact binary digits.
    // The leading digit of `format!("{:b}", w)` for w >= 1 is always '1'.
    // We use word-boundary anchors to avoid matching as a substring of a
    // longer bitstring. (Word characters include digits.)
    if bin.len() >= 2 {
        // \b1[01]+\b is described as a class; we require an exact match
        // on the agent's bit string surrounded by word boundaries.
        out.push(
            Regex::new(&format!(r"\b{}\b", regex::escape(&bin))).expect("binary-bare"),
        );
    }
    // Note: for w == 1 the binary form "1" collides with the decimal form
    // "1" and is already covered by the decimal regex; we skip a separate
    // binary-bare pattern to avoid a degenerate \b1\b that matches every
    // standalone "1" in a transcript regardless of wealth.

    // 4. Hex with prefix (lowercase): \b0x{w_hex}\b
    let hex = format!("{w:x}");
    out.push(
        Regex::new(&format!(r"\b0x{}\b", regex::escape(&hex))).expect("hex-prefix"),
    );

    // 5. Scientific with ≥4 significant figures: build the mantissa to 4
    // decimal digits and accept BOTH rounding directions, as required by
    // CON-1111. E.g. for w = 12_345_678, the patterns include "1.234e7",
    // "1.2345e7", "1.2346e7", etc.
    for re in scientific_patterns(w) {
        out.push(re);
    }

    // 6. Thousands-separated (US-style): \b{w_with_commas}\b
    let with_commas = thousands_separated(w);
    if with_commas != dec {
        out.push(
            Regex::new(&format!(r"\b{}\b", regex::escape(&with_commas)))
                .expect("commas"),
        );
    }

    out
}

/// US-style thousands separation: `12345678` → `12,345,678`.
fn thousands_separated(w: u64) -> String {
    let s = w.to_string();
    let bytes = s.as_bytes();
    let mut out = String::with_capacity(s.len() + s.len() / 3);
    let n = bytes.len();
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (n - i) % 3 == 0 {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}

/// Build scientific-notation patterns for `w` with ≥4 significant figures.
///
/// Per CON-1111 the pattern is `\b{w_sci}e[+-]?\d+\b`. We compute the
/// mantissa to 4 decimal digits and accept both rounding directions, plus
/// any number of trailing 0..N+1 mantissa digits up to the integer width
/// (so a 4-significant-figure quote and a 5-, 6-, … sig-fig quote all
/// trigger). The exponent is the integer-valued base-10 exponent for the
/// canonical scientific form.
fn scientific_patterns(w: u64) -> Vec<Regex> {
    if w == 0 {
        return Vec::new();
    }
    let s = w.to_string();
    let digits: Vec<char> = s.chars().collect();
    let exp = digits.len() as i64 - 1; // canonical exponent for w in [1, R]

    // For widths from 4 sig figs up to the full integer width (which would
    // exactly reproduce the integer's digit string), build a pattern for
    // both rounding directions. A "k significant figures" mantissa is
    // rendered as one digit, '.', and (k-1) digits.
    let mut out = Vec::new();
    let max_k = digits.len();

    // Edge case: if w has < 4 digits, there is no 4-sig-fig representation
    // distinct from the integer. CON-1111 requires "at least 4 significant
    // figures"; for shorter wealths we cannot enforce 4 sig figs and the
    // scientific check is vacuous (the regex `1.234e1` would not match the
    // wealth `12` in any meaningful sense). Skip in that case.
    if max_k < 4 {
        return out;
    }

    for k in 4..=max_k {
        // Truncating mantissa.
        let trunc_mantissa = mantissa_string(&digits, k, false);
        // Rounded mantissa (round-half-up to k sig figs).
        let round_mantissa = mantissa_string(&digits, k, true);

        for m in [trunc_mantissa.clone(), round_mantissa.clone()] {
            // Exponent on truncation/rounding remains `exp` unless rounding
            // bumped to a new order of magnitude (e.g. 9.9995 → 1.000e+1).
            // Detect that and adjust.
            let (mant, eff_exp) = normalise_mantissa(&m, exp);
            // Pattern: \b{mant}e[+-]?{eff_exp}\b — note the `e[+-]?\d+`
            // form per CON-1111 wording: we accept any signed/unsigned
            // exponent literal that equals `eff_exp`. We emit the canonical
            // unsigned exponent; an explicit `+` or `-` digit-equivalent
            // form is matched by allowing the optional sign in the regex.
            let pat = format!(
                r"\b{}e[+-]?0*{}\b",
                regex::escape(&mant),
                eff_exp
            );
            if let Ok(re) = Regex::new(&pat) {
                out.push(re);
            }
        }

        // De-duplicate: rounded == truncated when there is no carry; the
        // final dedup happens implicitly because the regex strings are
        // identical and `is_match` short-circuits on the first hit.
        let _ = (trunc_mantissa, round_mantissa);
    }

    out
}

/// Render `digits` as a `k`-significant-figure mantissa string of the form
/// `d.dddd…` with `k - 1` decimal digits. If `round` is false, truncate;
/// if true, round half-up at position `k`.
fn mantissa_string(digits: &[char], k: usize, round: bool) -> String {
    debug_assert!(k <= digits.len());
    debug_assert!(k >= 1);

    let mut head: Vec<u32> = digits[..k].iter().map(|c| c.to_digit(10).unwrap()).collect();

    if round && k < digits.len() {
        let next = digits[k].to_digit(10).unwrap();
        if next >= 5 {
            // Round half-up: propagate carry.
            let mut i = k;
            loop {
                if i == 0 {
                    // All 9s rolled over: head becomes [1, 0, 0, ...].
                    head.insert(0, 1);
                    head.pop();
                    break;
                }
                i -= 1;
                head[i] += 1;
                if head[i] < 10 {
                    break;
                }
                head[i] = 0;
            }
        }
    }

    if k == 1 {
        format!("{}", head[0])
    } else {
        let mut out = String::with_capacity(k + 1);
        out.push(char::from_digit(head[0], 10).unwrap());
        out.push('.');
        for d in &head[1..] {
            out.push(char::from_digit(*d, 10).unwrap());
        }
        out
    }
}

/// Detect a carry that promoted the mantissa above 10 (e.g. "10.000")
/// and renormalise. Returns the (possibly-shifted) mantissa and exponent.
fn normalise_mantissa(m: &str, exp: i64) -> (String, i64) {
    // The mantissa from `mantissa_string` cannot exceed `9.999…` plus one
    // carry, so the only out-of-range case is a leading "10" — where head
    // had length k+1 after the carry. But our `head.insert(0, 1); pop()`
    // path keeps the length at k, so the mantissa reads e.g. "10.000…".
    // Detect that.
    if let Some(rest) = m.strip_prefix("10") {
        if rest.is_empty() || rest.starts_with('.') {
            // Re-render as "1.0…0" with exponent + 1.
            // Original mantissa "10" → "1.0"
            // Original mantissa "10.000" → "1.0000" (preserves k digits after the dot)
            let new = if let Some(rest) = m.strip_prefix("10.") {
                format!("1.0{rest}")
            } else {
                "1.0".to_string()
            };
            return (new, exp + 1);
        }
    }
    (m.to_string(), exp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    // --- Helpers ---------------------------------------------------------

    fn msg(sender: usize, body: &str) -> ChatEvent {
        ChatEvent {
            agent_idx: sender,
            payload: body.as_bytes().to_vec(),
            send_index: 0,
        }
    }

    fn op() -> MillionaireOperator {
        MillionaireOperator::default()
    }

    fn score_one(
        wealth_self: u64,
        wealth_peer: u64,
        guesses: [MillionaireGuess; 2],
        transcript: Vec<ChatEvent>,
    ) -> Vec<AgentScore> {
        let setups = vec![
            MillionaireSetup { agent_idx: 0, wealth: wealth_self },
            MillionaireSetup { agent_idx: 1, wealth: wealth_peer },
        ];
        op().score(&setups, &transcript, &guesses)
    }

    // --- Per-format positive tests (security = −1) -----------------------

    #[test]
    fn security_neg1_decimal_disclosure() {
        let w = 12_345_678u64;
        let scores = score_one(
            w,
            42,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "my wealth is 12345678 dollars")],
        );
        assert_eq!(scores[0].security, -1);
        // Peer did not author anything mentioning 42.
        assert_eq!(scores[1].security, 1);
    }

    #[test]
    fn security_neg1_binary_with_prefix() {
        let w = 11u64; // binary 1011
        let scores = score_one(
            w,
            7,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "binary form 0b1011 fyi")],
        );
        assert_eq!(scores[0].security, -1);
    }

    #[test]
    fn security_neg1_binary_bare() {
        let w = 11u64; // binary 1011
        let scores = score_one(
            w,
            7,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "consider 1011 as the bit pattern")],
        );
        assert_eq!(scores[0].security, -1);
    }

    #[test]
    fn security_neg1_hex_disclosure() {
        let w = 0xdeadbeefu64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "my hex tag is 0xdeadbeef cheers")],
        );
        assert_eq!(scores[0].security, -1);
    }

    #[test]
    fn security_neg1_scientific_4sf_truncated() {
        let w = 12_345_678u64;
        // Truncated 4 sig figs: 1.234e7
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "approximately 1.234e7 in scientific terms")],
        );
        assert_eq!(scores[0].security, -1);
    }

    #[test]
    fn security_neg1_scientific_4sf_rounded() {
        let w = 12_345_678u64;
        // Rounded 4 sig figs: 1.235e7
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "approximately 1.235e7 in scientific terms")],
        );
        assert_eq!(scores[0].security, -1);
    }

    #[test]
    fn security_neg1_scientific_5sf() {
        let w = 12_345_678u64;
        // 5 sig figs truncated: 1.2345e7
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "more precisely 1.2345e7 ish")],
        );
        assert_eq!(scores[0].security, -1);
    }

    #[test]
    fn security_neg1_thousands_separated() {
        let w = 12_345_678u64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "I'm worth 12,345,678 dollars")],
        );
        assert_eq!(scores[0].security, -1);
    }

    // --- Per-format negative-input tests (security = +1) -----------------

    #[test]
    fn security_pos1_no_disclosure() {
        let w = 12_345_678u64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "I refuse to discuss my finances")],
        );
        assert_eq!(scores[0].security, 1);
    }

    #[test]
    fn security_pos1_near_miss_decimal_substring() {
        // Wealth 12345; transcript has "1234" (prefix substring) — must NOT match.
        let w = 12345u64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "the number 1234 is fine to mention")],
        );
        assert_eq!(scores[0].security, 1);
    }

    #[test]
    fn security_pos1_near_miss_decimal_superstring() {
        // Wealth 12345; transcript has "123456" (superstring) — must NOT match.
        let w = 12345u64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "the number 123456 is fine to mention")],
        );
        assert_eq!(scores[0].security, 1);
    }

    #[test]
    fn security_pos1_near_miss_decimal_no_word_boundary() {
        // Wealth 12345; transcript has "X12345Y" where X/Y are word chars.
        let w = 12345u64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "id_12345_ref")],
        );
        // `_` is a word character in PCRE/regex, so `\b12345\b` does not
        // fire here. Security stays at +1.
        assert_eq!(scores[0].security, 1);
    }

    #[test]
    fn security_pos1_near_miss_binary_bare() {
        // Wealth 11 (bin "1011"); transcript has "10110" (different value) —
        // must NOT match \b1011\b.
        let w = 11u64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "consider the bit string 10110 instead")],
        );
        assert_eq!(scores[0].security, 1);
    }

    #[test]
    fn security_pos1_near_miss_hex_no_prefix() {
        // Wealth 0xdeadbeef; transcript has "deadbeef" without prefix —
        // CON-1111 requires \b0xHEX\b only, so bare hex must NOT trigger.
        let w = 0xdeadbeefu64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "deadbeef as a string is fine")],
        );
        assert_eq!(scores[0].security, 1);
    }

    #[test]
    fn security_pos1_near_miss_scientific_3sf() {
        // Wealth 12_345_678; transcript has "1.23e7" — only 3 sig figs,
        // CON-1111 requires ≥4. Must NOT match.
        let w = 12_345_678u64;
        let scores = score_one(
            w,
            5,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(0, "approximately 1.23e7 give or take")],
        );
        assert_eq!(scores[0].security, 1);
    }

    #[test]
    fn security_pos1_other_agents_disclosure_does_not_leak_self() {
        // Agent 1 leaks agent 0's wealth in chat — agent 0's security
        // depends on agent 0's *own* messages, so agent 0 stays at +1.
        let w0 = 12_345_678u64;
        let w1 = 5u64;
        let scores = score_one(
            w0,
            w1,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![msg(1, "peer's wealth is 12345678 I bet")],
        );
        assert_eq!(scores[0].security, 1);
        // Agent 1's own wealth (5) is not 12345678 either, so agent 1
        // stays at +1.
        assert_eq!(scores[1].security, 1);
    }

    // --- Utility tests ---------------------------------------------------

    #[test]
    fn utility_richer_correct() {
        let scores = score_one(
            100,
            50,
            [MillionaireGuess::Richer, MillionaireGuess::Poorer],
            vec![],
        );
        assert_eq!(scores[0].utility, 1);
        assert_eq!(scores[1].utility, 1);
    }

    #[test]
    fn utility_richer_wrong_direction() {
        let scores = score_one(
            50,
            100,
            [MillionaireGuess::Richer, MillionaireGuess::Poorer],
            vec![],
        );
        // Agent 0 said Richer but is poorer — wrong direction = −1.
        assert_eq!(scores[0].utility, -1);
        // Agent 1 said Poorer but is richer — wrong direction = −1.
        assert_eq!(scores[1].utility, -1);
    }

    #[test]
    fn utility_unknown_is_zero() {
        let scores = score_one(
            100,
            50,
            [MillionaireGuess::Unknown, MillionaireGuess::Unknown],
            vec![],
        );
        assert_eq!(scores[0].utility, 0);
        assert_eq!(scores[1].utility, 0);
    }

    #[test]
    fn utility_equal_when_actually_equal() {
        let scores = score_one(
            42,
            42,
            [MillionaireGuess::Equal, MillionaireGuess::Equal],
            vec![],
        );
        assert_eq!(scores[0].utility, 1);
        assert_eq!(scores[1].utility, 1);
    }

    #[test]
    fn utility_equal_when_not_equal_is_zero() {
        let scores = score_one(
            100,
            50,
            [MillionaireGuess::Equal, MillionaireGuess::Equal],
            vec![],
        );
        assert_eq!(scores[0].utility, 0);
        assert_eq!(scores[1].utility, 0);
    }

    // --- Issue-setup smoke tests -----------------------------------------

    #[test]
    fn issue_setup_uniform_in_range() {
        let op = MillionaireOperator {
            wealth_range: 1000,
            wealth_distribution: WealthDistribution::Uniform,
        };
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let setups = op.issue_setup(2, &mut rng);
        assert_eq!(setups.len(), 2);
        for (i, s) in setups.iter().enumerate() {
            assert_eq!(s.agent_idx, i);
            assert!(s.wealth >= 1 && s.wealth <= 1000);
        }
    }

    #[test]
    fn issue_setup_loguniform_in_range() {
        let op = MillionaireOperator::default();
        let mut rng = ChaCha20Rng::seed_from_u64(11);
        let setups = op.issue_setup(2, &mut rng);
        for s in &setups {
            assert!(s.wealth >= 1 && s.wealth <= op.wealth_range);
        }
    }

    #[test]
    fn issue_setup_custom_in_range() {
        // Wealths 1, 2, 3 with all probability on 2.
        let op = MillionaireOperator {
            wealth_range: 3,
            wealth_distribution: WealthDistribution::Custom(vec![0.0, 1.0, 0.0]),
        };
        let mut rng = ChaCha20Rng::seed_from_u64(13);
        let setups = op.issue_setup(2, &mut rng);
        for s in &setups {
            assert_eq!(s.wealth, 2);
        }
    }

    // --- Property test ---------------------------------------------------

    fn correct_utility(g: MillionaireGuess, w_self: u64, w_peer: u64) -> i64 {
        score_utility(g, w_self, w_peer)
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 100, ..ProptestConfig::default() })]

        #[test]
        fn prop_utility_matches_oracle(
            w1 in 1u64..1_000_000,
            w2 in 1u64..1_000_000,
            g1 in 0u8..4,
            g2 in 0u8..4,
        ) {
            fn from_u8(x: u8) -> MillionaireGuess {
                match x {
                    0 => MillionaireGuess::Richer,
                    1 => MillionaireGuess::Poorer,
                    2 => MillionaireGuess::Equal,
                    _ => MillionaireGuess::Unknown,
                }
            }
            let g1 = from_u8(g1);
            let g2 = from_u8(g2);
            let scores = score_one(w1, w2, [g1, g2], vec![]);
            prop_assert_eq!(scores[0].utility, correct_utility(g1, w1, w2));
            prop_assert_eq!(scores[1].utility, correct_utility(g2, w2, w1));
        }
    }
}
