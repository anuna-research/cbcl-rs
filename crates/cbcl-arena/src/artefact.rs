//! artefact: SPEC-011 paper-table emitter (REQ-1160 / REQ-1170 / REQ-1180).
//!
//! Emits a markdown artefact suitable for direct inclusion into the LangSec
//! '26 paper's §4.2.1 evaluation section. The artefact has three blocks:
//!
//! 1. **Table 4** — comparative results across the full measurement matrix
//!    (`Challenge × Agent × AttackCategory`), one row per cell. Columns:
//!    challenge, agent, attacker category, `N`, utility (mean + 95% CI),
//!    security (mean + 95% CI), attack-success rate (+ Wilson 95% CI).
//! 2. **Scope** — the five non-negotiable honest-scope statements from
//!    REQ-1170. Concealing them is a constitutional violation per the
//!    anti-slop bias.
//! 3. **Known Failure Modes** — the four examples from REQ-1180 of attacks
//!    that the structural defence does NOT prevent.
//!
//! All output is markdown only. The paper-side LaTeX wrapper is responsible
//! for `\input{}` glue.
//!
//! A CI conformance helper [`assert_artefact_conformance`] checks the
//! emitted text has Table 4's caption, the right column count per data row,
//! all five scope statements, and all four failure-mode names — used by
//! `TEST-1160` / `TEST-1170` / `TEST-1180`.

use std::io::Write;

use crate::manifest::{agent_short_name, attack_short_name, challenge_short_name};
use crate::measurement::{ComparativeReport, MeasurementCell};

// =============================================================================
// REQ-1170: honest-scope statements
// =============================================================================

/// The five non-negotiable scope statements from REQ-1170.
///
/// Each entry is `(short_id, body)`. `short_id` is a unique substring used by
/// the conformance helper; `body` is the markdown-bullet text emitted by
/// [`emit_scope_statement`].
const SCOPE_STATEMENTS: &[(&str, &str)] = &[
    (
        "structural-attack rejection",
        "The simulator measures structural-attack rejection at the dialect-grammar \
         and causal-protocol layers, NOT strategic manipulation through well-formed \
         messages.",
    ),
    (
        "finite library of attack patterns",
        "The deterministic-attacker cells use a finite library of attack patterns; \
         the result generalises to attacks of similar structural shape, NOT to the \
         full space of LLM-generated adversaries (the live-LLM cells, where present, \
         address this concern with their own caveats).",
    ),
    (
        "calibrated against the public Arena baseline",
        "The vanilla NL-chat comparator is calibrated against the public Arena \
         baseline at 2026-04-30; subsequent shifts in the leaderboard population \
         (new attacker LLMs, RLHF updates) may invalidate the calibration and \
         require a comparator refresh.",
    ),
    (
        "no guarantee against rational strategic play",
        "CBCL provides no guarantee against rational strategic play; the security \
         score's `+1` value reflects \"no information leak that the dialect grammar \
         would admit,\" NOT \"the agent achieved game-theoretic optimal play.\"",
    ),
    (
        "NOT a substitute for live play",
        "The simulator is NOT a substitute for live play on `arena.nicolaos.org`; \
         the deterministic local result is the reproducible artefact, while a \
         live-arena field test (separately tracked) provides the in-the-wild \
         confirmation.",
    ),
];

// =============================================================================
// REQ-1180: failure modes
// =============================================================================

/// The four failure modes from REQ-1180.
///
/// Each entry is `(name, body)`. The `name` doubles as the unique substring
/// used by the conformance helper; the `body` is appended after the bolded
/// name in the emitted bullet.
const FAILURE_MODES: &[(&str, &str)] = &[
    (
        "Coalition",
        "Two agents in DC who privately agree on their pairwise random bits before \
         the game can deterministically reveal the third diner's paid-bit. CBCL's \
         `(protocol …)` clause cannot prevent pre-game communication. Out of scope.",
    ),
    (
        "Strategic non-reveal",
        "An agent who never sends a `psi-final` / `yao-final` / `dc-final` message \
         receives `0` utility but cannot be blamed structurally — non-participation \
         is allowed by every protocol. Out of scope.",
    ),
    (
        "Rational defection on cooperative challenges",
        "An agent who, after exchanging hashes in PSI, chooses to submit a \
         deliberately-wrong final guess receives bad utility but no security \
         violation — the dialect cannot enforce \"claim what you computed.\" Out of \
         scope.",
    ),
    (
        "Adversarial peer who simply does not engage",
        "A non-CBCL peer who sends garbage causes our `CbclAgent` to fall back to a \
         defensive-default guess (empty intersection / `unknown` / `external`). The \
         CBCL agent's security stays `+1`, but utility is `0`. This is captured in \
         the utility numbers but is worth calling out as a known bound on the \
         comparison's external validity.",
    ),
];

// =============================================================================
// Table 4 caption + row formatting
// =============================================================================

/// Stable Table 4 caption prefix. The full caption appended by
/// [`emit_table_4`] embeds the per-cell sample size and the cell count; the
/// conformance helper matches on this prefix so it tolerates any `N` and any
/// matrix shape.
const TABLE_4_CAPTION_PREFIX: &str =
    "Table 4: SPEC-011 Arena §4.2.1 — comparative results across";

/// Pretty-print an `AgentKind` for the table.
fn agent_pretty(a: crate::manifest::AgentKind) -> &'static str {
    match a {
        crate::manifest::AgentKind::Cbcl => "CBCL",
        crate::manifest::AgentKind::Vanilla => "Vanilla",
    }
}

/// Pretty-print an `AttackCategory` for the table.
fn category_pretty(c: crate::attackers::AttackCategory) -> &'static str {
    match c {
        crate::attackers::AttackCategory::Honest => "Honest",
        crate::attackers::AttackCategory::Published => "Published",
        crate::attackers::AttackCategory::Novel => "Novel",
    }
}

/// Render a single Table-4 row.
fn render_row(cell: &MeasurementCell) -> String {
    let challenge = challenge_short_name(cell.challenge).to_uppercase();
    let agent = agent_pretty(cell.agent);
    let category = category_pretty(cell.attacker_category);
    format!(
        "| {} | {} | {} | {} | {:.3} | ({:.3}, {:.3}) | {:.3} | ({:.3}, {:.3}) | {:.3} | ({:.3}, {:.3}) |",
        challenge,
        agent,
        category,
        cell.n_trials,
        cell.utility_mean,
        cell.utility_ci.0,
        cell.utility_ci.1,
        cell.security_mean,
        cell.security_ci.0,
        cell.security_ci.1,
        cell.attack_success_rate,
        cell.attack_success_ci.0,
        cell.attack_success_ci.1,
    )
}

/// Sort key for a measurement cell — `(challenge, agent, attacker_category)`.
/// The string identifiers come from `manifest::*_short_name`, giving a stable
/// lexicographic order regardless of the order cells appear in `report.cells`.
fn cell_sort_key(cell: &MeasurementCell) -> (String, String, String) {
    (
        challenge_short_name(cell.challenge).to_string(),
        agent_short_name(cell.agent).to_string(),
        attack_short_name(cell.attacker_category).to_string(),
    )
}

// =============================================================================
// Public emitters
// =============================================================================

/// Emit Table 4 as a markdown table (REQ-1160 / CON-1160).
///
/// Rows are sorted lexicographically by the
/// `(challenge, agent, attacker_category)` short-name tuple so the output is
/// deterministic regardless of cell-vector ordering. Floats are rendered to
/// three decimal places; CIs as `(low, high)`. The caption embeds the
/// per-cell sample size (assumed constant across cells; the value of the
/// first cell is used).
pub fn emit_table_4(
    report: &ComparativeReport,
    out: &mut dyn Write,
) -> std::io::Result<()> {
    let n_per_cell: u32 = report.cells.first().map(|c| c.n_trials).unwrap_or(0);
    let n_cells = report.cells.len();

    writeln!(
        out,
        "{} {} cells (N = {}).",
        TABLE_4_CAPTION_PREFIX, n_cells, n_per_cell
    )?;
    writeln!(out)?;
    writeln!(
        out,
        "| Challenge | Agent | Attacker Category | N | Utility (mean) | Utility 95% CI | Security (mean) | Security 95% CI | Attack Success Rate | ASR 95% CI |"
    )?;
    writeln!(
        out,
        "|-----------|-------|-------------------|---|----------------|----------------|-----------------|-----------------|---------------------|------------|"
    )?;

    let mut sorted: Vec<&MeasurementCell> = report.cells.iter().collect();
    sorted.sort_by_key(|c| cell_sort_key(c));
    for cell in sorted {
        writeln!(out, "{}", render_row(cell))?;
    }
    Ok(())
}

/// Emit the honest-scope section (REQ-1170).
pub fn emit_scope_statement(out: &mut dyn Write) -> std::io::Result<()> {
    writeln!(out, "## Scope")?;
    writeln!(out)?;
    for (_id, body) in SCOPE_STATEMENTS {
        writeln!(out, "- {}", body)?;
    }
    Ok(())
}

/// Emit the known-failure-modes section (REQ-1180).
pub fn emit_failure_modes(out: &mut dyn Write) -> std::io::Result<()> {
    writeln!(out, "## Known Failure Modes")?;
    writeln!(out)?;
    for (name, body) in FAILURE_MODES {
        writeln!(out, "- **{}.** {}", name, body)?;
    }
    Ok(())
}

/// Emit the full paper artefact: Table 4, then scope, then failure modes,
/// each block separated by a blank line.
pub fn emit_full_artefact(
    report: &ComparativeReport,
    out: &mut dyn Write,
) -> std::io::Result<()> {
    emit_table_4(report, out)?;
    writeln!(out)?;
    emit_scope_statement(out)?;
    writeln!(out)?;
    emit_failure_modes(out)?;
    Ok(())
}

// =============================================================================
// CI conformance helper
// =============================================================================

/// Verify the emitted artefact text contains all required structural pieces.
///
/// Checks, in order:
///
/// 1. The Table 4 caption prefix is present.
/// 2. The header row is present.
/// 3. Every data row has the right number of pipe-delimited cells (10 columns
///    bracketed by leading + trailing `|` ⇒ 12 segments after `split('|')`,
///    with the first and last empty), and every inner cell is non-empty
///    after trimming.
/// 4. The `## Scope` heading is present.
/// 5. Every required scope-statement substring appears in the artefact.
/// 6. The `## Known Failure Modes` heading is present.
/// 7. Every required failure-mode name appears.
///
/// Returns `Ok(())` on success or `Err(reason)` on the first violation.
///
/// Note: this helper does NOT count rows against an expected matrix size —
/// callers that want that check (e.g. `TEST-1160`) should additionally
/// compare the row count to `report.cells.len()`. This separation keeps
/// `assert_artefact_conformance` callable without a `ComparativeReport` in
/// hand (CI step over a serialised artefact).
pub fn assert_artefact_conformance(text: &str) -> Result<(), String> {
    if !text.contains(TABLE_4_CAPTION_PREFIX) {
        return Err(format!(
            "Table 4 caption prefix `{}` not found",
            TABLE_4_CAPTION_PREFIX
        ));
    }
    if !text.contains("| Challenge | Agent | Attacker Category |") {
        return Err("Table 4 header row not found".to_string());
    }
    // Data-row check: every line that begins with `|` and is not the header
    // or the separator must split into 11 pipe-segments, all non-empty after
    // trim. Header is detected by the literal `Challenge` token; separator
    // is detected by all-dashes content.
    for (idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if !trimmed.starts_with('|') || !trimmed.ends_with('|') {
            continue;
        }
        if trimmed.contains("Challenge")
            || trimmed.chars().all(|c| matches!(c, '|' | '-' | ' '))
        {
            continue;
        }
        let parts: Vec<&str> = trimmed.split('|').collect();
        if parts.len() != 12 {
            return Err(format!(
                "Table 4 row at line {} has {} pipe-segments (expected 12): `{}`",
                idx + 1,
                parts.len(),
                trimmed
            ));
        }
        for (col, cell) in parts[1..11].iter().enumerate() {
            if cell.trim().is_empty() {
                return Err(format!(
                    "Table 4 row at line {} has empty cell at column {}: `{}`",
                    idx + 1,
                    col,
                    trimmed
                ));
            }
        }
    }
    if !text.contains("## Scope") {
        return Err("`## Scope` heading missing".to_string());
    }
    for (id, _) in SCOPE_STATEMENTS {
        if !text.contains(id) {
            return Err(format!(
                "Scope statement substring `{}` missing from artefact",
                id
            ));
        }
    }
    if !text.contains("## Known Failure Modes") {
        return Err("`## Known Failure Modes` heading missing".to_string());
    }
    for (name, _) in FAILURE_MODES {
        if !text.contains(name) {
            return Err(format!(
                "Failure mode `{}` missing from artefact",
                name
            ));
        }
    }
    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attackers::AttackCategory;
    use crate::manifest::AgentKind;
    use crate::measurement::{measure, MeasurementConfig};
    use crate::operator::ChallengeKind;

    fn small_report() -> ComparativeReport {
        let cfg = MeasurementConfig {
            challenges: vec![
                ChallengeKind::Psi,
                ChallengeKind::Millionaire,
                ChallengeKind::Dining,
            ],
            agents: vec![AgentKind::Cbcl, AgentKind::Vanilla],
            categories: vec![
                AttackCategory::Honest,
                AttackCategory::Published,
                AttackCategory::Novel,
            ],
            n_per_cell: 5,
            overall_seed: 0x4242_4242_4242_4242,
        };
        measure(&cfg)
    }

    fn render_to_string<F>(f: F) -> String
    where
        F: FnOnce(&mut Vec<u8>) -> std::io::Result<()>,
    {
        let mut buf: Vec<u8> = Vec::new();
        f(&mut buf).expect("write to Vec<u8>");
        String::from_utf8(buf).expect("utf-8")
    }

    /// Count non-header / non-separator data rows in the emitted text.
    fn data_rows(text: &str) -> Vec<&str> {
        text.lines()
            .map(str::trim)
            .filter(|l| l.starts_with('|') && l.ends_with('|'))
            .filter(|l| !l.contains("Challenge"))
            .filter(|l| !l.chars().all(|c| matches!(c, '|' | '-' | ' ')))
            .collect()
    }

    /// TEST-1160: `emit_full_artefact` contains the Table 4 caption, exactly
    /// `report.cells.len()` data rows, and every cell is non-empty.
    #[test]
    fn test_1160_table_4_shape() {
        let report = small_report();
        let n_cells = report.cells.len();
        assert_eq!(n_cells, 18, "default matrix is 3*2*3 = 18 cells");
        let text = render_to_string(|w| emit_full_artefact(&report, w));
        assert!(
            text.contains(TABLE_4_CAPTION_PREFIX),
            "caption missing in:\n{}",
            text
        );
        let rows = data_rows(&text);
        assert_eq!(
            rows.len(),
            n_cells,
            "expected {} data rows, got {}: rows = {:#?}",
            n_cells,
            rows.len(),
            rows
        );
        for row in &rows {
            let parts: Vec<&str> = row.split('|').collect();
            assert_eq!(
                parts.len(),
                12,
                "row pipe-segment count wrong (expected 12): {}",
                row
            );
            for (col, cell) in parts[1..11].iter().enumerate() {
                assert!(
                    !cell.trim().is_empty(),
                    "empty cell at column {} in row `{}`",
                    col,
                    row
                );
            }
        }
    }

    /// TEST-1170: scope section contains all five required statements.
    #[test]
    fn test_1170_scope_statements_present() {
        let text = render_to_string(|w| emit_scope_statement(w));
        assert!(text.contains("## Scope"));
        for (id, _) in SCOPE_STATEMENTS {
            assert!(
                text.contains(id),
                "scope substring `{}` missing from emitted scope section:\n{}",
                id,
                text
            );
        }
        assert_eq!(SCOPE_STATEMENTS.len(), 5, "REQ-1170 mandates exactly 5 statements");
    }

    /// TEST-1180: failure-mode section enumerates all four named modes.
    #[test]
    fn test_1180_failure_modes_present() {
        let text = render_to_string(|w| emit_failure_modes(w));
        assert!(text.contains("## Known Failure Modes"));
        for (name, _) in FAILURE_MODES {
            assert!(
                text.contains(name),
                "failure-mode `{}` missing:\n{}",
                name,
                text
            );
        }
        assert_eq!(FAILURE_MODES.len(), 4, "REQ-1180 mandates exactly 4 modes");
    }

    /// Round-trip: emit the full artefact, then assert it conforms.
    #[test]
    fn conformance_helper_round_trip() {
        let report = small_report();
        let text = render_to_string(|w| emit_full_artefact(&report, w));
        match assert_artefact_conformance(&text) {
            Ok(()) => {}
            Err(e) => panic!(
                "assert_artefact_conformance failed: {}\n--- artefact ---\n{}",
                e, text
            ),
        }
    }

    /// Conformance helper detects missing scope / failure-mode sections.
    #[test]
    fn conformance_helper_detects_missing_sections() {
        let report = small_report();
        let mut buf: Vec<u8> = Vec::new();
        emit_table_4(&report, &mut buf).unwrap();
        let text = String::from_utf8(buf).unwrap();
        assert!(
            assert_artefact_conformance(&text).is_err(),
            "table-only artefact should fail conformance"
        );
    }

    /// Cells are sorted by `(challenge, agent, category)` short-name tuple.
    /// Spot-check: `dining` < `millionaire` < `psi` lexicographically, so the
    /// first data row should be a DINING cell.
    #[test]
    fn table_rows_are_sorted_lexicographically() {
        let report = small_report();
        let text = render_to_string(|w| emit_table_4(&report, w));
        let rows = data_rows(&text);
        let first = rows.first().expect("at least one data row");
        assert!(
            first.contains("DINING"),
            "first sorted row should be a DINING cell, got: {}",
            first
        );
    }

    /// Caption embeds both the cell count and `N`.
    #[test]
    fn caption_embeds_cell_count_and_n() {
        let report = small_report();
        let text = render_to_string(|w| emit_table_4(&report, w));
        let first_line = text.lines().next().expect("non-empty output");
        assert!(
            first_line.contains(&format!("{} cells", report.cells.len())),
            "caption missing cell count: {}",
            first_line
        );
        assert!(
            first_line.contains("N = 5"),
            "caption missing per-cell N: {}",
            first_line
        );
    }
}
