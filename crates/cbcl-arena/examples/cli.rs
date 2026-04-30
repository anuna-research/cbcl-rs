//! `cbcl-arena` example CLI (SPEC-011 §4.2.1 Demo 3).
//!
//! Runs the SPEC-011 measurement matrix and emits the Demo 3 paper
//! artefact (`emit_table_4`). After the measurement, the CLI checks the
//! four falsifiable headline predictions in `REQ-1150` / `OBS-1110` and
//! prints one `[PASS]` / `[FAIL]` line per prediction. The process exits
//! `0` if every prediction passes; `1` if any fail.
//!
//! ```text
//! USAGE: cbcl-arena [--n N] [--out PATH] [--seed S] [--challenges CSV] [--release-only]
//!
//!   --n N             Runs per cell (default 300)
//!   --out PATH        Output markdown path (default: stdout)
//!   --seed S          Master seed (default: 0xCBC1_A1EA_DEFA_0173)
//!   --challenges CSV  Subset of {psi,millionaire,dining} (default: all three)
//!   --release-only    Refuse to run in debug builds (used by NFR-1111 timing
//!                     checks where debug-mode timings are not meaningful).
//! ```
//!
//! Argument parsing uses only [`std::env::args`] — no `clap` dep.

use std::env;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use cbcl_arena::artefact::{emit_full_artefact, emit_table_4};
use cbcl_arena::attackers::AttackCategory;
use cbcl_arena::manifest::AgentKind;
use cbcl_arena::measurement::{measure, ComparativeReport, MeasurementCell, MeasurementConfig};
use cbcl_arena::operator::ChallengeKind;

/// Master seed used when `--seed` is not supplied. A stable bit pattern,
/// derived to be self-documenting in hex dumps (REQ-1151 stable).
const DEFAULT_SEED: u64 = 0xCBC1_A1EA_DEFA_0173_u64;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    match run(&args) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("cbcl-arena: error: {e}");
            ExitCode::from(2)
        }
    }
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let opts = parse_args(args)?;

    if opts.release_only && cfg!(debug_assertions) {
        eprintln!(
            "cbcl-arena: --release-only specified but this is a debug build; \
             skipping run."
        );
        return Ok(ExitCode::from(0));
    }

    let cfg = MeasurementConfig {
        challenges: opts.challenges.clone(),
        agents: vec![AgentKind::Cbcl, AgentKind::Vanilla],
        categories: vec![
            AttackCategory::Honest,
            AttackCategory::Published,
            AttackCategory::Novel,
        ],
        n_per_cell: opts.n,
        overall_seed: opts.seed,
    };

    eprintln!(
        "cbcl-arena: running measurement matrix \
         (challenges={:?}, n_per_cell={}, seed=0x{:016x})",
        cfg.challenges
            .iter()
            .map(|c| short_challenge(*c))
            .collect::<Vec<_>>(),
        cfg.n_per_cell,
        cfg.overall_seed,
    );

    let report = measure(&cfg);

    // Emit the full artefact (Table 4 + Scope + Failure Modes) when writing
    // to a file, matching the SPEC-011 §Verification artefact contract
    // (REQ-1160 / REQ-1170 / REQ-1180). When writing to stdout we emit only
    // Table 4 so the headline-prediction lines on stderr remain easy to read.
    match &opts.out {
        Some(path) => {
            let f = File::create(path)
                .map_err(|e| format!("cannot open {} for writing: {e}", path.display()))?;
            let mut w = BufWriter::new(f);
            emit_full_artefact(&report, &mut w)
                .map_err(|e| format!("emit_full_artefact failed: {e}"))?;
            w.flush()
                .map_err(|e| format!("flush failed: {e}"))?;
            eprintln!(
                "cbcl-arena: wrote full artefact (Table 4 + Scope + Failure Modes) to {}",
                path.display()
            );
        }
        None => {
            let stdout = io::stdout();
            let mut w = stdout.lock();
            emit_table_4(&report, &mut w).map_err(|e| format!("emit_table_4 failed: {e}"))?;
            w.flush().ok();
        }
    }

    // Headline-prediction validation.
    let mut all_pass = true;
    eprintln!();
    eprintln!("cbcl-arena: headline predictions (REQ-1150 / OBS-1110)");
    for line in headline_lines(&report) {
        eprintln!("  {}", line.text);
        if !line.passed {
            all_pass = false;
        }
    }

    if all_pass {
        Ok(ExitCode::from(0))
    } else {
        Ok(ExitCode::from(1))
    }
}

// =============================================================================
// argument parsing
// =============================================================================

#[derive(Debug)]
struct Opts {
    n: usize,
    out: Option<PathBuf>,
    seed: u64,
    challenges: Vec<ChallengeKind>,
    release_only: bool,
}

fn parse_args(args: &[String]) -> Result<Opts, String> {
    let mut n: usize = 300;
    let mut out: Option<PathBuf> = None;
    let mut seed: u64 = DEFAULT_SEED;
    let mut challenges: Vec<ChallengeKind> =
        vec![ChallengeKind::Psi, ChallengeKind::Millionaire, ChallengeKind::Dining];
    let mut release_only = false;

    let mut it = args.iter().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--help" | "-h" => {
                print_help();
                std::process::exit(0);
            }
            "--n" => {
                let v = it
                    .next()
                    .ok_or_else(|| "--n expects an integer".to_string())?;
                n = v
                    .parse::<usize>()
                    .map_err(|e| format!("--n: {v}: {e}"))?;
                if n == 0 {
                    return Err("--n must be > 0".into());
                }
            }
            "--out" => {
                let v = it
                    .next()
                    .ok_or_else(|| "--out expects a path".to_string())?;
                out = Some(PathBuf::from(v));
            }
            "--seed" => {
                let v = it
                    .next()
                    .ok_or_else(|| "--seed expects an integer".to_string())?;
                seed = parse_u64_flexible(v)
                    .ok_or_else(|| format!("--seed: cannot parse {v} as u64"))?;
            }
            "--challenges" => {
                let v = it
                    .next()
                    .ok_or_else(|| "--challenges expects a CSV value".to_string())?;
                challenges = parse_challenges(v)?;
            }
            "--release-only" => {
                release_only = true;
            }
            other => {
                return Err(format!("unknown argument: {other}"));
            }
        }
    }

    Ok(Opts {
        n,
        out,
        seed,
        challenges,
        release_only,
    })
}

fn parse_u64_flexible(s: &str) -> Option<u64> {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        let cleaned: String = rest.chars().filter(|c| *c != '_').collect();
        u64::from_str_radix(&cleaned, 16).ok()
    } else {
        let cleaned: String = s.chars().filter(|c| *c != '_').collect();
        cleaned.parse::<u64>().ok()
    }
}

fn parse_challenges(s: &str) -> Result<Vec<ChallengeKind>, String> {
    let mut out: Vec<ChallengeKind> = Vec::new();
    for tok in s.split(',') {
        let t = tok.trim().to_ascii_lowercase();
        if t.is_empty() {
            continue;
        }
        let c = match t.as_str() {
            "psi" => ChallengeKind::Psi,
            "millionaire" | "yao" => ChallengeKind::Millionaire,
            "dining" | "dc" => ChallengeKind::Dining,
            other => return Err(format!("unknown challenge: {other}")),
        };
        if !out.contains(&c) {
            out.push(c);
        }
    }
    if out.is_empty() {
        return Err("--challenges: at least one challenge required".into());
    }
    Ok(out)
}

fn print_help() {
    let text = "USAGE: cbcl-arena [--n N] [--out PATH] [--seed S] [--challenges CSV] [--release-only]\n\
                \n\
                Runs the SPEC-011 measurement matrix and emits the §4.2.1 Demo 3 table.\n\
                \n\
                  --n N             Runs per cell (default 300)\n\
                  --out PATH        Output markdown path (default: stdout)\n\
                  --seed S          Master seed (default: 0xCBC1_A1EA_DEFA_0173)\n\
                  --challenges CSV  Subset of {psi,millionaire,dining} (default: all three)\n\
                  --release-only    Refuse to run in a debug build (timing-check helper)\n";
    let _ = io::stdout().lock().write_all(text.as_bytes());
}

// =============================================================================
// headline-prediction checks (REQ-1150 / OBS-1110)
// =============================================================================

/// One headline-prediction result line.
pub struct HeadlineLine {
    /// The formatted text (already including `[PASS]` / `[FAIL]` prefix).
    pub text: String,
    /// `true` if the prediction passed.
    pub passed: bool,
}

fn headline_lines(report: &ComparativeReport) -> Vec<HeadlineLine> {
    let mut out: Vec<HeadlineLine> = Vec::new();

    // Prediction 1: PSI/Vanilla/Published rate ∈ [0.35, 0.50].
    if let Some(c) = find_cell(
        report,
        ChallengeKind::Psi,
        AgentKind::Vanilla,
        AttackCategory::Published,
    ) {
        let r = c.attack_success_rate;
        let passed = (0.35..=0.50).contains(&r);
        out.push(line(
            passed,
            "psi-vanilla-published-calibration",
            format_rate_in_band(r, c.attack_success_ci, 0.35, 0.50),
        ));
    } else {
        out.push(skip("psi-vanilla-published-calibration"));
    }

    // Prediction 2: PSI/CBCL/Published rate ∈ [0, 0.012].
    if let Some(c) = find_cell(
        report,
        ChallengeKind::Psi,
        AgentKind::Cbcl,
        AttackCategory::Published,
    ) {
        let r = c.attack_success_rate;
        let passed = (0.0..=0.012).contains(&r);
        out.push(line(
            passed,
            "psi-cbcl-published-security",
            format_rate_in_band(r, c.attack_success_ci, 0.0, 0.012),
        ));
    } else {
        out.push(skip("psi-cbcl-published-security"));
    }

    // Prediction 3: PSI/CBCL/Novel rate ∈ [0, 0.012].
    if let Some(c) = find_cell(
        report,
        ChallengeKind::Psi,
        AgentKind::Cbcl,
        AttackCategory::Novel,
    ) {
        let r = c.attack_success_rate;
        let passed = (0.0..=0.012).contains(&r);
        out.push(line(
            passed,
            "psi-cbcl-novel-security",
            format_rate_in_band(r, c.attack_success_ci, 0.0, 0.012),
        ));
    } else {
        out.push(skip("psi-cbcl-novel-security"));
    }

    // Prediction 4: honest-cooperative utility delta `|cbcl - vanilla| <= 0.1`
    // for every challenge that ran.
    let mut challenges_in_report: Vec<ChallengeKind> = report
        .cells
        .iter()
        .map(|c| c.challenge)
        .collect();
    challenges_in_report.sort_by_key(|c| match c {
        ChallengeKind::Psi => 0,
        ChallengeKind::Millionaire => 1,
        ChallengeKind::Dining => 2,
    });
    challenges_in_report.dedup();

    for ch in challenges_in_report {
        let cbcl = find_cell(report, ch, AgentKind::Cbcl, AttackCategory::Honest);
        let van = find_cell(report, ch, AgentKind::Vanilla, AttackCategory::Honest);
        let label = format!("honest-utility-delta-{}", short_challenge(ch));
        match (cbcl, van) {
            (Some(c), Some(v)) => {
                let delta = (c.utility_mean - v.utility_mean).abs();
                let passed = delta <= 0.1;
                let detail = format!(
                    "|cbcl-vanilla|={:.3} (cbcl={:.3}, vanilla={:.3}) <= 0.1",
                    delta, c.utility_mean, v.utility_mean
                );
                out.push(line(passed, &label, detail));
            }
            _ => out.push(skip(&label)),
        }
    }

    out
}

fn find_cell(
    report: &ComparativeReport,
    ch: ChallengeKind,
    ag: AgentKind,
    cat: AttackCategory,
) -> Option<&MeasurementCell> {
    report
        .cells
        .iter()
        .find(|c| c.challenge == ch && c.agent == ag && c.attacker_category == cat)
}

fn line(passed: bool, name: &str, detail: String) -> HeadlineLine {
    let tag = if passed { "[PASS]" } else { "[FAIL]" };
    HeadlineLine {
        text: format!("{tag} {name}: {detail}"),
        passed,
    }
}

fn skip(name: &str) -> HeadlineLine {
    HeadlineLine {
        text: format!("[SKIP] {name}: cell not in report"),
        passed: true,
    }
}

fn format_rate_in_band(rate: f64, ci: (f64, f64), lo: f64, hi: f64) -> String {
    format!(
        "rate={:.3} [CI {:.3}, {:.3}] in [{:.2}, {:.3}]",
        rate, ci.0, ci.1, lo, hi
    )
}

fn short_challenge(c: ChallengeKind) -> &'static str {
    match c {
        ChallengeKind::Psi => "psi",
        ChallengeKind::Millionaire => "millionaire",
        ChallengeKind::Dining => "dining",
    }
}
