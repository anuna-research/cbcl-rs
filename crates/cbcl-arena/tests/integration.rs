//! `cbcl-arena` integration tests (SPEC-011 §Verification).
//!
//! Covers:
//!
//! - **TEST-1190** single-game latency (`single_game_latency_*`) — `#[ignore]`
//! - **TEST-1191** full-measurement runtime (`full_measurement_runtime`) —
//!   `#[ignore]`
//! - **TEST-1192** no engine modifications + dialect SHA-256 baseline check
//!   (`no_engine_modifications`)
//! - **TEST-1193** local determinism / byte-identical replay
//!   (`measurement_replay_byte_identical`)
//! - End-to-end smoke test for the full pipeline
//!   (`end_to_end_smoke_emits_artefact`)
//!
//! Slow tests are gated by `#[ignore]` so the default
//! `cargo test -p cbcl-arena` stays fast. To run the slow tests:
//!
//! ```sh
//! cargo test -p cbcl-arena --release -- --ignored
//! ```

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};

use cbcl_arena::artefact::{assert_artefact_conformance, emit_full_artefact, emit_table_4};
use cbcl_arena::attackers::AttackCategory;
use cbcl_arena::manifest::AgentKind;
use cbcl_arena::measurement::{measure, MeasurementConfig};
use cbcl_arena::operator::ChallengeKind;

// =============================================================================
// helpers
// =============================================================================

/// Workspace root, derived from `CARGO_MANIFEST_DIR` (the per-crate path).
/// `crates/cbcl-arena` -> `..` -> `..` -> workspace root.
fn workspace_root() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    Path::new(manifest_dir)
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .expect("workspace root resolvable from CARGO_MANIFEST_DIR")
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    let digest = h.finalize();
    let mut s = String::with_capacity(digest.len() * 2);
    for b in digest.iter() {
        use std::fmt::Write;
        write!(s, "{b:02x}").unwrap();
    }
    s
}

// =============================================================================
// TEST-1190: single-game latency (NFR-1110)
// =============================================================================
//
// `NFR-1110` budgets a single game (PSI, Yao, or DC) at p95 ≤ 50 ms on a
// developer-class machine. We approximate "single game" by calling
// `measure()` on a 1-cell × N=1 configuration; the orchestrator overhead
// is small relative to the per-game cost.
//
// `#[ignore]`'d because it is sensitive to debug builds — run with:
// `cargo test -p cbcl-arena --release -- --ignored single_game_latency`.

fn one_game_seed_for(i: usize) -> u64 {
    0xA11A_DEA1_A11A_A11A_u64
        .wrapping_add(i as u64)
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

fn measure_single_game_latencies(
    challenge: ChallengeKind,
    agent: AgentKind,
    attacker: AttackCategory,
    n_samples: usize,
) -> Vec<Duration> {
    let mut latencies: Vec<Duration> = Vec::with_capacity(n_samples);
    for i in 0..n_samples {
        let cfg = MeasurementConfig {
            challenges: vec![challenge],
            agents: vec![agent],
            categories: vec![attacker],
            n_per_cell: 1,
            overall_seed: one_game_seed_for(i),
        };
        let t0 = Instant::now();
        let r = measure(&cfg);
        let dt = t0.elapsed();
        // Sanity: one cell.
        assert_eq!(r.cells.len(), 1);
        latencies.push(dt);
    }
    latencies
}

fn p95(mut samples: Vec<Duration>) -> Duration {
    samples.sort();
    let n = samples.len();
    let idx = ((n as f64) * 0.95).ceil() as usize;
    let idx = idx.saturating_sub(1).min(n - 1);
    samples[idx]
}

#[test]
#[ignore = "TEST-1190 latency (slow): run with --release --ignored"]
fn single_game_latency_psi() {
    // PSI is the heaviest of the three (chat-heavy CBCL handshake).
    let lats = measure_single_game_latencies(
        ChallengeKind::Psi,
        AgentKind::Cbcl,
        AttackCategory::Honest,
        100,
    );
    let p = p95(lats.clone());
    eprintln!(
        "TEST-1190 PSI p95 = {:?} (over {} samples; budget 50 ms)",
        p,
        lats.len()
    );
    assert!(
        p <= Duration::from_millis(50),
        "PSI single-game p95 latency {p:?} exceeds 50 ms budget (NFR-1110)"
    );
}

#[test]
#[ignore = "TEST-1190 latency (slow): run with --release --ignored"]
fn single_game_latency_millionaire() {
    let lats = measure_single_game_latencies(
        ChallengeKind::Millionaire,
        AgentKind::Cbcl,
        AttackCategory::Honest,
        100,
    );
    let p = p95(lats.clone());
    eprintln!(
        "TEST-1190 Yao p95 = {:?} (over {} samples; budget 50 ms)",
        p,
        lats.len()
    );
    assert!(
        p <= Duration::from_millis(50),
        "Yao single-game p95 latency {p:?} exceeds 50 ms budget (NFR-1110)"
    );
}

#[test]
#[ignore = "TEST-1190 latency (slow): run with --release --ignored"]
fn single_game_latency_dining() {
    let lats = measure_single_game_latencies(
        ChallengeKind::Dining,
        AgentKind::Cbcl,
        AttackCategory::Honest,
        100,
    );
    let p = p95(lats.clone());
    eprintln!(
        "TEST-1190 DC p95 = {:?} (over {} samples; budget 50 ms)",
        p,
        lats.len()
    );
    assert!(
        p <= Duration::from_millis(50),
        "DC single-game p95 latency {p:?} exceeds 50 ms budget (NFR-1110)"
    );
}

// =============================================================================
// TEST-1191: full-measurement runtime budget (NFR-1111)
// =============================================================================

#[test]
#[ignore = "TEST-1191 runtime (slow): run with --release --ignored"]
fn full_measurement_runtime() {
    if cfg!(debug_assertions) {
        eprintln!(
            "TEST-1191 SKIPPED: debug build (the 600 s budget is meaningful only in --release)"
        );
        return;
    }
    let cfg = MeasurementConfig::default_full_matrix(0xc0ff_eeee_c0ff_eeee);
    let t0 = Instant::now();
    let r = measure(&cfg);
    let elapsed = t0.elapsed();
    eprintln!(
        "TEST-1191: full N={} matrix ({} cells) finished in {:.2} s",
        cfg.n_per_cell,
        r.cells.len(),
        elapsed.as_secs_f64()
    );
    assert_eq!(r.cells.len(), 18);
    assert!(
        elapsed.as_secs() <= 600,
        "TEST-1191: full N=300 measurement took {:.2} s, budget 600 s (NFR-1111)",
        elapsed.as_secs_f64()
    );
}

// =============================================================================
// TEST-1192: no engine modifications + dialect baseline (NFR-1112)
// =============================================================================
//
// Implementation strategy:
// - **Path-presence check** for `cbcl-core` and `cbcl-parser` source
//   directories (the simulator must compose them, not inline them).
// - **SHA-256 baseline check** for the three load-bearing dialect files.
//   Hashes were captured at the `feat/arena-demo` commit. If a hash
//   mismatch is observed, the dialect has changed since the baseline was
//   set: SPEC-011 / RISK-1113 must be updated to reflect the new dialect.

const PSI_DIALECT_SHA256: &str =
    "02525f4f16f4b19c4318ea1f5d7b8e5846695f3d5fb0dabca325d7e9a62b772f";
const MILLIONAIRE_DIALECT_SHA256: &str =
    "da1505f746670771e755b13df9c70a52c995d509ce930d0988aaaa2d02bb70b2";
const DINING_DIALECT_SHA256: &str =
    "c9db3020106380c239cda746181de9f05e2228f0f4bd6c109581a242647a8b94";

#[test]
fn no_engine_modifications() {
    let root = workspace_root();

    // 1. Engine crates exist and have not been inlined under cbcl-arena.
    for relpath in ["crates/cbcl-core/src", "crates/cbcl-parser/src"] {
        let p = root.join(relpath);
        assert!(
            p.is_dir(),
            "TEST-1192: expected engine source dir at {} (NFR-1112)",
            p.display()
        );
    }

    // 2. The simulator must NOT shadow the engine's source by adding
    //    files of the same crate names under `crates/cbcl-arena/src/`.
    let arena_src = root.join("crates/cbcl-arena/src");
    for forbidden in ["cbcl_core", "cbcl_parser"] {
        let p = arena_src.join(forbidden);
        assert!(
            !p.exists(),
            "TEST-1192: simulator must not vendor {} under {} (NFR-1112)",
            forbidden,
            arena_src.display()
        );
    }

    // 3. Dialect SHA-256 baseline.
    let dialect_dir = root.join("demo/dialects");
    let pairs: [(&str, &str); 3] = [
        ("psi.cbcl", PSI_DIALECT_SHA256),
        ("millionaire.cbcl", MILLIONAIRE_DIALECT_SHA256),
        ("dining.cbcl", DINING_DIALECT_SHA256),
    ];
    for (file, expected) in pairs {
        let path = dialect_dir.join(file);
        let bytes = std::fs::read(&path).unwrap_or_else(|e| {
            panic!("TEST-1192: cannot read dialect {}: {}", path.display(), e)
        });
        let got = sha256_hex(&bytes);
        assert_eq!(
            got,
            expected,
            "TEST-1192: dialect {} SHA-256 changed from baseline.\n\
             expected: {}\n\
             got:      {}\n\
             If this change is intentional, update SPEC-011 and RISK-1113 \
             then refresh the baseline constant in this test file.",
            path.display(),
            expected,
            got
        );
    }
}

// =============================================================================
// TEST-1193: cross-platform determinism (local replay)
// =============================================================================

#[test]
fn measurement_replay_byte_identical() {
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
        n_per_cell: 20,
        overall_seed: 0xd0_d0_be_d0_de_ad_be_ef,
    };

    let r1 = measure(&cfg);
    let r2 = measure(&cfg);

    assert_eq!(r1.cells, r2.cells, "TEST-1193: cells must be byte-identical");
    assert_eq!(
        r1.manifest.per_cell_seeds, r2.manifest.per_cell_seeds,
        "TEST-1193: per-cell seeds must be byte-identical"
    );

    // The full `ComparativeReport` Debug render is NOT byte-identical
    // across runs because the manifest's `timestamp_utc` is captured
    // from the wall clock. The deterministic-cell-side claim of
    // NFR-1113 covers cells and per-cell seeds (above); the full
    // cross-platform claim additionally requires CI on multiple OS /
    // arch images.

    // The emitted Table 4 is timestamp-free (`emit_table_4` formats
    // only cell content + the per-cell `N`), so it must be
    // byte-identical across replays.
    let mut buf1: Vec<u8> = Vec::new();
    let mut buf2: Vec<u8> = Vec::new();
    emit_table_4(&r1, &mut buf1).expect("emit_table_4 #1");
    emit_table_4(&r2, &mut buf2).expect("emit_table_4 #2");
    assert_eq!(buf1, buf2, "TEST-1193: emitted Table 4 must be byte-identical");
}

// =============================================================================
// End-to-end smoke: full pipeline at small N.
// =============================================================================

#[test]
fn end_to_end_smoke_emits_artefact() {
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
        n_per_cell: 10,
        overall_seed: 0xfeed_face_dead_b0a7,
    };

    let report = measure(&cfg);
    assert_eq!(report.cells.len(), 18, "expected 18 = 3 × 2 × 3 cells");

    let mut buf: Vec<u8> = Vec::new();
    emit_full_artefact(&report, &mut buf).expect("emit_full_artefact");
    let text = String::from_utf8(buf).expect("artefact is valid UTF-8");

    // Non-empty.
    assert!(!text.trim().is_empty(), "artefact text is empty");

    // REQ-1160: Table 4 caption + header row + every row well-formed.
    // REQ-1170: Scope section + 5 statements.
    // REQ-1180: Failure Modes section + 4 names.
    assert_artefact_conformance(&text)
        .unwrap_or_else(|e| panic!("artefact conformance failed: {e}"));

    // Spot-check: row labels mention each challenge × each agent.
    for ch_label in ["PSI", "MILLIONAIRE", "DINING"] {
        assert!(
            text.contains(ch_label),
            "Table 4 missing challenge column label: {ch_label}"
        );
    }
    for ag_label in ["CBCL", "Vanilla"] {
        assert!(
            text.contains(ag_label),
            "Table 4 missing agent label: {ag_label}"
        );
    }
    for cat_label in ["Honest", "Published", "Novel"] {
        assert!(
            text.contains(cat_label),
            "Table 4 missing attacker category label: {cat_label}"
        );
    }
    // Section headers.
    assert!(text.contains("## Scope"), "missing ## Scope heading (REQ-1170)");
    assert!(
        text.contains("## Known Failure Modes"),
        "missing ## Known Failure Modes heading (REQ-1180)"
    );
}
