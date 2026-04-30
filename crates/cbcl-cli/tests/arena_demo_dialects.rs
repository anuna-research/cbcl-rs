//! Integration test: every dialect under demo/dialects/ must verify
//! under R1, R2, R3 (static, via cbcl-cli verify) AND R5 (the embedded
//! causal protocol's static checks: acyclicity, reachability,
//! definedness, uniqueness).
//!
//! The cbcl-cli `verify` subcommand only surfaces R1–R3 today, so this
//! test fills the R5 gap for the demo artefacts.
//!
//! Run with: cargo test --test arena_demo_dialects -p cbcl-cli

use std::fs;
use std::path::PathBuf;

use cbcl_core::{r1, r2, r3};
use cbcl_parser::dialect_parser::parse_dialect;
use cbcl_parser::parser::parse;

fn demo_dialects_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR points at crates/cbcl-cli; demo/ is two levels up.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .join("demo/dialects")
}

#[test]
fn every_demo_dialect_verifies_r1_r2_r3_r5() {
    let dir = demo_dialects_dir();
    let mut checked = 0usize;

    let entries = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()));

    for entry in entries {
        let path = entry.unwrap().path();
        if path.extension().and_then(|s| s.to_str()) != Some("cbcl") {
            continue;
        }

        let src = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));

        let sexpr = parse(&src)
            .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));

        let dialect = parse_dialect(&sexpr)
            .unwrap_or_else(|e| panic!("parse_dialect {}: {e}", path.display()));

        // R1, R2, R3 — the cbcl-cli verify surface.
        assert!(
            r1::verify_r1_dialect(&dialect),
            "{}: R1 violations {:?}",
            path.display(),
            r1::r1_violations(&dialect)
        );
        assert!(r2::verify_r2(&dialect), "{}: R2 violation", path.display());
        assert!(
            r3::verify_r3(&dialect),
            "{}: R3 violations {:?}",
            path.display(),
            r3::r3_violations(&dialect)
        );

        // R5 — the embedded causal protocol.
        let proto = dialect.causal_protocol.as_ref().unwrap_or_else(|| {
            panic!("{}: missing (protocol ...) clause", path.display())
        });
        let perf_names: Vec<&str> = dialect
            .performatives
            .iter()
            .map(|p| p.name.as_str())
            .collect();
        let violations = proto.verify_r5_protocol(&perf_names);
        assert!(
            violations.is_empty(),
            "{}: R5 violations {:?}",
            path.display(),
            violations
        );

        checked += 1;
    }

    assert!(
        checked >= 4,
        "expected at least 4 demo dialects, found {checked} in {}",
        dir.display()
    );
}
