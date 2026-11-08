#!/usr/bin/env python3
"""SPEC-038: prove the live Lean oracle detects real Rust regressions, in copies."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
oracle = root / "lean-cbcl/.lake/build/bin/cbcl-state-oracle"
if not oracle.is_file():
    raise SystemExit("Build first: cd lean-cbcl && lake build cbcl-state-oracle")
finite_test = "finite_kernel_matches_live_lean_oracle"
freeze_test = "freeze_kernel_matches_live_lean_oracle"
nested_test = "nested_kernel_matches_live_lean_oracle"
with tempfile.TemporaryDirectory(prefix="cbcl-live-oracle-") as directory:
    isolated = Path(directory)
    (isolated / "crates").mkdir()
    for name in ["cbcl-core", "cbcl-parser"]:
        shutil.copytree(root / "crates" / name, isolated / "crates" / name)
    shutil.copytree(root / "dialects", isolated / "dialects")
    for name in ["Cargo.lock", "rust-toolchain.toml"]:
        shutil.copy2(root / name, isolated / name)
    manifest, count = re.subn(r"members = \[.*?\]", 'members = ["crates/cbcl-core", "crates/cbcl-parser"]',
                             (root / "Cargo.toml").read_text(), count=1, flags=re.S)
    if count != 1:
        raise SystemExit("workspace membership anchor missing")
    (isolated / "Cargo.toml").write_text(manifest)
    env = dict(os.environ, CBCL_STATE_ORACLE=str(oracle), PROPTEST_CASES="32", PROPTEST_RNG_SEED="380038",
               CARGO_TARGET_DIR=str(isolated / "target"), CARGO_INCREMENTAL="0", CARGO_PROFILE_TEST_DEBUG="0")

    def run(test):
        return subprocess.run(["cargo", "test", "--offline", "-p", "cbcl-parser", "--test", "state_kernel_oracle",
                               test, "--", "--ignored", "--exact"], cwd=isolated, env=env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)

    for test in [finite_test,freeze_test,nested_test]:
        baseline = run(test)
        if baseline.returncode or f"test {test} ... ok" not in baseline.stdout:
            print(baseline.stdout)
            raise SystemExit(f"FAIL: live-oracle baseline {test}")
        print(f"PASS: live-oracle baseline {test}", flush=True)
    for name, filename, before, after, test in [
        ("reader-scope-cache-key-erased", "freeze.rs", "let key = (scope, name.to_string());", "let key = (0, name.to_string());", nested_test),
        ("reader-field-cache-key-erased", "freeze.rs", "let key = (scope, name.to_string());", "let key = (scope, String::new());", nested_test),
        ("reader-dependency-uses-whole-history", "freeze.rs", "let v = self.field(scope, &source);", "let v = self.field(0, &source);", nested_test),
        ("reader-frozen-dependency-not-unwrapped", "freeze.rs", "done.push((source, v.unfrozen().clone()));", "done.push((source, v.clone()));", nested_test),
        ("derived-source-fault-hidden", "lattice.rs", "earlier.filter(|v| v.fault_evidence().is_some())", "earlier.filter(|_| false)", nested_test),
        ("only-first-finite-contribution", "lattice.rs", ".fold(table.bottom, |a, b| table.merge(a, b))", ".next().unwrap_or(table.bottom)", finite_test),
        ("threshold-source-fault-hidden", "state.rs", "n == field && v.fault_evidence().is_some()", "false && n == field && v.fault_evidence().is_some()", finite_test),
        ("freeze-cut-ignored", "freeze.rs", ".filter(|a| cut.contains(&a.address))", ".filter(|_| true)", freeze_test),
        ("freeze-fault-policy-hidden", "freeze.rs", "if p.policy == FreezePolicy::Fault && !p.late.is_empty() {", "if false {", freeze_test),
        ("concurrent-freezers-hidden", "freeze.rs", "if frontier.len() > 1 {", "if false {", freeze_test),
        ("raw-fault-hides-freeze-evidence", "freeze.rs", "evidence.extend(fault.fault_evidence().unwrap_or_default());", "let _ = fault;", freeze_test),
    ]:
        path = isolated / "crates/cbcl-core/src" / filename
        source = path.read_text()
        if source.count(before) != 1:
            raise SystemExit(f"FAIL: {name} anchor missing or ambiguous")
        try:
            path.write_text(source.replace(before, after))
            result = run(test)
        finally:
            path.write_text(source)
        if result.returncode == 0 or f"test {test} ... FAILED" not in result.stdout or "assertion" not in result.stdout:
            print(result.stdout)
            raise SystemExit(f"FAIL: {name} not rejected by executed oracle comparison")
        print(f"PASS: {name} rejected by live Lean comparison", flush=True)
