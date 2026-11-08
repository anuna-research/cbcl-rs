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
test = "finite_kernel_matches_live_lean_oracle"
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

    def run():
        return subprocess.run(["cargo", "test", "--offline", "-p", "cbcl-parser", "--test", "state_kernel_oracle",
                               test, "--", "--ignored", "--exact"], cwd=isolated, env=env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)

    baseline = run()
    if baseline.returncode or f"test {test} ... ok" not in baseline.stdout:
        print(baseline.stdout)
        raise SystemExit("FAIL: live-oracle baseline")
    print("PASS: live-oracle baseline", flush=True)
    for name, filename, before, after in [
        ("only-first-finite-contribution", "lattice.rs", ".fold(table.bottom, |a, b| table.merge(a, b))", ".next().unwrap_or(table.bottom)"),
        ("threshold-source-fault-hidden", "state.rs", "n == field && v.fault_evidence().is_some()", "false && n == field && v.fault_evidence().is_some()"),
    ]:
        path = isolated / "crates/cbcl-core/src" / filename
        source = path.read_text()
        if source.count(before) != 1:
            raise SystemExit(f"FAIL: {name} anchor missing or ambiguous")
        try:
            path.write_text(source.replace(before, after))
            result = run()
        finally:
            path.write_text(source)
        if result.returncode == 0 or f"test {test} ... FAILED" not in result.stdout or "assertion" not in result.stdout:
            print(result.stdout)
            raise SystemExit(f"FAIL: {name} not rejected by executed oracle comparison")
        print(f"PASS: {name} rejected by live Lean comparison", flush=True)
