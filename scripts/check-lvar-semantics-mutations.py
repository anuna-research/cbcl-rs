#!/usr/bin/env python3
"""SPEC-038 TEST-3800/3801/3803/3804: mutate isolated Rust copies only."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[1]
    domain_test = ("lattice_factorisation", "domain_lift_obeys_union_law_across_distinct_openers")
    sum_test = ("threshold_reads", "negative_credits_are_rejected_and_signed_balances_remain_snapshots")
    closure_test = ("threshold_reads", "initializer_conflict_faults_progress_and_its_reached_threshold")
    freeze_test = ("freeze_reads", "freeze_keeps_its_causal_past_and_records_late_and_concurrent_writes")
    freeze_fault_test = ("freeze_reads", "fault_policy_names_the_freezer_and_late_writer")
    freeze_pair_test = ("freeze_reads", "repeated_causal_freezes_keep_the_first_cut_but_concurrent_freezes_fault")
    freeze_initial_test = ("freeze_reads", "freeze_cannot_hide_a_later_initializer_conflict")
    mutations = [
        ("domain-evidence-discarded", "lattice.rs", "if self.domain_governed(term) {",
         "if false {", domain_test),
        ("negative-credit-admitted", "shape.rs",
         "return matches!(sexpr, SExpr::Atom(Atom::Num(n)) if *n >= 0);",
         "return matches!(sexpr, SExpr::Atom(Atom::Num(_)));", sum_test),
        ("signed-events-threshold-admitted", "r7.rs", "if !monotone {", "if false {", sum_test),
        ("threshold-fault-suppressed", "state.rs", "n == field && v.fault_evidence().is_some()",
         "false && n == field && v.fault_evidence().is_some()", domain_test),
        ("derived-fault-suppressed", "state.rs",
         ".filter(|(_, v)| v.fault_evidence().is_some())", ".filter(|_| false)", domain_test),
        ("closure-fault-suppressed", "lattice.rs",
         '.filter(|(verb, _)| verbs.contains(&verb.as_str()))',
         '.filter(|_| false)', closure_test),
        ("freeze-cut-ignored", "freeze.rs", '.filter(|a| cut.contains(&a.address))',
         '.filter(|_| true)', freeze_test),
        ("freeze-fault-policy-ignored", "freeze.rs",
         'if plan.policy == FreezePolicy::Fault && !plan.late.is_empty() {',
         'if false {', freeze_fault_test),
        ("concurrent-freezers-hidden", "freeze.rs", 'if frontier.len() > 1 {',
         'if false {', freeze_pair_test),
        ("freeze-hides-initializer-fault", "freeze.rs",
         '_ if normal.fault_evidence().is_some() => normal,',
         '_ if false => normal,', freeze_initial_test),
    ]
    with tempfile.TemporaryDirectory(prefix="cbcl-lvar-semantics-") as directory:
        isolated = Path(directory)
        (isolated / "crates").mkdir()
        for name in ["cbcl-core", "cbcl-parser"]:
            shutil.copytree(root / "crates" / name, isolated / "crates" / name)
        for name in ["dialects", "test-vectors"]:
            shutil.copytree(root / name, isolated / name)
        for name in ["Cargo.lock", "rust-toolchain.toml"]:
            if (root / name).exists():
                shutil.copy2(root / name, isolated / name)
        manifest, count = re.subn(
            r"members = \[.*?\]", 'members = ["crates/cbcl-core", "crates/cbcl-parser"]',
            (root / "Cargo.toml").read_text(), count=1, flags=re.S,
        )
        if count != 1:
            raise SystemExit("FAIL: workspace members anchor missing")
        (isolated / "Cargo.toml").write_text(manifest)
        env = dict(os.environ, CARGO_TARGET_DIR=str(isolated / "target"),
                   CARGO_PROFILE_TEST_DEBUG="0", CARGO_PROFILE_DEV_DEBUG="0", CARGO_INCREMENTAL="0")

        def run(test):
            return subprocess.run(
                ["cargo", "test", "--offline", "-p", "cbcl-parser", "--test", test[0],
                 test[1], "--", "--exact"], cwd=isolated, env=env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
            )

        for test in sorted({m[-1] for m in mutations}):
            baseline = run(test)
            if baseline.returncode != 0 or f"test {test[1]} ... ok" not in baseline.stdout:
                print(baseline.stdout)
                raise SystemExit(f"FAIL: baseline {test[1]}")
            print(f"PASS: baseline {test[1]}", flush=True)
        for name, filename, original, replacement, test in mutations:
            path = isolated / "crates/cbcl-core/src" / filename
            source = path.read_text()
            if source.count(original) != 1:
                raise SystemExit(f"FAIL: {name} anchor missing or ambiguous")
            try:
                path.write_text(source.replace(original, replacement))
                result = run(test)
            finally:
                path.write_text(source)
            if result.returncode == 0 or f"test {test[1]} ... FAILED" not in result.stdout:
                print(result.stdout)
                raise SystemExit(f"FAIL: {name} did not fail its executed semantic test")
            print(f"PASS: {name} rejected by {test[1]}", flush=True)


if __name__ == "__main__":
    main()
