#!/usr/bin/env python3
"""SPEC-042 TEST-4207: prove native/formal conformance detects broken algorithms.

Build `cbcl-state-oracle` first. Inherits CBCL_STATE_ORACLE/Cargo environment.
Run without concurrent native builds: each mutation restores the source in finally.
"""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "crates/cbcl-core/src/canonical.rs"
MUTATIONS = [
    ("ordering", "pairs.sort_by(|a, b| a.0.cmp(b.0));", "// deliberate mutation: do not order pairs", "parameter_function_matches_formal_model"),
    ("opaque-value", "out[slot + 1] = value.clone();", "out[slot + 1] = SExpr::List(Vec::new());", "parameter_function_matches_formal_model"),
    ("positional-slot", "let mut out = params.to_vec();", "let mut out = params.iter().map(|_| SExpr::List(Vec::new())).collect::<Vec<_>>();", "parameter_function_matches_formal_model"),
    ("recursive-children", "normalise(children);", "let _ = children; // deliberate mutation", "dialect_function_matches_formal_model"),
    ("shape-order", "shapes.sort_by_cached_key(|s| (s.performative.clone(), canonical_encode(&shape_to_sexpr(s))));", "// deliberate mutation: do not order shapes", "dialect_function_matches_formal_model"),
]


def main():
    original = SOURCE.read_bytes()
    env = os.environ.copy()
    env.setdefault("PROPTEST_CASES", "32")
    env.setdefault("PROPTEST_RNG_SEED", "420042")
    baseline = subprocess.run(
        ["cargo", "test", "-p", "cbcl-parser", "--test", "state_kernel_oracle",
         "canonical::", "--", "--ignored"],
        cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if baseline.returncode:
        print(baseline.stdout, file=sys.stderr)
        raise RuntimeError("clean baseline/oracle must pass before mutation")
    for name, old, new, test in MUTATIONS:
        text = original.decode()
        if text.count(old) != 1:
            raise RuntimeError(f"{name}: expected exactly one mutation site")
        try:
            SOURCE.write_text(text.replace(old, new, 1))
            result = subprocess.run(
                ["cargo", "test", "-p", "cbcl-parser", "--test", "state_kernel_oracle",
                 f"canonical::{test}", "--", "--ignored", "--exact"],
                cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            # Compile failures, oracle errors and infrastructure failures are not kills.
            failure = f"test canonical::{test} ... FAILED"
            if result.returncode == 0 or failure not in result.stdout or "test result: FAILED." not in result.stdout:
                print(result.stdout, file=sys.stderr)
                raise RuntimeError(f"{name}: not rejected by an executed conformance test")
            if "assertion `left == right` failed" not in result.stdout:
                print(result.stdout, file=sys.stderr)
                raise RuntimeError(f"{name}: expected a failed equality contract, not an unrelated panic")
            if "oracle input error:" in result.stdout or "oracle transport failed" in result.stdout:
                raise RuntimeError(f"{name}: infrastructure failure is not conformance evidence")
            print(f"{name}: killed", flush=True)
        finally:
            SOURCE.write_bytes(original)
    # Rebuild after restoring the last mutant and require the clean code to pass.
    result = subprocess.run(
        ["cargo", "test", "-p", "cbcl-parser", "--test", "state_kernel_oracle",
         "canonical::", "--", "--ignored"],
        cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode:
        print(result.stdout, file=sys.stderr)
        raise RuntimeError("restored canonicalisation failed conformance")
    print("restored implementation: pass", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
