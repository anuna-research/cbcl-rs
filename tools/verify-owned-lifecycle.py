#!/usr/bin/env python3
"""Reproduce SPEC-033 oracle checks and optional targeted negative controls."""
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ENV = {**os.environ, "CARGO_INCREMENTAL": "0"}


def run(args, cwd=ROOT, *, expect_failure=False):
    p = subprocess.run(args, cwd=cwd, env=ENV, text=True, capture_output=True)
    if expect_failure:
        assert p.returncode != 0, f"negative control unexpectedly passed: {args}"
    elif p.returncode:
        raise RuntimeError(p.stdout + p.stderr)
    return p


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mutations", action="store_true")
    args = parser.parse_args()
    run(["lake", "build", "LeanCbcl.ConsensusFree.OwnedLifecycle", "LeanCbcl.ConsensusFree.OwnedProgress", "LeanCbcl.ConsensusFree.OwnerFunding"], ROOT / "lean-cbcl")
    for audit_file in ["OwnedLifecycleAudit.lean", "OwnedProgressAudit.lean", "OwnerFundingAudit.lean"]:
        audit = run(["lake", "env", "lean", audit_file], ROOT / "lean-cbcl")
        dependencies = re.findall(r"depends on axioms: \[([^]]*)\]", audit.stdout, flags=re.S)
        assert dependencies, "axiom audit emitted no theorem dependencies"
        for dependency in dependencies:
            assert set(filter(None, (name.strip() for name in dependency.split(",")))) <= {"propext", "Quot.sound", "Classical.choice"}, dependency
    oracle = run(["lake", "env", "lean", "--run", "OwnedLifecycleOracle.lean"], ROOT / "lean-cbcl")
    assert json.loads(oracle.stdout) == json.loads((ROOT / "test-vectors/quorum/owned-lifecycle-lean.json").read_text())
    run(["cargo", "test", "-p", "cbcl-parser", "--test", "quorum_runtime", "owned_", "--offline"])
    run(["cargo", "test", "-p", "cbcl-quorum-e2e", "--test", "owned_lifecycle", "--offline"])
    print("Lean build/axioms/oracle, Rust shared traces/adversarial tests and real-crypto durable lifecycle: PASS")
    if not args.mutations:
        return
    path = ROOT / "crates/cbcl-core/src/quorum/engine.rs"
    original = path.read_text()
    mutations = [
        ("slot", """            if self
                .state
                .signed
                .iter()
                .any(|other| self.state.operations[other].epoch == op.epoch)""", "            if false", "owned_full_balance"),
        ("seal-closure", "        if self.state.sealed.contains_key(&op.account) {", "        if false {", "owned_seal_authorization"),
        ("owner-signature-domain", "            VoteKind::OwnedSealRequest,", "            VoteKind::VersionRequest,", "owned_seal_authorization"),
        ("prior-fence", "            if self.state.fences.contains(id) || self.has(VoteKind::Cancel, id) {", "            if false {", "owned_future_root_prefence"),
        ("skip-catch-up", "        if current == target {", "        if current != target {", "owned_driver_early_byzantine_quorums"),
        ("one-shot-evidence", "            if pending.is_empty() || pending.len() == before {", "            if true {", "owned_partial_publication"),
    ]
    try:
        for name, before, after, test in mutations:
            assert original.count(before) == 1, name
            path.write_text(original.replace(before, after))
            result = run(["cargo", "test", "-p", "cbcl-parser", "--test", "quorum_runtime", test, "--offline"], expect_failure=True)
            assert "test result: FAILED" in result.stdout, "must fail behavior, not compilation"
            path.write_text(original)
            print(f"Rust negative control {name}: detected")
    finally:
        path.write_text(original)
    model = (ROOT / "lean-cbcl/LeanCbcl/ConsensusFree/OwnedLifecycle.lean").read_text()
    before = "(∀ y, s.votes y w = true → y = x ∨ c.held x y = true)"
    assert model.count(before) == 1
    with tempfile.TemporaryDirectory(prefix="cbcl-owned-mutation-") as temp:
        mutant = Path(temp) / "OwnedMutant.lean"
        mutant.write_text(model.replace(before, "(∀ y, s.votes y w = true → y = x ∨ True)"))
        result = run(["lake", "env", "lean", str(mutant)], ROOT / "lean-cbcl", expect_failure=True)
        assert "error:" in result.stdout
    print("Lean weakened-history guard: kernel proof rejected")
    for name, source, before, after in [
        ("dependency-guard", "OwnedProgress.lean", "if c.verified i && (c.dependencies i).all known then", "if c.verified i then"),
        ("reservation-accounting", "OwnerFunding.lean", "- marked s.accepted (fun i => c.debit i d)", "- marked s.issued (fun i => c.debit i d)"),
    ]:
        original_model = (ROOT / "lean-cbcl/LeanCbcl/ConsensusFree" / source).read_text()
        assert before in original_model
        with tempfile.TemporaryDirectory(prefix="cbcl-progress-mutation-") as temp:
            mutant = Path(temp) / "ProgressMutant.lean"
            mutant.write_text(original_model.replace(before, after, 1))
            result = run(["lake", "env", "lean", str(mutant)], ROOT / "lean-cbcl", expect_failure=True)
            assert "error:" in result.stdout or "error(" in result.stdout
        print(f"Lean negative control {name}: kernel proof rejected")
    run(["cargo", "test", "-p", "cbcl-parser", "--test", "quorum_runtime", "owned_", "--offline"])
    print("Restored implementation: PASS")


if __name__ == "__main__":
    main()
