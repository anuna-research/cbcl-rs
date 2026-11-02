#!/usr/bin/env python3
"""Kernel checks and negative controls for SPEC-034's initialized product.

Temporary fused sources leave the worktree untouched. Mutations must produce a
proof/witness failure, never just a missing module or changed import path.
"""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean-cbcl"
MODEL = LEAN / "LeanCbcl/ConsensusFree"


def run(args, failure=False):
    p = subprocess.run(args, cwd=LEAN, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if failure:
        assert p.returncode != 0, "negative control survived"
        assert "error:" in p.stdout and "unknown module" not in p.stdout.lower(), p.stdout
        assert "sorryAx" not in p.stdout, p.stdout
    else:
        assert p.returncode == 0, p.stdout
        assert "declaration uses 'sorry'" not in p.stdout, p.stdout
    return p.stdout


def main():
    args = argparse.ArgumentParser()
    args.add_argument("--mutations", action="store_true")
    opts = args.parse_args()
    run(["lake", "build", "LeanCbcl.ConsensusFree.OwnerProductWitness"])
    audit = run(["lake", "env", "lean", "OwnerProductAudit.lean"])
    axioms = set()
    for match in re.finditer(r"depends on axioms:\s*\[([^\]]*)\]", audit):
        axioms.update(x.strip() for x in match.group(1).split(",") if x.strip())
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, audit
    assert "admitted_eventually_always_complete" in audit and "sorryAx" not in audit
    print("Initialized product, no-deadlock + eventual/persistent completion, fair Byzantine-silence witness, standard axioms: PASS", flush=True)
    if not opts.mutations:
        return
    product = (MODEL / "OwnerProduct.lean").read_text()
    termination = (MODEL / "OwnerTermination.lean").read_text().split("\n", 1)[1]
    witness = (MODEL / "OwnerProductWitness.lean").read_text().split("\n", 1)[1]
    fused = product + "\n" + termination + "\n" + witness
    changes = [
        ("manifest-without-drain", "| .manifest i => head s i ∧ s.bits (.g .frozen) = true ∧ drained s", "| .manifest i => head s i ∧ s.bits (.g .frozen) = true ∧ True", "grind"),
        ("unfunded-pinned-books", "allocation := setAt s.allocation i (OwnerFunding.allocation c.costs (funds s))", "allocation := setAt s.allocation i (fun _ => 0)", "Type mismatch"),
        ("stale-operation-signature-fairness", "Pending s ∧ Unfinal s i ∧ s.bits (.u .operation i) = false", "Pending s ∧ Unfinal s i", "decide"),
    ]
    with tempfile.TemporaryDirectory(prefix="cbcl-deadlock-") as tmp:
        path = Path(tmp) / "Mutant.lean"
        for name, before, after, evidence in changes:
            assert fused.count(before) == 1, name
            path.write_text(fused.replace(before, after, 1))
            output = run(["lake", "env", "lean", str(path)], failure=True)
            assert evidence in output, output
            print(f"Negative control {name}: rejected by proof/witness", flush=True)
        # An easier receipt guard still permits the completion proof. Adapt the
        # matching proof term too, so the behavioral root-import witness must fail.
        before = "| .deliverRoot w => s.bits (.g .seal) = true ∧\n      ∃ i, s.bits (.root i) = true ∧ s.bits (.l .metadata i w) = true"
        assert fused.count(before) == 1
        mutant = fused.replace(before, "| .deliverRoot _ => s.bits (.g .seal) = true", 1)
        before_term = "⟨sealed, ⟨rootIndex, rootPublished, metadata w hw rootIndex (h.rootVersion rootIndex rootPublished)⟩⟩ _ rfl"
        assert mutant.count(before_term) == 1
        path.write_text(mutant.replace(before_term, "sealed _ rfl", 1))
        output = run(["lake", "env", "lean", str(path)], failure=True)
        assert "decide" in output, output
        print("Negative control root-QC-without-local-proposal: rejected by executable witness", flush=True)
    print("Original worktree source unchanged; all negative controls detected", flush=True)


if __name__ == "__main__":
    main()
