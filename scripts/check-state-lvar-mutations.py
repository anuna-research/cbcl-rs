#!/usr/bin/env python3
"""SPEC-038: exercise concrete observation proof obligations in isolated copies."""
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
module = "StateLVar"
source = (root / f"lean-cbcl/LeanCbcl/{module}.lean").read_text()
mutants = [
    ("dependency-fault-ignored", "if dependencyFault = true ∨ state = ⊤ then", "if state = ⊤ then", "thresholdRead_fault_first"),
    ("raw-history-discarded", "lift (fun a => FinSet.mk [a]) A", "FinSet.mk []", "rawHistory_eq"),
    ("initializer-fault-hidden", "| .top evidence => .fault evidence", "| .top _ => .value (FinSet.mk [])", "domain_fork_fault"),
    ("freeze-cut-ignored", "exact A.filter (fun a => decide (Ancestor world a f))", "exact A", "causalCut_agreement"),
    ("freezer-excluded-from-cut", "decide (Ancestor world a f)", "decide (Ancestor world a f ∧ a ≠ f)", "freezer_in_cut"),
    ("freeze-witness-address-dropped", "(address = a.addr ∨ address = b.addr)", "address = a.addr", "eventual_freeze_conflict"),
]
suites = [(module, source, mutants), ("StateContext",
    (root / "lean-cbcl/LeanCbcl/StateContext.lean").read_text(), [
    ("root-contribution-dropped", "if a.preds.isEmpty then", "if false then", "recognized_root_value"),
    ("invalid-root-hidden", "| .one address none => .fault {address}", "| .one _ none => .pending", "invalid_root_faults"),
    ("context-fault-hidden", "| .top evidence => .fault evidence", "| .top _ => .pending", "display_quasi"),
    ("context-evidence-dropped", "| .top evidence => .fault evidence", "| .top _ => .fault {}", "fault_evidence"),
])]
for module, source, mutants in suites:
    with tempfile.TemporaryDirectory(prefix="cbcl-state-lvar-") as directory:
        path = Path(directory) / f"{module}.lean"
        def compile_copy(text):
            path.write_text(text)
            return subprocess.run(["lake", "env", "lean", str(path)], cwd=root / "lean-cbcl",
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        baseline = compile_copy(source)
        if baseline.returncode:
            print(baseline.stdout)
            raise SystemExit("FAIL: baseline does not compile")
        print("PASS: baseline compiles", flush=True)
        for name, original, replacement, theorem in mutants:
            if source.count(original) != 1:
                raise SystemExit(f"FAIL: {name} anchor missing or ambiguous")
            broken = source.replace(original, replacement)
            result = compile_copy(broken)
            start = broken.index(f"theorem {theorem}")
            next_decl = re.search(r"\n(?:theorem|def|noncomputable def|end) ", broken[start:])
            end = start + next_decl.start() if next_decl else len(broken)
            first, last = broken[:start].count("\n") + 1, broken[:end].count("\n") + 1
            errors = [line for line in result.stdout.splitlines() if "error:" in line and
                      any(f"{module}.lean:{n}:" in line for n in range(first, last))]
            if not result.returncode or not errors:
                print(result.stdout)
                raise SystemExit(f"FAIL: {name} did not fail {theorem}")
            print(f"PASS: {name} rejected by {theorem}", flush=True)
