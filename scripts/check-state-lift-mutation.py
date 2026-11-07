#!/usr/bin/env python3
"""SPEC-038 REQ-3800/3801: reject dropped puts and incorrect clock candidates.

Compile a baseline copy before mutating, so an import/tool failure cannot
count as a killed semantic mutant. The working proof is never overwritten.
"""
from pathlib import Path
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[1]
    lean_dir = root / "lean-cbcl"
    source = (lean_dir / "LeanCbcl/StateLift.lean").read_text()
    candidate = "(clock a).map fun stamp => HlcRegister.decorate (fun _ => stamp) a"
    mutants = [
        ("dropped-put",
         "def lift (g : Act → L) (A : List Act) : L := A.foldl (fun acc a => acc ⊔ g a) ⊥",
         "def lift (g : Act → L) (A : List Act) : L := A.foldl (fun acc _ => acc) ⊥",
         "lift_cons", "lift_append"),
        ("address-only-clock", candidate,
         "(clock a).map fun _ => HlcRegister.decorate (fun _ => (0, 0, 0)) a",
         "physical_precedes_address", "logical_precedes_address"),
        ("unrecognized-clock-admitted", candidate,
         "some (HlcRegister.decorate (fun _ => (clock a).getD (0, 0, 0)) a)",
         "all_unrecognized_have_no_winner", None),
        ("domain-filter-bypassed",
         "A.filter fun a => domains.all fun d => a.verb != d.verb ||\n"
         "    inDomain d.key (initialAllowed d.opener d.field A) a",
         "A", "excluded_replacer_cannot_erase_value", "unrecognized_group_value_is_absent"),
        ("absent-group-value-dropped",
         "if T.isEmpty then none else some (scalar clock field T)",
         "(scalar clock field T).map some",
         "unrecognized_group_value_is_absent", "nonexistent_group_has_no_entry"),
    ]
    for name, original, _, _, _ in mutants:
        if source.count(original) != 1:
            raise SystemExit(f"FAIL: {name} anchor is missing or ambiguous")
    with tempfile.TemporaryDirectory(prefix="cbcl-state-lift-") as directory:
        path = Path(directory) / "StateLift.lean"

        def compile_copy(text):
            path.write_text(text)
            return subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=lean_dir,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=180,
            )

        baseline = compile_copy(source)
        if baseline.returncode != 0:
            print(baseline.stdout)
            raise SystemExit("FAIL: baseline proof does not compile")
        print("PASS: baseline compiles")
        for name, original, mutant, theorem, following in mutants:
            broken = source.replace(original, mutant)
            result = compile_copy(broken)
            # Require an error in the targeted proof, not an unrelated failure.
            start = broken.index(f"theorem {theorem}")
            end = (broken.index(f"theorem {following}", start) if following
                   else broken.index("end HlcLift", start))
            first = broken[:start].count("\n") + 1
            last = broken[:end].count("\n") + 1
            errors = [line for line in result.stdout.splitlines()
                      if any(f"StateLift.lean:{n}:" in line
                             for n in range(first, last)) and "error:" in line]
            if result.returncode == 0 or not errors:
                print(result.stdout)
                raise SystemExit(f"FAIL: {name} did not fail {theorem}")
            print(f"PASS: {name} rejected by {theorem}")
            print("\n".join(errors))


if __name__ == "__main__":
    main()
