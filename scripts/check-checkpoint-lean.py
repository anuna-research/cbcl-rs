#!/usr/bin/env python3
"""SPEC-035 TEST-3519: trust-zero Lean checks and semantic proof falsification.

Run ONLY after the proof owner freezes and builds the local imports. No source or
build-cache module is rewritten. Exact live source/compiled-import hashes bind the
baseline; mutants compile stand-alone copies of executable definitions. A proof
rejection requires a semantic diagnostic INSIDE an existing theorem, not a syntax,
import, missing-name or timeout failure. This is not a Rust compiled-test kill.

Usage: scripts/check-checkpoint-lean.py --check-source  # no Lean execution
       scripts/check-checkpoint-lean.py               # after final proof freeze
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean-cbcl"
MODULES = LEAN / "LeanCbcl"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SUPPORTED = ("initial", "values", "valuesPerKey", "observedSet", "lwwRegister", "lwwPerSigner", "lwwMap")
RUST_ADAPTER = ROOT / "crates/cbcl-checkpoint/src/summary.rs"
NATIVE_INVENTORY = MODULES / "StateKernelClause.lean"
RUST_TO_LEAN = dict(zip(
    ("Initial", "Values", "ValuesPerKey", "ObservedSet", "LwwRegister", "LwwPerSigner", "LwwMap"),
    SUPPORTED))


def runtime_inventory(source):
    """Accept only a closed matches! whitelist; reject new guards or wildcards."""
    start = re.search(r"\bfn supported\(r: &Rule\) -> bool\s*\{", source)
    if not start or len(re.findall(r"\bfn supported\s*\(", source)) != 1:
        raise ValueError("missing or ambiguous runtime supported whitelist")
    depth, end = 1, start.end()
    while end < len(source) and depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    body = source[start.end():end-1]
    match = re.fullmatch(r"\s*matches!\(\s*r\s*,(.*?)\)\s*", body, re.S)
    if depth or not match:
        raise ValueError("runtime supported is not a closed matches whitelist")
    names = []
    for arm in match.group(1).split("|"):
        variant = re.fullmatch(r"\s*Rule::(\w+)\s*\{\s*\.\.\s*\}\s*", arm)
        if not variant or variant.group(1) not in RUST_TO_LEAN:
            raise ValueError("unknown runtime supported arm: " + arm.strip())
        names.append(variant.group(1))
    if len(names) != len(set(names)) or set(names) != set(RUST_TO_LEAN):
        raise ValueError("runtime supported rules differ from proved seven")
    return names


def native_inventory(source):
    inventory = re.search(r"inductive Rule where(.*?)deriving DecidableEq", source, re.S)
    heads = re.search(r"def Rule.head : Rule → String(.*?)(?=/--|\ndef )", source, re.S)
    if not inventory or not heads:
        raise ValueError("missing full native rule/head inventory")
    names = re.findall(r"(?m)^\s*\|\s+(\w+)", inventory.group(1))
    pairs = re.findall(r'\|\s*\.(\w+)\s+\.\.\s*=>\s*"([^"\n]+)"', heads.group(1))
    residue = re.sub(r'\|\s*\.\w+\s+\.\.\s*=>\s*"[^"\n]+"', '', heads.group(1))
    if (residue.strip() or len(names) != 16 or len(set(names)) != 16
            or [name for name, _ in pairs] != names
            or len({head for _, head in pairs}) != 16):
        raise ValueError("full native sixteen-rule head inventory changed shape")
    return dict(pairs)

STATEMENT = """theorem render_advance_checkpoint (input : Input) (fields : List (String × Rule))
    (history tail : List Act) :
    ((Snapshot.checkpoint input fields history).advance input tail).render input =
      fullFold input fields (history ++ tail)"""
AUDITED = {
    "CBCL.CheckpointSummary." + name for name in
    ("step_preserves", "checkpoint_continuation", "live_current", "live_own")
} | {
    "CBCL.CheckpointKernel." + name for name in
    ("rule_step_valid", "rule_render_eq", "snapshot_advance_valid", "resume_valid_snapshot",
     "render_advance_checkpoint", "render_checkpoint", "native_expression",
     "native_compile_fields", "fullFoldRaw_native", "native_compile_clause",
     "render_advance_native_clause")
}
# Change executable semantics, never theorem statements or tactic scripts.
MUTANTS = [
    ("drop-old-pending-suppressions", "CheckpointSummary",
     "let old := s.pending.filter (fun p => p.2 != e.addr)",
     "let old : List (Scope × Nat) := []"),
    ("retire-across-every-scope", "CheckpointSummary",
     "c.replacing r && decide (c.scope r = c.scope w) && r.replaces.contains w.addr",
     "c.replacing r && r.replaces.contains w.addr"),
    ("ignore-duplicate-coverage", "CheckpointSummary",
     "if coverage e.addr then s else", "if false then s else"),
    ("discard-new-lww-register-winner", "CheckpointKernel",
     "CheckpointCompact.LwwRegister.step input.clock input.signerRank v c s e (coverage e.addr)",
     "s"),
]


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def strip_noncode(text):
    """Ignore nested Lean comments and string literals; preserve line numbers."""
    out, i, block, string = [], 0, 0, False
    while i < len(text):
        if block:
            if text.startswith("/-", i): block += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i): block -= 1; out.extend("  "); i += 2
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text): out.extend("  "); i += 2
            elif text[i] == '"': string = False; out.append(" "); i += 1
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i)); i = end
        elif text.startswith("/-", i): block = 1; out.extend("  "); i += 2
        elif text[i] == '"': string = True; out.append(" "); i += 1
        else: out.append(text[i]); i += 1
    if block or string:
        raise ValueError("unterminated source comment/string")
    return "".join(out)


def source_checks():
    files = sorted(MODULES.glob("Checkpoint*.lean"))
    if not files: raise ValueError("missing checkpoint proof modules")
    for path in files:
        code = strip_noncode(path.read_text())
        banned = re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|debug\.skipKernelTC", code)
        if banned: raise ValueError("forbidden unchecked construct in {}: {}".format(path.name, banned.group()))
    kernel = strip_noncode((MODULES / "CheckpointKernel.lean").read_text())
    inventory = re.search(r"inductive Rule where(.*?)deriving DecidableEq", kernel, re.S)
    if not inventory or tuple(re.findall(r"(?m)^\s*\|\s+(\w+)", inventory.group(1))) != SUPPORTED:
        raise ValueError("supported checkpoint rule inventory changed")
    runtime = runtime_inventory(RUST_ADAPTER.read_text())
    native = native_inventory(NATIVE_INVENTORY.read_text())
    if not set(SUPPORTED) <= native.keys():
        raise ValueError("proved rules absent from full native inventory")
    match = re.search(r"\btheorem\s+render_advance_checkpoint\b.*?(?=\s*:=\s*by)", kernel, re.S)
    if not match or " ".join(match.group().split()) != " ".join(STATEMENT.split()):
        raise ValueError("main theorem statement changed or acquired extra hypotheses")
    # Independent native evaluator on each side, not a renderer defined by the
    # desired equality. Full source bindings still require independent review.
    for text in ("view (evaluate {input with acts := r.live s} [] r.expression)",
                 "view (evaluate {input with acts := H} [] r.expression)"):
        if " ".join(text.split()) not in " ".join(kernel.split()):
            raise ValueError("native renderer/reference evaluator binding changed")
    requests = set(re.findall(r"^#print axioms\s+(\S+)", (MODULES / "CheckpointKernelTests.lean").read_text(), re.M))
    if not {name.rsplit(".", 1)[-1] for name in AUDITED} <= requests:
        raise ValueError("tests omit a required named theorem axiom report")
    for name, module, before, _ in MUTANTS:
        if (MODULES / (module + ".lean")).read_text().count(before) != 1:
            raise ValueError("{}: expected exactly one executable mutation anchor".format(name))
    return {"theorem": "CBCL.CheckpointKernel.render_advance_checkpoint",
            "statement": STATEMENT, "unchecked_source_constructs": [],
            "required_axiom_reports": sorted(AUDITED), "supported_checkpoint_rules": list(SUPPORTED),
            "runtime_supported_rules": runtime,
            "runtime_to_proved_rules": {name: RUST_TO_LEAN[name] for name in runtime},
            "native_full_rule_heads": native,
            "inventory_source_sha256": {str(p.relative_to(ROOT)): sha(p)
                                        for p in (RUST_ADAPTER, NATIVE_INVENTORY)},
            "observation_boundary": "extensional semantic views, not JSON byte equality"}


def bindings():
    paths = list(MODULES.rglob("*.lean")) + [RUST_ADAPTER]
    paths += [LEAN / x for x in ("LeanCbcl.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json") if (LEAN / x).is_file()]
    # Record precisely which compiled local imports trust-zero checking loads.
    paths += list((LEAN / ".lake/build/lib/lean/LeanCbcl").rglob("*.olean"))
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)}


def run(command, timeout):
    started = time.monotonic()
    p = subprocess.Popen(command, cwd=str(LEAN), stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True, encoding="utf-8",
                         errors="replace", start_new_session=True,
                         env=dict(os.environ, NO_COLOR="true"))
    timed_out = False
    try:
        try: stdout, stderr = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True; os.killpg(p.pid, signal.SIGKILL); stdout, stderr = p.communicate()
    except BaseException:
        if p.poll() is None: os.killpg(p.pid, signal.SIGKILL)
        p.wait(); raise
    return {"command": command, "cwd": str(LEAN), "exit_code": p.returncode,
            "timed_out": timed_out, "elapsed_seconds": round(time.monotonic() - started, 3),
            "stdout": stdout, "stderr": stderr}


def axiom_audit(output):
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    found = {}
    for name, axioms in re.findall(pattern, output, re.S):
        names = {a.strip() for a in axioms.split(",") if a.strip()}
        if names - ALLOWED: raise ValueError("{} uses non-foundational axioms: {}".format(name, sorted(names - ALLOWED)))
        if name in found: raise ValueError("duplicate axiom report: " + name)
        found[name] = sorted(names)
    if AUDITED - found.keys(): raise ValueError("missing axiom reports: " + str(sorted(AUDITED - found.keys())))
    return found


def proof_rejection(result, source):
    code = strip_noncode(source)
    # Only errors inside named theorem declarations count. Definition/type/parser
    # failures by themselves do not establish that a theorem rejected semantics.
    declarations = list(re.finditer(r"(?m)^(?:@\[[^\n]+\]\s*)?(?:private\s+)?(theorem|def|structure|inductive|namespace|end)\b[^\n]*", code))
    ranges = []
    for i, d in enumerate(declarations):
        if d.group(1) == "theorem":
            start = code[:d.start()].count("\n") + 1
            end = code[:declarations[i+1].start()].count("\n") + 1 if i+1 < len(declarations) else len(code.splitlines())+1
            name = re.search(r"\btheorem\s+(\S+)", d.group()).group(1)
            ranges.append((start, end, name))
    output = result["stdout"] + result["stderr"]
    diagnostics = re.findall(r"(?m)^(.+?\.lean):(\d+):(\d+): error: ([^\n]+)", output)
    invalid = re.compile(r"unknown (?:module|constant|identifier|namespace)|object file|file not found|failed to import|unexpected token|expected token|unterminated|invalid character|unrecognized tactic", re.I)
    proof = re.compile(r"unsolved goals|type mismatch|tactic.*(?:failed|failure)|`(?:grind|simp)` failed|application type mismatch|failed to synthesize", re.I)
    errors = []
    bad = False
    for path, line, column, message in diagnostics:
        theorem = next((name for start,end,name in ranges if start <= int(line) < end), None)
        bad |= bool(invalid.search(message))
        if theorem and proof.search(message):
            errors.append({"theorem": theorem, "line": int(line), "column": int(column), "message": message})
    rejected = result["exit_code"] != 0 and not result["timed_out"] and bool(errors) and not bad
    return rejected, errors


def write_report(path, report):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", dir=str(path.parent), delete=False, prefix=".lean-proof-") as f:
        json.dump(report, f, indent=2); f.write("\n"); temporary = f.name
    os.replace(temporary, path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-source", action="store_true", help="Static source/anchor check only; does not execute Lean or replace proof evidence.")
    parser.add_argument("--output", type=Path, default=ROOT / "proofs/cached-checkpoints/lean-proof-checks.json")
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    if args.timeout <= 0: parser.error("--timeout must be positive")
    try: checked = source_checks()
    except (OSError, ValueError) as error:
        print("Source check failed: " + str(error), file=sys.stderr); return 1
    if args.check_source:
        print("Source-only checks passed: exact main theorem, named axiom requests, no unchecked constructs, four unique semantic mutation anchors. No Lean execution.")
        return 0
    report = {"schema_version": 1, "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "complete": False, "passed": False, "trust_level": 0, "source_checks": checked,
              "runner_sha256": sha(Path(__file__)), "source_and_compiled_import_sha256": bindings(),
              "allowed_axioms": sorted(ALLOWED), "baselines": [], "proof_mutations": [],
              "scope": "Typed compact-summary/native-kernel model. Does not verify Rust, extraction, serialization, admission, cryptography or host durability; independent review/parity bridge required."}
    write_report(args.output, report)
    try:
        version = run(["lake", "env", "lean", "--version"], args.timeout); report["toolchain"] = version
        if version["exit_code"] or not re.search(r"\bversion 4\.27\.0\b", version["stdout"] + version["stderr"]):
            raise ValueError("Lean 4.27.0 toolchain check failed")
        # Control the original executable-definition modules as well as the
        # requested trust-zero named theorem/counterexample suite.
        for module in ("CheckpointSummary", "CheckpointKernel", "CheckpointKernelTests"):
            result = run(["lake", "env", "lean", "-t", "0", "LeanCbcl/" + module + ".lean"], args.timeout)
            report["baselines"].append(result)
            output = result["stdout"] + result["stderr"]
            if result["exit_code"] or result["timed_out"] or re.search(r"sorryAx|declaration uses ['\"]sorry['\"]", output):
                raise ValueError("trust-zero baseline failed: " + module)
            if module == "CheckpointKernelTests": report["axiom_audit"] = axiom_audit(output)
            print("baseline {}: PASS".format(module), flush=True); write_report(args.output, report)
        with tempfile.TemporaryDirectory(prefix="cbcl-checkpoint-lean-") as directory:
            for name,module,before,after in MUTANTS:
                original = (MODULES / (module + ".lean")).read_text()
                changed = original.replace(before, after, 1)
                path = Path(directory) / (module + ".lean"); path.write_text(changed)
                result = run(["lake", "env", "lean", "-t", "0", str(path)], args.timeout)
                rejected, errors = proof_rejection(result, changed)
                record = dict(result, mutation=name, module=module, before=before, after=after,
                              mutated_source_sha256=sha(path), proof_rejected=rejected,
                              theorem_errors=errors, status="proof_rejected" if rejected else "not_a_proof_rejection")
                report["proof_mutations"].append(record)
                print("{}: {}".format(name, record["status"]), flush=True); write_report(args.output, report)
        drift = [name for name,h in report["source_and_compiled_import_sha256"].items() if not (ROOT/name).is_file() or sha(ROOT/name)!=h]
        report["live_binding_drift"] = drift
        report["complete"] = True
        report["passed"] = not drift and len(report["proof_mutations"]) == len(MUTANTS) and all(r["proof_rejected"] for r in report["proof_mutations"])
    except (OSError, ValueError, KeyboardInterrupt) as error:
        report["error"] = str(error) or "interrupted"
        print("Proof checker failure: " + report["error"], file=sys.stderr)
    report["finished_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    write_report(args.output, report)
    print(json.dumps({"complete": report["complete"], "passed": report["passed"],
                      "proof_rejections": [r["mutation"] for r in report["proof_mutations"] if r["proof_rejected"]],
                      "report": str(args.output)}, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
