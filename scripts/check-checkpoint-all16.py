#!/usr/bin/env python3
"""Closed all-sixteen checkpoint proof evidence and semantic mutation checks.

Run --check-source during development. Run full checks only after the proof owner
freezes/builds current imports in lean-cbcl. Source and compiled-import hashes are
captured before checks and must remain unchanged. Mutants are temporary standalone
copies; a kill needs a semantic error inside an existing theorem. This is a typed
model check, not proof of Rust extraction, wire crypto, resource finality or JSON.
"""
import argparse
import datetime
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("checkpoint_lean_evidence_helpers", HERE / "checkpoint_lean_support.py")
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
ROOT, LEAN, MODULES = helper.ROOT, helper.LEAN, helper.MODULES
MAPPING = {
    "Initial": "initial", "Exists": "existsRule", "Count": "count", "Progress": "progress",
    "Events": "events", "SetUnion": "setUnion", "Values": "values",
    "ValuesPerKey": "valuesPerKey", "ObservedSet": "observedSet", "Counter": "counter",
    "Histogram": "histogram", "Sum": "sum", "LwwRegister": "lwwRegister",
    "LwwPerSigner": "lwwPerSigner", "LwwMap": "lwwMap", "BoundedCounter": "boundedCounter",
}
STATEMENT = """theorem render_advance_checkpoint (ports : Ports) (input : Input)
    (fields : List (String × Rule)) (history tail : List Act) :
    ((Snapshot.checkpoint ports input fields history).advance ports input tail).render ports input =
      fullFold ports input fields (history ++ tail)"""
AUDITED = {
    "CBCL.CheckpointAll." + name for name in (
        "rule_step_valid", "rule_render_eq", "snapshot_step_valid", "snapshot_advance_valid",
        "snapshot_checkpoint_valid", "render_valid", "resume_valid_snapshot",
        "render_advance_checkpoint", "render_checkpoint", "snapshot_duplicate_noop",
        "native_expression", "native_compile_fields", "native_compile_clause",
        "render_advance_native_clause", "resolve_complete", "resolve_fields_complete",
        "render_advance_wellformed_clause", "position_advance_checkpoint",
        "resource_facts_advance_checkpoint")
} | {
    "CBCL.CheckpointData." + name for name in (
        "Exists.step_preserves", "Count.step_preserves", "Counter.step_preserves",
        "SetUnion.step_preserves", "Events.step_preserves", "Events.read_native",
        "Events.map_meaning", "Events.map_native", "exists_continuation", "count_continuation",
        "counter_continuation", "setUnion_continuation", "events_continuation")
} | {
    "CBCL.CheckpointEvidence." + name for name in (
        "project_ingest", "project_replay", "checkpoint_tail", "materialize_checkpoint_tail",
        "resolve_checkpoint_tail", "progress_checkpoint_tail_native",
        "resourceInput_checkpoint_tail", "resource_checkpoint_tail_native", "resourceInput_setEq")
}
MUTANTS = [
    ("drop-events-projected-value", "CheckpointData",
     "(e.get field).map (fun value => ⟨e.addr, e.signer, value⟩)",
     '(e.get field).map (fun _ => ⟨e.addr, e.signer, .str "mutant-dropped-value"⟩)'),
    ("skip-count-increment", "CheckpointData",
     "if coverage e.addr then s else if e.verb = verb then s + 1 else s",
     "if coverage e.addr then s else if e.verb = verb then s else s"),
    ("drop-progress-protocol-record", "CheckpointAll",
     "⟨e.addr, ports.protocol e⟩ :: s.protocol,", "s.protocol,"),
    ("drop-resource-verifier-record", "CheckpointAll",
     "⟨e.addr, ports.resource.extract e⟩ :: s.resource⟩", "s.resource⟩"),
]
BASELINES = ("CheckpointData", "CheckpointDataTests", "CheckpointEvidence",
             "CheckpointEvidenceTests", "CheckpointAll", "CheckpointAllTests")


def whitespace(text):
    return " ".join(text.split())


def braced(text, start):
    opening = text.index("{", start)
    depth = 1
    at = opening + 1
    while at < len(text) and depth:
        depth += (text[at] == "{") - (text[at] == "}")
        at += 1
    if depth:
        raise ValueError("unterminated inventory match")
    return text[opening+1:at-1]


def runtime_inventory(source):
    # Recognition of an exhaustive constructor match, rather than collecting
    # names appearing anywhere in the file. Unknown/wildcard/gated arms refuse.
    code = helper.strip_noncode(source)
    code = re.sub(r"//[^\n]*", "", code)
    marker = "rows.push(match rule {"
    if code.count(marker) != 1:
        raise ValueError("missing/ambiguous Summary.new row constructor match")
    body = braced(code, code.index(marker))
    names = re.findall(r"\bRule::(\w+)\b", body)
    if len(names) != len(MAPPING) or set(names) != set(MAPPING):
        raise ValueError("runtime constructor does not exhaust the native heads")
    if re.search(r"\b_\s*=>|\b(?:return|Err|Unsupported)\b", body):
        raise ValueError("wildcard or runtime refusal inside native row constructor")
    return names


def source_checks():
    files = sorted(MODULES.glob("Checkpoint*.lean"))
    if not files:
        raise ValueError("no checkpoint source files")
    for path in files:
        code = helper.strip_noncode(path.read_text())
        banned = re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|debug\.skipKernelTC", code)
        if banned:
            raise ValueError(f"unchecked construct in {path.name}: {banned.group()}")
    native = helper.native_inventory((MODULES / "StateKernelClause.lean").read_text())
    if set(native) != set(MAPPING.values()):
        raise ValueError("native inventory differs from the closed all-head mapping")
    runtime = runtime_inventory((ROOT / "crates/cbcl-checkpoint/src/summary.rs").read_text())
    all_source = (MODULES / "CheckpointAll.lean").read_text()
    all_code = helper.strip_noncode(all_source)
    found = re.search(r"\btheorem\s+render_advance_checkpoint\b.*?(?=\s*:=\s*by)", all_code, re.S)
    if not found or whitespace(found.group()) != whitespace(STATEMENT):
        raise ValueError("all-head theorem changed or acquired a correctness hypothesis")
    resolver = all_code.split("def resolve (", 1)[1].split("theorem map_source_native", 1)[0]
    resolved = re.findall(r"(?m)^\s*\|\s*\.(\w+)\b", resolver)
    if len(resolved) != len(MAPPING) or set(resolved) != set(MAPPING.values()):
        raise ValueError("native all-head resolver is not exhaustive")
    required = (
        "acts := H", "causal := CheckpointEvidence.referenceStore ports.protocol H",
        "resource := ports.resource.resourceInput H", "compileRule earlier raw = some r.expression",
        "evaluateFields (ports.input input (normalize (history ++ tail))) [] expressions",
    )
    for text in required:
        if whitespace(text) not in whitespace(all_code):
            raise ValueError("native evaluator/port binding changed: " + text)
    for name, module, before, _ in MUTANTS:
        if (MODULES / (module + ".lean")).read_text().count(before) != 1:
            raise ValueError("mutation requires one executable anchor: " + name)
    return {
        "theorem": "CBCL.CheckpointAll.render_advance_checkpoint", "statement": STATEMENT,
        "native_rule_heads": native, "runtime_constructed_rules": runtime,
        "runtime_to_proved_rules": MAPPING, "unchecked_source_constructs": [],
        "source_files_scanned": [str(p.relative_to(ROOT)) for p in files],
        "required_named_axiom_reports": sorted(AUDITED),
        "boundary": "typed observations and explicit native protocol/resource ports; no JSON-byte/extraction/cryptography claim",
    }


def semantic_rejection(result, source):
    rejected, errors = helper.proof_rejection(result, source)
    output = result["stdout"] + result["stderr"]
    # Lean error(code) diagnostics must not evade the historical helper's
    # plain-error parser. Missing names/imports/parser failures never count.
    forbidden = re.compile(r"unknown (?:module|constant|identifier|namespace)|object file|file not found|failed to import|unexpected token|expected token|unterminated|invalid character|unrecognized tactic", re.I)
    if forbidden.search(output):
        return False, errors
    code = helper.strip_noncode(source)
    declarations = list(re.finditer(r"(?m)^(?:@\[[^\n]+\]\s*)?(?:private\s+)?(theorem|def|abbrev|structure|inductive|namespace|end|example)\b", code))
    theorem_ranges = []
    for index, declaration in enumerate(declarations):
        if declaration.group(1) == "theorem":
            start = code[:declaration.start()].count("\n") + 1
            end = code[:declarations[index+1].start()].count("\n") + 1 if index+1 < len(declarations) else len(code.splitlines())+1
            theorem_ranges.append((start,end))
    diagnostics = re.findall(r"(?m)^.+?\.lean:(\d+):\d+: error(?:\([^)]*\))?: ([^\n]+)", output)
    if any(not any(start <= int(line) < end for start,end in theorem_ranges) for line,_ in diagnostics):
        return False, errors
    return rejected, errors


def audit(output):
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for name, axioms in re.findall(pattern, output, re.S):
        names = {a.strip() for a in axioms.split(",") if a.strip()}
        if name in found or names - helper.ALLOWED:
            raise ValueError("duplicate or non-foundational axiom report: " + name)
        found[name] = sorted(names)
    if set(found) != AUDITED:
        raise ValueError("axiom audit is not the exact named theorem set: " + str(sorted(AUDITED - set(found))))
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-source", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / "proofs/cached-checkpoints/all16-lean-checks.json")
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    try:
        checked = source_checks()
    except (ValueError, OSError, IndexError) as error:
        print("all-head source check failed: " + str(error), file=sys.stderr)
        return 1
    if args.check_source:
        print(json.dumps({"source_checks": "passed", "lean_executed": False,
                          "native_heads": list(checked["native_rule_heads"]),
                          "mutation_anchors": [m[0] for m in MUTANTS]}, indent=2))
        return 0
    report = {
        "schema_version": 1, "complete": False, "passed": False, "trust_level": 0,
        "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "runner_sha256": helper.sha(Path(__file__)), "helper_sha256": helper.sha(HERE / "checkpoint_lean_support.py"),
        "source_checks": checked, "source_and_compiled_import_sha256": helper.bindings(),
        "allowed_axioms": sorted(helper.ALLOWED), "baselines": [], "proof_mutations": [],
        "scope": "All native heads in typed Lean model; explicit native evidence extraction/classifier boundary. Not a Rust compiled-test mutant kill or host/security release approval.",
    }
    helper.write_report(args.output, report)
    try:
        version = helper.run(["lake", "env", "lean", "--version"], args.timeout)
        report["toolchain"] = version
        if version["exit_code"] or version["timed_out"] or not re.search(r"\bversion 4\.27\.0\b", version["stdout"] + version["stderr"]):
            raise ValueError("Lean 4.27.0 toolchain verification failed")
        baseline_modules = list(BASELINES)
        report["baseline_modules"] = baseline_modules
        for module in baseline_modules:
            result = helper.run(["lake", "env", "lean", "-t", "0", "LeanCbcl/" + module + ".lean"], args.timeout)
            report["baselines"].append(result)
            if result["exit_code"] or result["timed_out"] or re.search(r"sorryAx|declaration uses ['\"]sorry['\"]", result["stdout"] + result["stderr"]):
                raise ValueError("trust-zero baseline failed: " + module)
            print("baseline " + module + ": PASS", flush=True)
            helper.write_report(args.output, report)
        with tempfile.TemporaryDirectory(prefix="cbcl-checkpoint-all16-") as directory:
            path = Path(directory) / "NamedAxioms.lean"
            path.write_text("import LeanCbcl.CheckpointAll\n" + "\n".join("#print axioms " + name for name in sorted(AUDITED)) + "\n")
            result = helper.run(["lake", "env", "lean", "-t", "0", str(path)], args.timeout)
            report["named_axiom_run"] = result
            if result["exit_code"] or result["timed_out"]:
                raise ValueError("named trust-zero axiom audit failed")
            report["axiom_audit"] = audit(result["stdout"] + result["stderr"])
            for name, module, before, after in MUTANTS:
                changed = (MODULES / (module + ".lean")).read_text().replace(before, after, 1)
                path = Path(directory) / (module + ".lean")
                path.write_text(changed)
                result = helper.run(["lake", "env", "lean", "-t", "0", str(path)], args.timeout)
                rejected, errors = semantic_rejection(result, changed)
                report["proof_mutations"].append(dict(result, mutation=name, module=module,
                    before=before, after=after, mutated_source_sha256=helper.sha(path),
                    proof_rejected=rejected, theorem_errors=errors,
                    status="proof_rejected" if rejected else "not_a_proof_rejection"))
                print(name + ": " + ("proof_rejected" if rejected else "NOT REJECTED"), flush=True)
                helper.write_report(args.output, report)
        final_bindings = helper.bindings()
        initial_bindings = report["source_and_compiled_import_sha256"]
        report["live_binding_drift"] = [name for name in sorted(set(initial_bindings) | set(final_bindings))
            if initial_bindings.get(name) != final_bindings.get(name)]
        if helper.sha(Path(__file__)) != report["runner_sha256"] or helper.sha(HERE / "checkpoint_lean_support.py") != report["helper_sha256"]:
            report["live_binding_drift"].append("evidence checker source")
        report["complete"] = True
        report["passed"] = not report["live_binding_drift"] and len(report["proof_mutations"]) == len(MUTANTS) and all(r["proof_rejected"] for r in report["proof_mutations"])
    except (ValueError, OSError, KeyboardInterrupt) as error:
        report["error"] = str(error) or "interrupted"
    report["finished_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    helper.write_report(args.output, report)
    print(json.dumps({"complete": report["complete"], "passed": report["passed"], "error": report.get("error"), "report": str(args.output)}, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
