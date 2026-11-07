#!/usr/bin/env python3
"""SPEC-035: falsify checkpoint guards in an isolated, locked/offline workspace.

Only copied Rust implementation files are mutated. The complete small workspace
source, native dialect definitions and original Cargo.lock are frozen together;
no live core/parser dependency or caller source is symlinked into a mutant. A
baseline executes each exact selected test before mutation. A kill requires that
same named test to execute and FAIL; build errors, timeouts, missing tests and
survivors are reported separately and cause a nonzero exit. No scaling test runs.

Usage: python3 scripts/check-checkpoint-mutations.py
       python3 scripts/check-checkpoint-mutations.py --mutation quorum-below-three

The default v2 report is proofs/cached-checkpoints/all16-runtime-mutations.json. A partial run is
explicitly incomplete. The reusable build cache is target/checkpoint-mutants;
Cargo dev/test debug information and incremental compilation are disabled.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from typing import Tuple

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "crates/cbcl-checkpoint/src/"


@dataclass(frozen=True)
class Edit:
    path: str
    before: str
    after: str
    regex: bool = False


@dataclass(frozen=True)
class Mutant:
    name: str
    test: str
    edits: Tuple[Edit, ...]
    guard: str


def edit(file, before, after, regex=False):
    return Edit(PREFIX + file, before, after, regex)


def mutants():
    return [
        Mutant("quorum-below-three",
               "lifecycle_tests::native_certificate_roundtrip_threshold_scope_and_no_companion_history",
               (edit("certificate.rs", "self.endorsements.len() < c.policy.threshold()",
                     "self.endorsements.len() < c.policy.threshold().saturating_sub(1)"),),
               "A valid two-signature certificate must fail the pinned three-signature threshold."),
        Mutant("scope-bypass",
               "lifecycle_tests::native_certificate_roundtrip_threshold_scope_and_no_companion_history",
               (edit("certificate.rs",
                     'if a.fields.get(k) != Some(&SExpr::Atom(Atom::Str(v))) {',
                     'if false {'),
                edit("certificate.rs",
                     'if a.fields.get("manifest") != Some(&SExpr::Atom(Atom::Str(hex(&h)))) {',
                     'if false {')),
               "Correctly signed wrong-scope or wrong-manifest claims must fail independently of Context/Manifest pin checks."),
        Mutant("duplicate-endorsements-count",
               "lifecycle_tests::native_certificate_roundtrip_threshold_scope_and_no_companion_history",
               (edit("certificate.rs",
                     "if previous.is_some_and(|p| p >= i) || !seen.insert(i) {",
                     "if (previous.is_some_and(|p| p >= i) || !seen.insert(i)) && false {"),),
               "Repeated valid signatures from one member cannot count as distinct votes."),
        Mutant("ignore-cached-content-address",
               "lifecycle_tests::cache_corruption_symlinks_and_runtime_modes_fail_closed",
               (edit("host.rs",
                     'if hash(b"cbcl/checkpoint/blob/v1", &blob) != offer.blob {',
                     'if false {'),),
               "A provider returning a different valid certificate must fail the requested blob hash, not merely parsing/signatures."),
        Mutant("accept-absent-floor-head",
               "member::tests::proof_footprint_failure_is_atomic_and_floor_checks_final_root",
               (edit("member.rs",
                     'if !p.present {\n                return Err(Error::Invalid("local rollback"));\n            }',
                     'if false {\n                return Err(Error::Invalid("local rollback"));\n            }'),),
               "An authentic absence proof for a remembered head cannot satisfy the local floor."),
        Mutant("forget-previous-signed-evidence",
               "member::tests::covered_replays_preserve_distinct_signature_attempts_without_refolding",
               (edit("member.rs",
                     r'self\.evidence\s*=\s*self\.evidence\.retaining\(&previous\.evidence\);',
                     '// MUTANT: omit already supplied signed evidence.', regex=True),),
               "A no-resupply rebase must retain all original signed attempts, including alternate signatures for one identity."),
        Mutant("generation-cas-bypass",
               "lifecycle_tests::concurrent_evidence_outbox_retry_and_local_edits_all_invalidate_staged_installation",
               (edit("host.rs", "if p.expected_generation != self.generation {", "if false {"),),
               "Evidence, local edits, outbox and retry changes must invalidate an earlier prepared installation."),
        Mutant("drop-summary-suppression",
               "summary::tests::all_fourteen_plain_rules_every_prefix_cut_permutation_duplicate",
               (edit("summary.rs", "if writer(r, act) && !suppressed {", "if writer(r, act) {"),),
               "An arriving previously suppressed contribution cannot become live merely because it arrived late."),
        Mutant("managed-key-capability-bypass",
               "lifecycle_tests::managed_key_custody_rejects_generic_endorsement_signing",
               (edit("certificate.rs",
                     '.is_some_and(|p| p.name() == "endorse")',
                     '.is_some_and(|_| false)'),),
               "The managed generic signer cannot sign an endorsement without the opaque profile capability."),
        Mutant("ignore-offer-byte-budget",
               "lifecycle_tests::offer_parser_enforces_lengths_and_cumulative_limits",
               (edit("host.rs", "Reader::new(bytes, limits.offer_bytes)?",
                     "Reader::new(bytes, usize::MAX)?"),),
               "An otherwise valid complete offer above its byte limit must fail independently of step counts, truncation and total limits."),
        Mutant("store-binding-bypass",
               "lifecycle_tests::prepared_install_cannot_substitute_another_stores_floor_or_evidence_snapshot",
               (edit("host.rs", "if p.store_binding != Some(self.instance)", "if false"),),
               "Prepared state from a different store must fail even with identical generation and floor; the captured-floor check remains enabled."),
        Mutant("companion-thread-bypass",
               "lifecycle_tests::native_certificate_roundtrip_threshold_scope_and_no_companion_history",
               (edit("certificate.rs",
                     'if msg.message().innermost_simple().and_then(Message::thread) != Some(thread.0.as_str()) {',
                     'if false {'),),
               "Authentic correctly scoped endorsements on a foreign thread must fail independently of signature, scope and causal-parent checks."),
        Mutant("failed-fetch-budget-bypass",
               "lifecycle_tests::failed_fetches_consume_their_allowance_and_orphan_temporary_files_do_not_block_recovery",
               (edit("host.rs",
                     r'metrics\.bytes\s*=\s*metrics\s*\.bytes\s*\.checked_add\(reserved\)\s*\.ok_or\(Error::Budget\)\?;',
                     '// MUTANT: failed fetches consume no reserved allowance.', regex=True),),
               "Failed/partial fetches consume their reserved allowance before another candidate can be fetched; the test uses only failed fetches so success-refund arithmetic cannot mask this guard."),
        Mutant("current-manifest-prefix-scan",
               "member::tests::member_archive_counters_measure_actual_delta_reads_and_current_freeze",
               (edit("member.rs",
                     "pub fn manifest(&self, c: &Context) -> Result<Manifest> {",
                     "pub fn manifest(&self, c: &Context) -> Result<Manifest> {\n        for message in self.archive.iter() { let _ = message.id()?; }"),),
               "A current manifest must not traverse historical bodies: this mutant actually scans and hashes each archived message through the counted iterator, without audit_replay recursion or fake counter increments."),
        Mutant("native-causal-verifier-bypass",
               "member::tests::invalid_and_missing_footprints_never_change_client_or_evidence",
               (edit("member.rs",
                     r'let verdict = verify_causal_for_role\(\s*step\.message\.message\(\),\s*&endpoint\(c\)\?,\s*&c\.target,\s*&cast,\s*&resumed,\s*&thread\(c\)\?,\s*&ContentHash\(root_id\),\s*\);',
                     'let verdict = VerificationResult::Valid;', regex=True),),
               "Even an authenticated uncovered message with valid coverage proofs must fail the ordinary native causal/role verdict when it is at the wrong protocol position."),
        Mutant("independent-authorization-capability-bypass",
               "member::tests::older_known_cut_derives_independently_unknown_and_tampered_cuts_decline",
               (edit("member.rs",
                     'if self.derive(&manifest.frontier, c, keys)? != *manifest {',
                     'if false {'),),
               "Opaque endorsement authority cannot be issued for a proposed root or state that differs from independently reconstructed history; this is separate from managed generic-signing custody."),
        Mutant("native-signature-verification-bypass",
               "member::tests::stale_proofs_wrong_context_language_and_bad_signatures_cannot_install",
               (edit("certificate.rs",
                     'if !keys.verify(&key, &codec::message_bytes(&unsigned), &sig) {',
                     'if false {'),),
               "An otherwise unchanged, correctly addressed native message carrying an invalid zeroed 64-byte signature must fail authentication independently of managed signing capabilities, proof freshness, context and language checks."),
    ]


def anchor_matches(text, change):
    pattern = change.before if change.regex else re.escape(change.before)
    return list(re.finditer(pattern, text))


def check_anchors(selected):
    """Read-only source/test name check; this is NOT execution/kill evidence."""
    rust_sources = list((ROOT / PREFIX).glob("*.rs"))
    errors = []
    for mutant in selected:
        for change in mutant.edits:
            count = len(anchor_matches((ROOT / change.path).read_text(), change))
            if count != 1:
                errors.append("{}: {} anchor occurs {} times".format(mutant.name, change.path, count))
        name = mutant.test.rsplit("::", 1)[-1]
        count = sum(len(re.findall(r"\bfn\s+" + re.escape(name) + r"\s*\(", path.read_text()))
                    for path in rust_sources)
        if count != 1:
            errors.append("{}: test function {} occurs {} times".format(mutant.name, name, count))
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("Read-only check: {} mutation anchors and selected test names found; no Rust tests or mutations executed.".format(len(selected)))
    return 0


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def atomic_report(path, report):
    path.parent.mkdir(parents=True, exist_ok=True)
    name = None
    try:
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(path.parent),
                                         prefix=".checkpoint-mutations-", delete=False) as out:
            name = out.name
            json.dump(report, out, indent=2)
            out.write("\n")
            out.flush()
            os.fsync(out.fileno())
        os.replace(name, path)
    finally:
        if name and os.path.exists(name):
            os.unlink(name)


def stop_process(process):
    if process.poll() is None:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            return
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()


def run(command, cwd, env, timeout):
    started = time.monotonic()
    try:
        process = subprocess.Popen(command, cwd=str(cwd), env=env,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True, encoding="utf-8", errors="replace",
                                   start_new_session=True)
    except OSError as error:
        return {"exit_code": None, "timed_out": False, "stdout": "",
                "stderr": str(error), "elapsed_seconds": time.monotonic() - started,
                "command": command}
    timed_out = False
    try:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            stop_process(process)
            stdout, stderr = process.communicate()
    except BaseException:
        stop_process(process)
        raise
    return {"exit_code": process.returncode, "timed_out": timed_out,
            "stdout": stdout, "stderr": stderr,
            "elapsed_seconds": round(time.monotonic() - started, 3), "command": command}


def executed_test(result, name, outcome):
    """Require the exact Rust test record AND libtest's numeric result summary."""
    stdout = result["stdout"]
    record = re.search(r"^test " + re.escape(name) + r" \.\.\. " + outcome + r"\s*$",
                       stdout, re.MULTILINE)
    summary = re.search(r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed;",
                        stdout, re.MULTILINE)
    if not record or not summary or result["timed_out"]:
        return False
    if outcome == "ok":
        return result["exit_code"] == 0 and summary.groups() == ("ok", "1", "0")
    return result["exit_code"] == 101 and summary.groups() == ("FAILED", "0", "1")


def self_test():
    """Exercise scorer false positives without creating Rust build artifacts."""
    name = "member::tests::guard"
    good = {"exit_code": 0, "timed_out": False, "stderr": "", "stdout":
            "test " + name + " ... ok\ntest result: ok. 1 passed; 0 failed;\n"}
    failed = dict(good, exit_code=101, stdout=
                  "test " + name + " ... FAILED\ntest result: FAILED. 0 passed; 1 failed;\n")
    checks = [executed_test(good, name, "ok"), executed_test(failed, name, "FAILED")]
    not_kills = [
        dict(failed, stdout="", stderr="error: could not compile test crate"),
        dict(failed, stdout="running 0 tests\ntest result: ok. 0 passed; 0 failed;\n"),
        dict(failed, stdout=failed["stdout"].replace(name, "member::tests::different")),
        dict(failed, timed_out=True),
        dict(failed, exit_code=0),
        dict(failed, stdout=failed["stdout"].replace("0 passed; 1 failed", "0 passed; 0 failed")),
    ]
    checks.extend(not executed_test(r, name, "FAILED") for r in not_kills)
    checks.append(not executed_test(dict(good, stdout=good["stdout"].replace("1 passed", "0 passed")), name, "ok"))
    if not all(checks):
        raise ValueError("checkpoint mutation result scorer self-test failed")
    print("Scorer self-test: {} checks passed (compile errors/zero tests/wrong tests/timeouts are not kills).".format(len(checks)), flush=True)


def evidence(result):
    # Exact tests produce small output. Keep a bounded tail for infrastructure
    # errors as well, so a disk-full compiler failure cannot bloat the report.
    return dict(result, stdout=result["stdout"][-32768:], stderr=result["stderr"][-32768:])


def snapshot(destination):
    # Preserve the actual workspace and lock instead of synthesizing versions or
    # resolving a standalone crate afresh. All workspace manifests must exist for
    # Cargo --locked even though only cbcl-checkpoint --lib is built and tested.
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "rust-toolchain"):
        if (ROOT / name).is_file():
            shutil.copy2(ROOT / name, destination / name)
    ignore = shutil.ignore_patterns("target", ".git", "__pycache__", "*.pyc")
    for name in ("crates", "tools", "dialects"):
        shutil.copytree(ROOT / name, destination / name, ignore=ignore, symlinks=False)
    sources = [destination / "Cargo.toml", destination / "Cargo.lock"]
    for name in ("crates", "tools", "dialects"):
        sources.extend(p for p in (destination / name).rglob("*") if p.is_file())
    return {str(p.relative_to(destination)): digest(p) for p in sorted(sources)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-anchors", action="store_true", help="Read-only check of source anchors and test names; does not run mutations or replace evidence.")
    parser.add_argument("--self-test", action="store_true", help="Exercise result scoring without compiling Rust.")
    parser.add_argument("--output", type=Path, default=ROOT / "proofs/cached-checkpoints/all16-runtime-mutations.json")
    parser.add_argument("--target-dir", type=Path, default=ROOT / "target/checkpoint-mutants")
    parser.add_argument("--mutation", action="append", choices=[m.name for m in mutants()],
                        help="Run selected mutants only; the report explicitly records this subset.")
    parser.add_argument("--timeout", type=float, default=180,
                        help="Seconds allowed for each exact baseline/mutant test, including compilation.")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    target = args.target_dir.resolve()
    output = args.output.resolve()
    selected = [m for m in mutants() if not args.mutation or m.name in args.mutation]
    if args.check_anchors:
        return check_anchors(selected)
    target.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, CARGO_PROFILE_DEV_DEBUG="0", CARGO_PROFILE_TEST_DEBUG="0",
               CARGO_INCREMENTAL="0", CARGO_TERM_COLOR="never")
    report = {"schema_version": 1, "started_at": utc_now(), "complete": False,
              "all_killed": False, "full_suite": not bool(args.mutation),
              "selected_mutations": [m.name for m in selected],
              "target_dir": str(target), "runner_sha256": digest(Path(__file__)),
              "baselines": {}, "mutations": []}
    # A second invocation must not concurrently rewrite a shared mutation target
    # or replace the first runner's report. POSIX is also the host test platform.
    import fcntl
    with (target / ".runner.lock").open("w") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("Another checkpoint mutation runner owns this target directory.", file=sys.stderr)
            return 2
        try:
            with tempfile.TemporaryDirectory(prefix="cbcl-checkpoint-mutants-") as directory:
                isolated = Path(directory)
                (isolated / "test-tmp").mkdir()
                env["TMPDIR"] = str(isolated / "test-tmp")
                report["source_sha256"] = snapshot(isolated)
                report["lock_sha256"] = digest(isolated / "Cargo.lock")
                report["toolchain"] = {
                    tool: evidence(run([tool, "--version"], isolated, env, args.timeout))
                    for tool in ("cargo", "rustc")}
                atomic_report(output, report)

                def command(test):
                    return ["cargo", "test", "--manifest-path", str(isolated / "Cargo.toml"),
                            "--target-dir", str(target), "--offline", "--locked", "-p",
                            "cbcl-checkpoint", "--lib", test, "--", "--exact", "--nocapture",
                            "--test-threads=1"]

                for test in dict.fromkeys(m.test for m in selected):
                    result = run(command(test), isolated, env, args.timeout)
                    passed = executed_test(result, test, "ok")
                    report["baselines"][test] = dict(evidence(result), passed=passed)
                    print("baseline {}: {}".format(test, "PASS" if passed else "FAIL"), flush=True)
                    atomic_report(output, report)
                for mutant in selected:
                    record = {"mutation": mutant.name, "test": mutant.test,
                              "guard": mutant.guard, "killed_by_test": False,
                              "edits": [dict(path=e.path, before=e.before, after=e.after, regex=e.regex)
                                        for e in mutant.edits]}
                    originals = {}
                    try:
                        if not report["baselines"][mutant.test]["passed"]:
                            record["status"] = "baseline_failed"
                        else:
                            for e in mutant.edits:
                                path = isolated / e.path
                                if path not in originals:
                                    originals[path] = path.read_text()
                                text = path.read_text()
                                matches = anchor_matches(text, e)
                                if len(matches) != 1:
                                    raise ValueError("{}: anchor occurs {} times, expected exactly one".format(
                                        e.path, len(matches)))
                                match = matches[0]
                                record.setdefault("matched_edits", []).append({
                                    "path": e.path, "before": match.group(), "after": e.after})
                                path.write_text(text[:match.start()] + e.after + text[match.end():])
                            result = run(command(mutant.test), isolated, env, args.timeout)
                            record.update(evidence(result))
                            record["killed_by_test"] = executed_test(result, mutant.test, "FAILED")
                            if record["killed_by_test"]:
                                record["status"] = "killed"
                            elif result["timed_out"]:
                                record["status"] = "timeout"
                            elif executed_test(result, mutant.test, "ok"):
                                record["status"] = "survived"
                            else:
                                record["status"] = "infrastructure_or_compile_failure"
                    except (OSError, ValueError) as error:
                        record["status"] = "mutation_setup_failure"
                        record["error"] = str(error)
                    finally:
                        for path, original in originals.items():
                            path.write_text(original)
                    report["mutations"].append(record)
                    print("{}: {}".format(mutant.name, record["status"].upper()), flush=True)
                    atomic_report(output, report)
                # Detect accidental restoration drift in OUR snapshot as well.
                changed = [name for name, expected in report["source_sha256"].items()
                           if digest(isolated / name) != expected]
                report["snapshot_restored"] = not changed
                report["snapshot_drift"] = changed
                # The main agent may continue editing the shared source while we
                # test our frozen copy. Never silently present that old snapshot
                # as evidence for a newer source tree.
                live_drift = [name for name, expected in report["source_sha256"].items()
                              if not (ROOT / name).is_file() or digest(ROOT / name) != expected]
                report["live_source_matches_snapshot"] = not live_drift
                report["live_source_drift"] = live_drift
                report["complete"] = True
                report["all_killed"] = (not changed and len(report["mutations"]) == len(selected)
                                        and all(r["killed_by_test"] for r in report["mutations"]))
                report["finished_at"] = utc_now()
                atomic_report(output, report)
        except KeyboardInterrupt:
            report["interrupted"] = True
            atomic_report(output, report)
            print("Interrupted; report remains incomplete.", file=sys.stderr)
            return 130
        except (OSError, ValueError) as error:
            report["runner_error"] = str(error)
            atomic_report(output, report)
            print("Runner failure: {}".format(error), file=sys.stderr)
            return 2
    print(json.dumps({"complete": report["complete"], "all_killed": report["all_killed"],
                      "mutations": [{"mutation": r["mutation"], "status": r["status"],
                                     "killed_by_test": r["killed_by_test"]}
                                    for r in report["mutations"]], "report": str(output)}, indent=2))
    if not report["live_source_matches_snapshot"]:
        print("Live sources changed during this frozen run; inspect live_source_drift before accepting current-tree evidence.", file=sys.stderr)
    return 0 if report["all_killed"] and report["live_source_matches_snapshot"] else 1


if __name__ == "__main__":
    sys.exit(main())
