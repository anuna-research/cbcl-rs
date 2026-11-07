#!/usr/bin/env python3
"""Capture launch metadata and parse SPEC-035 native scaling evidence. Never runs tests.

Before the final Cargo run:
  python3 scripts/check-checkpoint-scaling.py --capture-manifest /tmp/checkpoint-native-acceptance.metadata.json
After the run:
  python3 scripts/check-checkpoint-scaling.py --log /tmp/checkpoint-native-acceptance.txt \
    --metadata /tmp/checkpoint-native-acceptance.metadata.json --require-persist

Default input: /tmp/checkpoint-native-final.txt. Default report:
proofs/cached-checkpoints/native-scaling.json. A growing/incomplete log produces
an explicitly incomplete report and exit 2; malformed/inconsistent data exits 1.
Source/toolchain captured while parsing is REPORT-TIME metadata, not retroactive
proof of what an earlier binary compiled. --metadata binds a separately captured
launch manifest; the caller owns freezing sources and recording the Cargo command.
"""

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SIZES = (600, 6000, 60000)
TEST = "native_eight_lane_600_6000_60000_delta32_publication_work"
COMMAND = ["cargo", "test", "-p", "cbcl-checkpoint", "--release", TEST,
           "--", "--ignored", "--nocapture"]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def command(args):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True,
                            timeout=15, check=False)
    return {"argv": args, "returncode": result.returncode,
            "stdout": result.stdout.strip(), "stderr": result.stderr.strip()}


def manifest():
    paths = {ROOT / name for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain",
             "rust-toolchain.toml", ".cargo/config", ".cargo/config.toml")}
    for crate in ("cbcl-core", "cbcl-parser", "cbcl-checkpoint"):
        base = ROOT / "crates" / crate
        paths.add(base / "Cargo.toml")
        paths.update((base / "src").rglob("*.rs"))
        paths.update((base / "tests").rglob("*.rs"))
    paths.add(ROOT / "dialects/checkpoint.cbcl")
    files = {str(path.relative_to(ROOT)): sha(path.read_bytes())
             for path in sorted(paths) if path.is_file()}
    return {
        "schema_version": 1,
        "captured_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "source_files_sha256": files,
        "source_manifest_sha256": sha(json.dumps(files, sort_keys=True).encode()),
        "git_head": command(["git", "rev-parse", "HEAD"]),
        "git_status": command(["git", "status", "--short"]),
        "rustc": command(["rustc", "--version", "--verbose"]),
        "cargo": command(["cargo", "--version"]),
        "host": {"os": platform.system(), "release": platform.release(),
                 "machine": platform.machine(), "logical_cpus": os.cpu_count()},
        "build_environment": {key: value for key, value in os.environ.items()
                              if key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS",
                                         "CARGO_BUILD_TARGET", "RUSTUP_TOOLCHAIN")
                              or key.startswith("CARGO_PROFILE_RELEASE_")},
        "intended_command": COMMAND,
    }


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + ".pending")
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temp.replace(path)


def source_comparison(launch, current):
    """Keep the full comparison; separately project out only unrelated unit tests."""
    if launch is None:
        return {"current_source_matches_launch": None,
                "implementation_scaling_source_matches_launch": None,
                "source_drift": None}
    before = launch["source_files_sha256"]
    after = current["source_files_sha256"]

    def unrelated_test(path):
        name = Path(path).name
        return name.endswith("_tests.rs") and name not in ("scaling_tests.rs", "test_support.rs")

    drift = [{"path": path,
              "change": "added" if path not in before else "removed" if path not in after else "modified",
              "launch_sha256": before.get(path), "current_sha256": after.get(path),
              "scope": "unrelated_unit_test" if unrelated_test(path) else "implementation_or_scaling"}
             for path in sorted(before.keys() | after.keys()) if before.get(path) != after.get(path)]
    launch_projected = {p: h for p, h in before.items() if not unrelated_test(p)}
    current_projected = {p: h for p, h in after.items() if not unrelated_test(p)}
    return {
        "current_source_matches_launch": launch["source_manifest_sha256"] == current["source_manifest_sha256"],
        "source_drift": drift,
        "implementation_scaling_source_matches_launch": launch_projected == current_projected,
        "implementation_scaling_source_manifest_sha256": {
            "launch": sha(json.dumps(launch_projected, sort_keys=True).encode()),
            "current": sha(json.dumps(current_projected, sort_keys=True).encode())},
        "source_projection_policy": "Exclude only files named *_tests.rs except scaling_tests.rs and test_support.rs. Keep production code, manifests/lockfile, dialects, scaling harness, test support, and all other captured files. Excluded changes remain in source_drift and never make current_source_matches_launch true.",
        "unrelated_test_paths_excluded_from_projection": sorted(
            p for p in before.keys() | after.keys() if unrelated_test(p)),
    }


def fields(text):
    """Recognize emitted key=value records, including complete nested JSON values."""
    decoder = json.JSONDecoder()
    values = {}
    while text.strip():
        text = text.lstrip()
        match = re.match(r"([A-Za-z][A-Za-z0-9_]*)=", text)
        if not match:
            raise ValueError("unrecognized native record suffix: " + text[:100])
        key = match[1]
        if key in values:
            raise ValueError("duplicate native record field: " + key)
        text = text[match.end():]
        if text.startswith(("{", "[", '"')):
            value, end = decoder.raw_decode(text)
            text = text[end:]
        else:
            token, _, text = text.partition(" ")
            if re.fullmatch(r"-?\d+", token):
                value = int(token)
            elif re.fullmatch(r"-?\d+\.\d+", token):
                value = float(token)
            elif token in ("true", "false"):
                value = token == "true"
            else:
                value = token
        values[key] = value
    return values


def parse(raw):
    records = []
    for number, line in enumerate(raw.splitlines(keepends=True), 1):
        if line.startswith("native-"):
            if not line.endswith("\n"):
                continue  # A live writer may not have finished this record.
            kind, _, text = line.strip().partition(" ")
            records.append({"kind": kind, "line": number, **fields(text)})
    return records


def summarize(records, raw, require_persist):
    errors, missing, rows = [], [], []
    setups = [r for r in records if "setup_context_us" in r]
    if len(setups) != 1:
        missing.append("exactly one fixed-context setup record")
    setup = setups[0] if len(setups) == 1 else None
    if setup and (setup.get("lanes") != 8 or not setup.get("covered_messages_not_state_edits")):
        errors.append("fixture must declare eight lanes and covered messages, not state edits")
    invariant_samples = []
    for size in SIZES:
        matching = [r for r in records if r.get("coveredMessages") == size]
        samples = []
        for repetition in range(3):
            sample = {"repetition": repetition}
            for record in matching:
                if record.get("repetition") == repetition:
                    for key, value in record.items():
                        if key not in ("kind", "line", "coveredMessages"):
                            if key in sample and sample[key] != value:
                                errors.append(f"conflicting {size}/{repetition}/{key}")
                            sample[key] = value
            if not all(key in sample for key in ("thread_cpu_ns", "wall_ns", "metrics")):
                missing.append(f"complete opening sample {size}/{repetition}")
            else:
                invariant_samples.append(sample)
            persist = sample.get("persist_work")
            if require_persist and persist is None:
                missing.append(f"warm persistence work {size}/{repetition}")
            if persist and persist.get("value_encodes") != sample.get("expected_new_bodies"):
                errors.append(f"warm persistence body count mismatch {size}/{repetition}")
            samples.append(sample)
        phase_keys = sorted({key for sample in samples for key in sample.get("metrics", {})
                             if key.endswith("_micros")})
        medians = {key: statistics.median([s[key] for s in samples])
                   for key in ("thread_cpu_ns", "wall_ns", "render_ns")
                   if all(key in s for s in samples)}
        phases = {key: statistics.median([s["metrics"][key] for s in samples])
                  for key in phase_keys if all(key in s.get("metrics", {}) for s in samples)}
        work = [r["member_archive_work"] for r in matching if "member_archive_work" in r]
        if len(work) != 1:
            missing.append(f"opening member-work record {size}")
        elif len(work[0]) != 3 or any(any(w.get(k) != 0 for k in (
                "dependency_body_lookups", "prefix_reconstruction_body_reads", "snapshot_body_records"))
                for w in work[0]):
            errors.append(f"opening accesses member archive at {size}")
        publication = [r for r in records if r["kind"] == "native-publication"
                       and r.get("checkpointCoveredMessages") == size]
        if len(publication) != 1:
            missing.append(f"publication work record {size}")
        else:
            p = publication[0]
            if p.get("delta") != 32 or p.get("baseCoveredMessages") != size + 2:
                errors.append(f"incorrect publication delta/base at {size}")
            if len(p.get("work", [])) != 3 or any(
                    w.get("dependency_body_lookups") != 32
                    or w.get("prefix_reconstruction_body_reads") != 0
                    or w.get("snapshot_body_records") != 0 for w in p.get("work", [])):
                errors.append(f"publication archive-work bound failed at {size}")
        rows.append({"covered_tick_messages": size, "samples": samples, "medians": medians,
                     "median_phases_micros": phases, "opening_member_work": work,
                     "publication_samples": publication, "publication_sample_count": len(publication)})
    for sample in invariant_samples:
        for key, expected in (("frontier", 8), ("finite_dependency_bodies", 2),
                              ("proof_paths", 12), ("signatures_checked", 23)):
            if sample.get(key) != expected:
                errors.append(f"{key} must equal {expected}")
    for key in ("certificate_bytes", "offer_bytes", "tail_signed_bytes", "dependency_signed_bytes", "floor_bytes"):
        values = {s.get(key) for s in invariant_samples}
        if None in values or len(values) > 1:
            errors.append(f"nonconstant or missing {key}")
    ratio = None
    if all("thread_cpu_ns" in row["medians"] for row in rows):
        smallest = rows[0]["medians"]["thread_cpu_ns"]
        if smallest <= 0:
            errors.append("nonpositive CPU measurement")
        else:
            ratio = rows[2]["medians"]["thread_cpu_ns"] / smallest
            if ratio > 2:
                errors.append("provisional largest/smallest median CPU target exceeds 2")
    passed = bool(re.search(r"test scaling_tests::" + TEST + r" \.\.\. ok", raw)
                  and re.search(r"test result: ok\. 1 passed; 0 failed;", raw))
    if not passed:
        missing.append("successful named combined depth test and terminal test result")
    return {"status": "invalid" if errors else "incomplete" if missing else "observed_pass",
            "setup": setup, "scaling": rows, "largest_smallest_median_thread_cpu_ratio": ratio,
            "errors": errors, "missing": missing,
            "warm_persistence_measured": all("persist_work" in s for row in rows for s in row["samples"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--log", type=Path, default=Path("/tmp/checkpoint-native-final.txt"))
    parser.add_argument("--metadata", type=Path, help="launch manifest from --capture-manifest")
    parser.add_argument("--capture-manifest", type=Path, help="capture metadata only; never runs Cargo tests")
    parser.add_argument("--output", type=Path, default=ROOT / "proofs/cached-checkpoints/native-scaling.json")
    parser.add_argument("--require-persist", action="store_true")
    args = parser.parse_args()
    current = manifest()
    if args.capture_manifest:
        write_json(args.capture_manifest, current)
        print(f"Launch manifest: {args.capture_manifest}")
        return 0
    data = args.log.read_bytes()
    raw = data.decode("utf-8", errors="strict")
    records = parse(raw)
    report = summarize(records, raw, args.require_persist)
    launch = json.loads(args.metadata.read_text()) if args.metadata else None
    report.update({"schema_version": 1, "spec": "SPEC-035-cached-state-checkpoints",
                   "tests": ["TEST-3514", "TEST-3515"],
                   "raw_log": {"path": str(args.log.resolve()), "sha256": sha(data),
                               "bytes": len(data), "text": raw},
                   "records": records, "launch_metadata": launch, "report_time_metadata": current,
                   "source_binding": "launch_manifest_supplied" if launch else "unverified_for_imported_log",
                   "measurement_boundary": "Thread CPU and wall time cover synchronous prepare plus durable commit; render is separate. Three independently admitting members and native full-history oracle run outside opening timing. Publication has one sample per scale, starts after the two-message opening tail, and includes durable storage before advertisement. Finite dependency bodies are distinct from prefix scans/replay.",
                   "prior_client": {"construction": "Client::from_certificate followed by DurableClient::create before timing",
                                    "floor": "Certified cut frontier (eight heads), not an empty floor",
                                    "retained_evidence": "Only the pinned signed target root before opening; not an empty evidence set",
                                    "covered_signed_archive_preloaded_on_disk": False,
                                    "interpretation": "Opening avoids downloading/folding the covered archive. This benchmark does not measure replacing a client already holding the whole covered signed archive; evidence.rs separately checks retained-archive persistence work."},
                   "limitations": ["Observed local experimental-profile evidence; not a production or browser-host ratification.",
                                    "Imported logs cannot establish historical source/toolchain identity without launch metadata.",
                                    "Warm persistence work is absent in logs recorded before its instrumentation.",
                                    "Prior client starts with a certificate floor and target-root evidence only, not the entire covered retained signed archive on disk."]})
    report.update(source_comparison(launch, current))
    write_json(args.output, report)
    print(f"{report['status']}: {args.output}")
    return {"observed_pass": 0, "incomplete": 2, "invalid": 1}[report["status"]]


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"checkpoint scaling evidence error: {error}", file=sys.stderr)
        sys.exit(1)
