#!/usr/bin/env python3
"""Build per-trial and per-cell CSVs from the Demo 3 measurement logs.

Walks every `cell-*-shard*.log` (post-2026-05-07 parallel sweep format) and
`cell-*.log` (pre-2026-05-07 sequential sweep format) under
`crates/cbcl-arena/measurements/N100-*-2026-05-{05,07}/`, parses per-trial
`utility=X security=Y` lines, and joins to per-trial token/cost data
extracted from each trial's JSONL transcript.

Outputs:
    <out>/trial_data.csv      one row per trial (4000 rows for the 4-provider
                              x 10-cell x N=100 sweep)
    <out>/cell_aggregates.csv one row per (provider, demo, cell)

Both CSVs include provenance fields (run date, wire format, temperature, log
path, transcript path) so that reviewers can trace any reported number back
to its source. Schema is documented in
`<paper-repo>/demo2-data/README.md`.

Usage:
    python build_csvs.py --out demo2-data/

Reads from cbcl-rs/ relative paths; run from the cbcl-rs repo root or pass
absolute paths via --measurements and --transcripts.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path

# Round-robin attacker assignments. Mirrors examples/glm_psi.rs:229 and
# examples/glm_yao.rs:220. The order MUST match the source; if either
# function changes, update these lists.
PSI_PATTERNS = [
    "direct-ask",
    "operator-impersonation",
    "premature-final",
    "response-injection",
    "social-pressure",
]
YAO_PATTERNS = [
    "direct-ask",
    "compare-by-naming",
    "threshold-injection",
    "social-pressure",
    "operator-impersonation",
    "bracket-flooding",
    "premature-final",
    "range-reframe",
    "protocol-mimicry",
]

ATTACKER_CELLS = {"free", "disciplined", "native-attacker"}

# Provider tag in transcript filenames (e.g. `glm51-free-000.jsonl`).
PROVIDER_TAG = {
    "glm": "glm51",
    "codex": "gpt55",
    "haiku": "hk45",
    "deepseek": "dsk32",
}

MODEL_LABEL = {
    "glm": "GLM-5.1",
    "codex": "GPT-5.5",
    "haiku": "Haiku 4.5",
    "deepseek": "DeepSeek V3.2",
}

WIRE_FORMAT = {
    "glm": "Z.AI direct",
    "codex": "OpenAI public Chat Completions API (gpt-5.5)",
    "haiku": "OpenRouter -> Anthropic (claude-haiku-4.5)",
    "deepseek": "OpenRouter -> DeepSeek (deepseek-v3.2)",
}

TEMPERATURE = {
    "glm": "0",
    "codex": "1 (default; gpt-5.5 rejects T=0)",
    "haiku": "0",
    "deepseek": "0",
}

# Threshold for treating a cell log as broken (API-cascade failure).
# Logs with more than this many `first attempt failed` lines are excluded;
# the seat returns abstention defaults on every error so the cell aggregate
# becomes mean-of-errors rather than a measurement.
BROKEN_LOG_RETRY_THRESHOLD = 50

TRIAL_LINE_RE = re.compile(
    r"^\[glm_(?P<demo>psi|yao)\] (?P<cell>\S+) trial (?P<trial>\d+): "
    r"utility=(?P<u>-?\d+) security=(?P<s>-?\d+)"
)


def provider_from_path(path: str) -> str:
    for needle, prov in [("codex", "codex"), ("haiku", "haiku"),
                         ("deepseek", "deepseek"), ("glm", "glm")]:
        if needle in path:
            return prov
    return "unknown"


def is_broken_log(path: Path) -> bool:
    text = path.read_text(errors="replace")
    return text.count("first attempt failed") > BROKEN_LOG_RETRY_THRESHOLD


def attacker_pattern(demo: str, cell: str, trial: int) -> str:
    if cell not in ATTACKER_CELLS:
        return ""
    if demo == "psi":
        return PSI_PATTERNS[trial % len(PSI_PATTERNS)]
    return YAO_PATTERNS[trial % len(YAO_PATTERNS)]


def transcript_relpath(provider: str, demo: str, cell: str, trial: int) -> str:
    tag = PROVIDER_TAG[provider]
    if demo == "yao":
        return f"crates/cbcl-arena/transcripts/{tag}-yao-{cell}-{trial:03d}.jsonl"
    return f"crates/cbcl-arena/transcripts/{tag}-{cell}-{trial:03d}.jsonl"


def usage_for_trial(transcript_root: Path, rel_path: str) -> dict | None:
    """Walk a trial's JSONL and aggregate per-turn API usage."""
    full = transcript_root / Path(rel_path).name
    if not full.exists():
        # rel_path is "crates/cbcl-arena/transcripts/X.jsonl"; try basename match
        full = transcript_root / Path(rel_path).name
    if not full.exists():
        return None
    n_turns = 0
    pt = ct = 0
    cost = 0.0
    cost_seen = False
    for line in full.open():
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        n_turns += 1
        usage = (obj.get("response") or {}).get("usage") or {}
        # Chat Completions: prompt_tokens / completion_tokens
        # Responses API: input_tokens / output_tokens
        pt += int(usage.get("prompt_tokens") or usage.get("input_tokens") or 0)
        ct += int(usage.get("completion_tokens") or usage.get("output_tokens") or 0)
        if "cost" in usage and usage["cost"] is not None:
            cost += float(usage["cost"])
            cost_seen = True
    return {
        "turns": n_turns,
        "prompt_tokens": pt,
        "completion_tokens": ct,
        "usd_cost": round(cost, 6) if cost_seen else None,
    }


def wilson_ci(p: float, n: int, z: float = 1.96) -> tuple[float, float]:
    if n == 0:
        return (0.0, 0.0)
    den = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / den
    margin = z * (((p * (1 - p) + z * z / (4 * n)) / n) ** 0.5) / den
    return (max(0.0, centre - margin), min(1.0, centre + margin))


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument(
        "--measurements",
        type=Path,
        default=Path("crates/cbcl-arena/measurements"),
        help="Path to measurements directory (default: crates/cbcl-arena/measurements).",
    )
    p.add_argument(
        "--transcripts",
        type=Path,
        default=Path("crates/cbcl-arena/transcripts"),
        help="Path to transcripts directory (default: crates/cbcl-arena/transcripts).",
    )
    p.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output directory (will write trial_data.csv and cell_aggregates.csv).",
    )
    return p.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    args.out.mkdir(parents=True, exist_ok=True)

    # Load order matters: broken-data sources first, fresh sources last
    # (last-write-wins on conflicting (provider, demo, cell, trial) keys).
    load_order = [
        # (glob pattern relative to --measurements, run_date)
        ("N100-glm-2026-05-05/cell-*.log", "2026-05-05"),
        ("N100-haiku-2026-05-05/cell-*.log", "2026-05-05"),
        ("N100-codex-2026-05-07/cell-*-shard*.log", "2026-05-07"),
        ("N100-haiku-2026-05-07/cell-*-shard*.log", "2026-05-07"),
        ("N100-deepseek-2026-05-07/cell-*-shard*.log", "2026-05-07"),
    ]

    trials: dict[tuple, dict] = {}
    n_skipped_broken = 0
    n_lines = 0
    for rel_glob, run_date in load_order:
        for log_path in sorted(args.measurements.glob(rel_glob)):
            if is_broken_log(log_path):
                n_skipped_broken += 1
                continue
            prov = provider_from_path(str(log_path))
            log_rel = str(log_path.resolve())
            # Try to make log path repo-relative for portability.
            try:
                cbcl_rs_root = args.measurements.resolve().parents[2]
                log_rel = str(log_path.resolve().relative_to(cbcl_rs_root))
            except (ValueError, IndexError):
                pass
            for line in log_path.open(errors="replace"):
                m = TRIAL_LINE_RE.match(line)
                if not m:
                    continue
                n_lines += 1
                key = (prov, m.group("demo"), m.group("cell"), int(m.group("trial")))
                trials[key] = {
                    "provider": prov,
                    "model": MODEL_LABEL[prov],
                    "demo": m.group("demo"),
                    "cell": m.group("cell"),
                    "trial": int(m.group("trial")),
                    "utility": int(m.group("u")),
                    "security": int(m.group("s")),
                    "run_date": run_date,
                    "wire_format": WIRE_FORMAT[prov],
                    "temperature": TEMPERATURE[prov],
                    "log_path": log_rel,
                }

    print(f"loaded {len(trials)} trials ({n_lines} lines parsed, "
          f"{n_skipped_broken} broken logs skipped)")

    # Enrich each trial with transcript-derived data
    n_missing = 0
    for key, row in trials.items():
        prov, demo, cell, trial = key
        rel = transcript_relpath(prov, demo, cell, trial)
        row["transcript_path"] = rel
        row["attacker_pattern"] = attacker_pattern(demo, cell, trial)
        u = usage_for_trial(args.transcripts, rel)
        if u is None:
            n_missing += 1
            row["turns"] = ""
            row["prompt_tokens"] = ""
            row["completion_tokens"] = ""
            row["usd_cost"] = ""
        else:
            row["turns"] = u["turns"]
            row["prompt_tokens"] = u["prompt_tokens"]
            row["completion_tokens"] = u["completion_tokens"]
            row["usd_cost"] = "" if u["usd_cost"] is None else u["usd_cost"]
    if n_missing:
        print(f"warning: {n_missing} transcripts not found", file=sys.stderr)

    # Write per-trial CSV
    trial_csv = args.out / "trial_data.csv"
    fields = [
        "provider", "model", "demo", "cell", "trial",
        "utility", "security",
        "run_date", "wire_format", "temperature",
        "log_path", "transcript_path", "attacker_pattern",
        "turns", "prompt_tokens", "completion_tokens", "usd_cost",
    ]
    with trial_csv.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields)
        w.writeheader()
        for key in sorted(trials):
            w.writerow(trials[key])
    print(f"wrote {trial_csv}: {len(trials)} rows")

    # Aggregate per-cell
    cells = defaultdict(list)
    for row in trials.values():
        cells[(row["provider"], row["model"], row["demo"], row["cell"])].append(row)

    cell_csv = args.out / "cell_aggregates.csv"
    cell_fields = [
        "provider", "model", "demo", "cell", "n_trials",
        "utility_mean_native_scale", "utility_mean_x4_scale",
        "utility_min", "utility_max",
        "leak_count", "leak_rate", "leak_ci_lo_95", "leak_ci_hi_95",
        "run_date", "wire_format", "temperature",
        "mean_turns", "total_prompt_tokens", "total_completion_tokens",
        "total_usd_cost",
    ]
    with cell_csv.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cell_fields)
        w.writeheader()
        for key in sorted(cells):
            rows = cells[key]
            n = len(rows)
            us = [r["utility"] for r in rows]
            ss = [r["security"] for r in rows]
            leaks = sum(1 for s in ss if s == -1)
            rate = leaks / n
            lo, hi = wilson_ci(rate, n)
            turns_vals = [r["turns"] for r in rows if r["turns"] != ""]
            pt_vals = [r["prompt_tokens"] for r in rows if r["prompt_tokens"] != ""]
            ct_vals = [r["completion_tokens"] for r in rows if r["completion_tokens"] != ""]
            cost_vals = [float(r["usd_cost"]) for r in rows if r["usd_cost"] != ""]
            prov, model, demo, cell = key
            w.writerow({
                "provider": prov,
                "model": model,
                "demo": demo,
                "cell": cell,
                "n_trials": n,
                "utility_mean_native_scale": round(sum(us) / n, 4),
                "utility_mean_x4_scale": round(sum(us) / n * 4, 4),
                "utility_min": min(us),
                "utility_max": max(us),
                "leak_count": leaks,
                "leak_rate": round(rate, 4),
                "leak_ci_lo_95": round(lo, 4),
                "leak_ci_hi_95": round(hi, 4),
                "run_date": rows[0]["run_date"],
                "wire_format": WIRE_FORMAT[prov],
                "temperature": TEMPERATURE[prov],
                "mean_turns": round(sum(int(t) for t in turns_vals) / len(turns_vals), 2) if turns_vals else "",
                "total_prompt_tokens": sum(int(p) for p in pt_vals) if pt_vals else "",
                "total_completion_tokens": sum(int(c) for c in ct_vals) if ct_vals else "",
                "total_usd_cost": round(sum(cost_vals), 4) if cost_vals else "",
            })
    print(f"wrote {cell_csv}: {len(cells)} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
