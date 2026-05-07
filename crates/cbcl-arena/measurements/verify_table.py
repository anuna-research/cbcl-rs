#!/usr/bin/env python3
"""Cross-check the published Table 1 against the per-cell CSV.

Reads `tab-malicious-peer-results.tex` and `cell_aggregates.csv`, then
verifies every leak rate and cooperative-utility cell in the table matches
the audit-grade aggregate. PSI utilities use the operator's native scale
$[-4, +4]$; Yao utilities use the $\times 4$ presentation scale (rendered
to give the same dynamic range as PSI). Exits non-zero on any mismatch.

Usage:
    python verify_table.py \\
        --table /path/to/tab-malicious-peer-results.tex \\
        --csv /path/to/demo2-data/cell_aggregates.csv

If neither flag is given, defaults assume:
    paper repo root contains   tables/tab-malicious-peer-results.tex
    paper repo root contains   demo2-data/cell_aggregates.csv
and the script is run from the paper repo root.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path


# Provider label as it appears in the table source -> CSV provider key
ROW_LABEL_TO_PROVIDER = {
    "GLM-5.1": "glm",
    "GPT-5.5": "codex",
    "Haiku 4.5": "haiku",
    "DeepSeek V3.2": "deepseek",
    "Llama 3.3 70B": "llama",
}

ROW_RE = re.compile(
    r"(GLM-5\.1|GPT-5\.5|Haiku 4\.5|DeepSeek V3\.2|Llama 3\.3 70B)\s*\n"
    r"\s*&\s*\\makecell\{([^}]+)\}\s*\n"   # group 1
    r"\s*&\s*\\makecell\{([^}]+)\}\s*\n"   # group 2
    r"\s*&\s*\\makecell\{([^}]+)\}\s*\n"   # group 3
    r"\s*&\s*\\makecell\{([^}]+)\}\s*\n"   # group 4
    r"\s*&\s*\\makecell\{([^}]+)\}\s*\n"   # group 5
    r"\s*&\s*\\makecell\{([^}]+)\}\s*\\\\"  # group 6
)

# The first three columns and the last three columns are each assigned to
# either PSI or Yao based on the multicolumn header line, so column order
# (PSI-first vs Yao-first) is a presentation choice independent of cell
# content. Verifier reads the header to figure out which is which.
HEADER_RE = re.compile(
    r"\\multicolumn\{3\}\{c\}\{([^}]+)\}"
)

LEAK_RE = re.compile(r"^\s*([\d.]+)\s*\[\s*([\d.]+)\s*,\s*([\d.]+)\s*\]")
UTIL_RE = re.compile(r"/\s*(-?\$?-?[\d.]+\$?|--)\s*$")


def parse_cell(cell_str: str) -> tuple[float | None, float | None, float | None, float | None]:
    """Parse a `LEAK [LO, HI] / UTIL` cell. Returns (leak%, lo%, hi%, util_or_None)."""
    leak_m = LEAK_RE.search(cell_str)
    if not leak_m:
        return None, None, None, None
    leak = float(leak_m.group(1))
    lo = float(leak_m.group(2))
    hi = float(leak_m.group(3))
    util_m = UTIL_RE.search(cell_str)
    util = None
    if util_m:
        s = util_m.group(1).replace("$", "").replace("--", "")
        if s:
            util = float(s)
    return leak, lo, hi, util


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--table", type=Path, default=Path("tables/tab-malicious-peer-results.tex"))
    p.add_argument("--csv", type=Path, default=Path("demo2-data/cell_aggregates.csv"))
    p.add_argument("--tolerance", type=float, default=0.005,
                   help="Absolute tolerance for utility comparison (default: 0.005).")
    p.add_argument("--leak-tolerance", type=float, default=0.6,
                   help="Absolute tolerance for leak rate (percentage points; default: 0.6).")
    return p.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)

    # Load CSV
    csv_rows = list(csv.DictReader(args.csv.open()))
    by_key = {(r["provider"], r["demo"], r["cell"]): r for r in csv_rows}

    # Parse table
    src = args.table.read_text()
    rows = ROW_RE.findall(src)
    if len(rows) != 5:
        print(f"FAIL: expected 5 provider rows in table, found {len(rows)}", file=sys.stderr)
        return 2

    # Determine column ordering from the multicolumn header. The first multicolumn
    # spans the first three data columns, the second spans the last three.
    headers = HEADER_RE.findall(src)
    if len(headers) != 2:
        print(f"FAIL: expected 2 multicolumn headers, found {len(headers)}", file=sys.stderr)
        return 2
    def header_to_demo(label: str) -> str:
        if "PSI" in label or "Set Intersection" in label: return "psi"
        if "Yao" in label or "Millionaire" in label: return "yao"
        raise ValueError(f"could not classify header '{label}' as PSI or Yao")
    first_block_demo = header_to_demo(headers[0])
    second_block_demo = header_to_demo(headers[1])
    if {first_block_demo, second_block_demo} != {"psi", "yao"}:
        print(f"FAIL: headers do not cover both demos: {headers}", file=sys.stderr)
        return 2

    failures: list[str] = []

    for label, c1, c2, c3, c4, c5, c6 in rows:
        # Map the six raw cells to (psi_f, psi_s, psi_n, yao_f, yao_s, yao_n)
        # using the column ordering announced by the header.
        first_cells, second_cells = (c1, c2, c3), (c4, c5, c6)
        if first_block_demo == "psi":
            psi_f, psi_s, psi_n = first_cells
            yao_f, yao_s, yao_n = second_cells
        else:
            yao_f, yao_s, yao_n = first_cells
            psi_f, psi_s, psi_n = second_cells
        prov = ROW_LABEL_TO_PROVIDER[label]

        cells = [
            ("psi", "free",                psi_f, "x1"),
            ("psi", "disciplined",         psi_s, "x1"),
            ("psi", "native-attacker",     psi_n, "x1"),
            ("yao", "free",                yao_f, "x4"),
            ("yao", "disciplined",         yao_s, "x4"),
            ("yao", "native-attacker",     yao_n, "x4"),
        ]
        # Cooperative-utility numbers in the shim/native columns are the
        # `cooperative` and `native-cooperative` cells respectively, not the
        # `disciplined` and `native-attacker` cells. Cooperative utility
        # appears in the same cell as the attacker leak rate, so we look up
        # the cooperative utility separately.
        coop_util_lookups = [
            ("psi", "cooperative",         psi_s, "x1"),  # PSI shim col
            ("psi", "native-cooperative",  psi_n, "x1"),  # PSI native col
            ("yao", "cooperative",         yao_s, "x4"),  # Yao shim col
            ("yao", "native-cooperative",  yao_n, "x4"),  # Yao native col
        ]

        for demo, cell, cell_str, scale in cells:
            leak_table, _, _, _ = parse_cell(cell_str)
            csv_row = by_key.get((prov, demo, cell))
            if csv_row is None:
                failures.append(f"{label} {demo}/{cell}: no CSV row")
                continue
            leak_csv = float(csv_row["leak_rate"]) * 100
            if leak_table is None:
                failures.append(f"{label} {demo}/{cell}: failed to parse leak from table cell '{cell_str}'")
                continue
            if abs(leak_table - leak_csv) > args.leak_tolerance:
                failures.append(
                    f"{label} {demo}/{cell}: leak rate table={leak_table:.1f}% "
                    f"csv={leak_csv:.1f}% (diff > {args.leak_tolerance}pp)"
                )

        for demo, csv_cell, cell_str, scale in coop_util_lookups:
            _, _, _, util_table = parse_cell(cell_str)
            if util_table is None:
                continue  # cooperative util not present in this column (e.g. LLM-only)
            csv_row = by_key.get((prov, demo, csv_cell))
            if csv_row is None:
                failures.append(f"{label} {demo}/{csv_cell}: no CSV row for cooperative util")
                continue
            field = "utility_mean_x4_scale" if scale == "x4" else "utility_mean_native_scale"
            util_csv = float(csv_row[field])
            if abs(util_table - util_csv) > args.tolerance:
                failures.append(
                    f"{label} {demo}/{csv_cell}: util table={util_table} csv={util_csv} "
                    f"({field}); diff > {args.tolerance}"
                )

    if failures:
        print("FAIL: table does not match CSV", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print("OK: every table cell matches cell_aggregates.csv "
          "(PSI on native scale, Yao x4 to match GLM presentation)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
