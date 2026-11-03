#!/usr/bin/env python3
"""Score a complete cargo-mutants run using its structured result counts."""

import json
from pathlib import Path
import sys


def check(directory, threshold):
    result = json.loads((directory / "outcomes.json").read_text())
    generated = json.loads((directory / "mutants.json").read_text())
    names = ("caught", "missed", "timeout", "unviable", "total_mutants")
    counts = {name: result[name] for name in names}
    if any(type(value) is not int or value < 0 for value in counts.values()):
        raise ValueError("mutation counts must be nonnegative integers")
    if not isinstance(generated, list) or len(generated) != counts["total_mutants"]:
        raise ValueError("not all generated mutants have results")
    if sum(counts[name] for name in names[:4]) != counts["total_mutants"]:
        raise ValueError("inconsistent or unclassified mutation results")
    # Independently reject absent/failed baselines, even if a tool version
    # unexpectedly exits with a scoreable status after a baseline failure.
    baselines = [o for o in result["outcomes"] if o["scenario"] == "Baseline"]
    if not baselines or any(o["summary"] != "Success" for o in baselines):
        raise ValueError("unmutated baseline did not succeed")
    viable = counts["caught"] + counts["missed"] + counts["timeout"]
    if viable == 0:
        raise ValueError("no viable mutants were tested")
    killed = counts["caught"] + counts["timeout"]
    # Preserve the existing policy: timeouts count as detected; unviable
    # mutants are excluded. Compare integers so rounding cannot pass a run.
    passed = killed * 100 >= threshold * viable
    print("=== Mutation Testing Results ===")
    for name in names[:4]:
        print(f"  {name}: {counts[name]}")
    print(f"  Viable: {viable}")
    print(f"{'PASS' if passed else 'FAIL'}: Kill rate {100 * killed / viable:.2f}% "
          f"(threshold: {threshold}%)")
    return 0 if passed else 1


if __name__ == "__main__":
    try:
        sys.exit(check(Path(sys.argv[1]), int(sys.argv[2])))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"FAIL: Cannot score mutation results: {error}", file=sys.stderr)
        sys.exit(1)
