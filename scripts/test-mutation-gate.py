#!/usr/bin/env python3
"""Exercise the actual shell gate without running or modifying Rust mutants."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().with_name("run-mutation-tests.sh")
FAKE_CARGO = r'''
import json, os
from pathlib import Path
import sys

if "--list" not in sys.argv:
    output = Path(sys.argv[sys.argv.index("--output") + 1]) / "mutants.out"
    output.mkdir()
    fixture = json.loads(os.environ["MUTATION_FIXTURE"])
    if fixture is not None:
        (output / "outcomes.json").write_text(json.dumps(fixture))
        (output / "mutants.json").write_text(json.dumps(
            [{}] * int(os.environ["GENERATED_MUTANTS"])))
    # No caught lines; misleading log text must not affect the score.
    print("MISSED warning: caught timeout unviable")
sys.exit(int(os.environ["MUTATION_EXIT"]))
'''


def result(caught=267, missed=29, timeout=5, unviable=44):
    return dict(caught=caught, missed=missed, timeout=timeout, unviable=unviable,
                total_mutants=caught + missed + timeout + unviable,
                outcomes=[dict(scenario="Baseline", summary="Success")])


class MutationGateTests(unittest.TestCase):
    def run_gate(self, data, status=3, generated=None, list_only=False):
        with tempfile.TemporaryDirectory(prefix="cbcl-mutation-gate-") as temp:
            root = Path(temp)
            for name in ("cargo", "cargo-mutants"):
                mock = root / name
                mock.write_text(f"#!{sys.executable}\n" + FAKE_CARGO)
                mock.chmod(0o755)
            env = dict(os.environ, PATH=f"{root}:{os.environ['PATH']}", TMPDIR=temp,
                       MUTATION_FIXTURE=json.dumps(data), MUTATION_EXIT=str(status),
                       GENERATED_MUTANTS=str(generated if generated is not None else
                                             (data or {}).get("total_mutants", 0)))
            return subprocess.run(["bash", str(SCRIPT)] + (["--list"] if list_only else []),
                                  env=env, cwd=temp, capture_output=True, text=True)

    def test_reported_ci_run_passes(self):
        run = self.run_gate(result())
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("90.37%", run.stdout)

    def test_exact_threshold_and_all_caught(self):
        for counts, status in [((90, 10, 0, 0), 2), ((100, 0, 0, 0), 0)]:
            with self.subTest(counts=counts):
                self.assertEqual(self.run_gate(result(*counts), status).returncode, 0)

    def test_below_threshold_fails(self):
        self.assertNotEqual(self.run_gate(result(89, 11, 0, 0), 2).returncode, 0)

    def test_baseline_and_tool_failures_propagate(self):
        for status in (1, 4, 5, 6, 70, 130):
            with self.subTest(status=status):
                self.assertEqual(self.run_gate(result(), status).returncode, status)

    def test_missing_and_incomplete_reports_fail(self):
        self.assertNotEqual(self.run_gate(None, 0).returncode, 0)
        self.assertNotEqual(self.run_gate(result(), generated=346).returncode, 0)

    def test_invalid_counts_and_baselines_fail(self):
        fixtures = [result(0, 0, 0, 44)]
        for key, value in [("caught", -1), ("caught", "267"), ("caught", True),
                           ("total_mutants", 344), ("outcomes", []),
                           ("outcomes", [dict(scenario="Baseline", summary="Timeout")])]:
            fixture = result()
            fixture[key] = value
            fixtures.append(fixture)
        for fixture in fixtures:
            with self.subTest(fixture=fixture):
                self.assertNotEqual(self.run_gate(fixture).returncode, 0)

    def test_list_preserves_exit_status_without_results(self):
        for status in (0, 1, 2, 3, 4):
            with self.subTest(status=status):
                self.assertEqual(self.run_gate(None, status, list_only=True).returncode, status)


if __name__ == "__main__":
    unittest.main()
