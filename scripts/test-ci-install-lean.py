#!/usr/bin/env python3
"""Exercise Lean bootstrap retries offline, including elan's internal download."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]

COUNTER = '''
count=0
[ ! -f "$CI_LEAN_TEST_DIR/{name}" ] || count=$(cat "$CI_LEAN_TEST_DIR/{name}")
count=$((count + 1))
printf '%s' "$count" > "$CI_LEAN_TEST_DIR/{name}"
'''


class BootstrapTests(unittest.TestCase):
    def run_bootstrap(self, download=0, installer=0, toolchain=0, existing=False):
        with tempfile.TemporaryDirectory(prefix="cbcl-lean-bootstrap-") as directory:
            root = Path(directory)
            fake_bin = root / "bin"
            fake_bin.mkdir()
            home = root / "elan"
            home.joinpath("bin").mkdir(parents=True)

            def executable(path, source):
                path.write_text(source)
                path.chmod(0o755)

            stub = root / "elan-stub"
            executable(stub, '#!/usr/bin/env bash\nset -eu\n'
                       'if [[ "$1 $2" == "toolchain install" ]]; then\n'
                       + COUNTER.format(name="toolchain")
                       + '  if (( count <= CI_LEAN_TEST_TOOLCHAIN_FAILURES )); then exit 1; fi\n'
                       'elif [[ "$1" == "run" ]]; then\n'
                       '  printf "%s\\n" "$2" >> "$CI_LEAN_TEST_DIR/versions"\n'
                       'fi\n')
            bootstrap = root / "installer-script"
            executable(bootstrap, '#!/bin/sh\nset -eu\n'
                       + COUNTER.format(name="installer")
                       + 'if [ "$count" -le "$CI_LEAN_TEST_INSTALLER_FAILURES" ]; then\n'
                       '  echo "curl: (22) The requested URL returned error: 504" >&2\n'
                       '  exit 1\nfi\n'
                       'cp "$CI_LEAN_TEST_STUB" "$ELAN_HOME/bin/elan"\n')
            executable(fake_bin / "curl", '#!/bin/sh\nset -eu\n'
                       + COUNTER.format(name="download")
                       + 'if [ "$count" -le "$CI_LEAN_TEST_DOWNLOAD_FAILURES" ]; then exit 22; fi\n'
                       'output=""\nwhile [ "$#" -gt 0 ]; do\n'
                       '  if [ "$1" = "-o" ]; then shift; output="$1"; fi\n'
                       '  shift\ndone\ncp "$CI_LEAN_TEST_INSTALLER" "$output"\n')
            executable(fake_bin / "sleep", '#!/bin/sh\nexit 0\n')
            if existing:
                executable(home / "bin/elan", stub.read_text())
            path_file = root / "github-path"
            env = dict(os.environ, PATH=f"{fake_bin}:{os.environ['PATH']}", ELAN_HOME=str(home),
                       GITHUB_PATH=str(path_file), CI_LEAN_TEST_DIR=str(root),
                       CI_LEAN_TEST_STUB=str(stub), CI_LEAN_TEST_INSTALLER=str(bootstrap),
                       CI_LEAN_TEST_DOWNLOAD_FAILURES=str(download),
                       CI_LEAN_TEST_INSTALLER_FAILURES=str(installer),
                       CI_LEAN_TEST_TOOLCHAIN_FAILURES=str(toolchain))
            result = subprocess.run(["bash", str(ROOT / "scripts/ci-install-lean.sh")],
                                    env=env, text=True, capture_output=True, timeout=10)
            counts = {name: int((root / name).read_text()) if (root / name).exists() else 0
                      for name in ["download", "installer", "toolchain"]}
            paths = path_file.read_text().splitlines() if path_file.exists() else []
            versions = (root / "versions").read_text().splitlines() if (root / "versions").exists() else []
            return result, counts, paths == [str(home / "bin")], versions

    def test_retries_download_internal_504_and_toolchain(self):
        result, counts, exported, versions = self.run_bootstrap(download=2, installer=2, toolchain=2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(counts, dict(download=3, installer=3, toolchain=3))
        self.assertTrue(exported)
        self.assertEqual(versions, [ROOT.joinpath("lean-cbcl/lean-toolchain").read_text().strip()] * 2)

    def test_permanent_initial_download_failure_stays_fatal(self):
        result, counts, _, _ = self.run_bootstrap(download=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(counts, dict(download=5, installer=0, toolchain=0))
        self.assertIn("FAIL: elan installer download after 5 attempts", result.stderr)

    def test_permanent_installer_failure_stays_fatal(self):
        result, counts, _, _ = self.run_bootstrap(installer=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(counts, dict(download=1, installer=5, toolchain=0))
        self.assertIn("FAIL: elan installation after 5 attempts", result.stderr)

    def test_permanent_toolchain_failure_stays_fatal(self):
        result, counts, _, _ = self.run_bootstrap(toolchain=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(counts, dict(download=1, installer=1, toolchain=5))

    def test_existing_elan_skips_bootstrap_download(self):
        result, counts, exported, _ = self.run_bootstrap(existing=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(counts, dict(download=0, installer=0, toolchain=1))
        self.assertTrue(exported)


if __name__ == "__main__":
    unittest.main()
