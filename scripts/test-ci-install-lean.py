#!/usr/bin/env python3
"""Exercise Lean bootstrap retries offline, with pinned assets, checksum verification and API fallback."""
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
    def run_bootstrap(self, download=0, installer=0, toolchain=0, existing=False, cached=False, checksum=False, arch="x86_64", lean_download=0, lean_checksum=False, unpack=False):
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
                       '  touch "$CI_LEAN_TEST_DIR/ready"\n'
                       'elif [[ "$1 $2" == "toolchain link" ]]; then\n'
                       + COUNTER.format(name="link")
                       + '  [ -x "$4/bin/lean" ] && [ -x "$4/bin/lake" ]\n'
                       '  printf "%s\\n" "$4" > "$CI_LEAN_TEST_DIR/linked"\n'
                       '  touch "$CI_LEAN_TEST_DIR/ready"\n'
                       'elif [[ "$1" == "run" ]]; then\n'
                       '  [ -f "$CI_LEAN_TEST_DIR/ready" ] || exit 1\n'
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
                       + 'output=""\nurl=""\nwhile [ "$#" -gt 0 ]; do\n'
                       '  if [ "$1" = "-o" ]; then shift; output="$1"; fi\n'
                       '  printf "%s\\n" "$1" >> "$CI_LEAN_TEST_DIR/urls"\n'
                       '  url="$1"\n  shift\ndone\n'
                       'case "$url" in\n'
                       '  *leanprover/lean4/*)\n'
                       + COUNTER.format(name="lean-download")
                       + '    if [ "$count" -le "$CI_LEAN_TEST_LEAN_DOWNLOAD_FAILURES" ]; then exit 22; fi ;;\n'
                       '  *) if [ "$count" -le "$CI_LEAN_TEST_DOWNLOAD_FAILURES" ]; then exit 22; fi ;;\n'
                       'esac\ncp "$CI_LEAN_TEST_INSTALLER" "$output"\n')
            executable(fake_bin / "sleep", '#!/bin/sh\nexit 0\n')
            executable(fake_bin / 'uname', '#!/bin/sh\nif [ "$1" = -s ]; then echo Linux; else echo "$CI_LEAN_TEST_ARCH"; fi\n')
            executable(fake_bin / 'sha256sum', '#!/bin/sh\nread -r digest path\n'
                       'case "$path" in\n'
                       '  */lean.zip) exit "$CI_LEAN_TEST_LEAN_CHECKSUM" ;;\n'
                       '  *) exit "$CI_LEAN_TEST_CHECKSUM" ;;\nesac\n')
            executable(fake_bin / 'tar', '#!/bin/sh\ncp "$CI_LEAN_TEST_INSTALLER" "$4/elan-init"\n')
            executable(fake_bin / 'unzip', '#!/bin/sh\nset -eu\n'
                       + COUNTER.format(name="unpack")
                       + 'if [ "$CI_LEAN_TEST_UNPACK" = 1 ]; then exit 1; fi\n'
                       'platform=linux\n[ "$CI_LEAN_TEST_ARCH" != aarch64 ] || platform=linux_aarch64\n'
                       'mkdir -p "$4/lean-4.27.0-$platform/bin"\n'
                       'for name in lean lake; do\n'
                       '  cp "$CI_LEAN_TEST_STUB" "$4/lean-4.27.0-$platform/bin/$name"\ndone\n')
            if cached:
                (root / 'ready').touch()
            if existing:
                executable(home / "bin/elan", stub.read_text())
            path_file = root / "github-path"
            env = dict(os.environ, PATH=f"{fake_bin}:{os.environ['PATH']}", ELAN_HOME=str(home),
                       GITHUB_PATH=str(path_file), CI_LEAN_TEST_DIR=str(root),
                       CI_LEAN_TEST_STUB=str(stub), CI_LEAN_TEST_INSTALLER=str(bootstrap),
                       CI_LEAN_TEST_DOWNLOAD_FAILURES=str(download),
                       CI_LEAN_TEST_INSTALLER_FAILURES=str(installer),
                       CI_LEAN_TEST_TOOLCHAIN_FAILURES=str(toolchain), CI_LEAN_TEST_CHECKSUM=str(int(checksum)), CI_LEAN_TEST_ARCH=arch,
                       CI_LEAN_TEST_LEAN_DOWNLOAD_FAILURES=str(lean_download),
                       CI_LEAN_TEST_LEAN_CHECKSUM=str(int(lean_checksum)), CI_LEAN_TEST_UNPACK=str(int(unpack)))
            result = subprocess.run(["bash", str(ROOT / "scripts/ci-install-lean.sh")],
                                    env=env, text=True, capture_output=True, timeout=10)
            self.urls = (root / "urls").read_text() if (root / "urls").exists() else ""
            counts = {name: int((root / name).read_text()) if (root / name).exists() else 0
                      for name in ["download", "installer", "toolchain"]}
            self.fallback_counts = {name: int((root / name).read_text()) if (root / name).exists() else 0
                                    for name in ["lean-download", "unpack", "link"]}
            linked = root / "linked"
            self.link_survives = linked.exists() and Path(linked.read_text().strip()).is_dir()
            paths = path_file.read_text().splitlines() if path_file.exists() else []
            versions = (root / "versions").read_text().splitlines() if (root / "versions").exists() else []
            return result, counts, paths == [str(home / "bin")], versions

    def test_retries_download_internal_504_and_toolchain(self):
        result, counts, exported, versions = self.run_bootstrap(download=2, installer=2, toolchain=2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(counts, dict(download=3, installer=3, toolchain=3))
        self.assertIn("/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz", self.urls)
        self.assertNotIn("latest", self.urls)
        self.assertTrue(exported)
        self.assertEqual(versions, [ROOT.joinpath("lean-cbcl/lean-toolchain").read_text().strip()] * 2)

    def test_permanent_initial_download_failure_stays_fatal(self):
        result, counts, _, _ = self.run_bootstrap(download=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(counts, dict(download=10, installer=0, toolchain=0))
        self.assertIn("FAIL: pinned elan API asset download after 5 attempts", result.stderr)

    def test_permanent_installer_failure_stays_fatal(self):
        result, counts, _, _ = self.run_bootstrap(installer=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(counts, dict(download=1, installer=5, toolchain=0))
        self.assertIn("FAIL: elan installation after 5 attempts", result.stderr)

    def test_toolchain_release_failure_uses_verified_fallback(self):
        result, _, _, _ = self.run_bootstrap(toolchain=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("/lean4/releases/download/v4.27.0/lean-4.27.0-linux.zip", self.urls)
        self.assertEqual(self.fallback_counts, {"lean-download": 1, "unpack": 1, "link": 1})
        self.assertTrue(self.link_survives)

    def test_permanent_toolchain_failure_stays_fatal(self):
        result, counts, _, _ = self.run_bootstrap(toolchain=10, lean_download=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(counts, dict(download=11, installer=1, toolchain=5))
        self.assertEqual(self.fallback_counts, {"lean-download": 10, "unpack": 0, "link": 0})

    def test_toolchain_api_fallback_and_arm_asset(self):
        result, _, _, _ = self.run_bootstrap(toolchain=10, lean_download=5, arch="aarch64")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("/lean4/releases/assets/344780906", self.urls)
        self.assertEqual(self.fallback_counts, {"lean-download": 6, "unpack": 1, "link": 1})
        self.assertTrue(self.link_survives)

    def test_toolchain_checksum_failure_never_extracts_or_links(self):
        result, _, _, _ = self.run_bootstrap(toolchain=10, lean_checksum=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Lean archive checksum mismatch", result.stderr)
        self.assertEqual(self.fallback_counts, {"lean-download": 10, "unpack": 0, "link": 0})

    def test_toolchain_unpack_failure_never_links(self):
        result, _, _, _ = self.run_bootstrap(toolchain=10, unpack=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.fallback_counts, {"lean-download": 1, "unpack": 1, "link": 0})

    def test_existing_elan_skips_bootstrap_download(self):
        result, counts, exported, _ = self.run_bootstrap(existing=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(counts, dict(download=0, installer=0, toolchain=1))
        self.assertTrue(exported)

    def test_api_fallback_after_primary_endpoint_failure(self):
        result, counts, _, _ = self.run_bootstrap(download=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(counts, dict(download=6, installer=1, toolchain=1))
        self.assertIn("/releases/assets/529114798", self.urls)
        self.assertNotIn("latest", self.urls)

    def test_arm_asset_selection(self):
        result, _, _, _ = self.run_bootstrap(arch="aarch64", download=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("/releases/assets/529114794", self.urls)

    def test_checksum_failure_never_executes_installer(self):
        result, counts, _, _ = self.run_bootstrap(checksum=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(counts, dict(download=10, installer=0, toolchain=0))
        self.assertIn("checksum mismatch", result.stderr)

    def test_cached_toolchain_needs_no_download(self):
        result, counts, exported, _ = self.run_bootstrap(existing=True, cached=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(counts, dict(download=0, installer=0, toolchain=0))
        self.assertTrue(exported)


if __name__ == "__main__":
    unittest.main()
