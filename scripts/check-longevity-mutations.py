#!/usr/bin/env python3
"""SPEC-043 TEST-4308/4309: require executed tests to catch unsafe mutations.

Run without concurrent Cargo builds. Each source is restored in finally, and a
passing clean rebuild is required after mutation. Compilation failures aren't kills.
"""
from pathlib import Path
import os
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMMAND = ["cargo", "test", "--locked", "-p", "cbcl-core", "--test", "longevity"]
MUTATIONS = [
    ("public-key-length", "multikey.rs", "bytes.len() != codec.public_key_size()", "false", "codec_roundtrips_are_typed_and_bounded"),
    ("signing-codec", "keyid.rs", "key.codec() != crate::multikey::PublicKeyCodec::Ed25519", "false", "explicit_multikey_constructor_preserves_existing_principals"),
    ("depth-overflow", "r2.rs", "self.current_depth.checked_add(1)?", "self.current_depth.wrapping_add(1)", "resource_overflow_refuses_without_panicking"),
    ("expansion-overflow", "r2.rs", "self.expansion_size.checked_add(size)?", "self.expansion_size.wrapping_add(size)", "resource_overflow_refuses_without_panicking"),
]


def run(extra=()):
    env = os.environ.copy()
    env.setdefault("CARGO_INCREMENTAL", "0")
    env.setdefault("CARGO_PROFILE_DEV_DEBUG", "0")
    env.setdefault("CARGO_PROFILE_TEST_DEBUG", "0")
    return subprocess.run(COMMAND + list(extra), cwd=ROOT, env=env,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    baseline = run()
    if baseline.returncode:
        raise RuntimeError(f"clean baseline failed:\n{baseline.stdout}")
    for label, filename, old, new, test in MUTATIONS:
        source = ROOT / "crates/cbcl-core/src" / filename
        original = source.read_bytes()
        text = original.decode()
        if text.count(old) != 1:
            raise RuntimeError(f"{label}: mutation site must be unique")
        try:
            source.write_text(text.replace(old, new, 1))
            result = run([test, "--", "--exact"])
            if (result.returncode == 0 or
                    f"test {test} ... FAILED" not in result.stdout or
                    "test result: FAILED." not in result.stdout):
                raise RuntimeError(f"{label}: no executed test killed mutant:\n{result.stdout}")
            print(f"{label}: killed", flush=True)
        finally:
            source.write_bytes(original)
    clean = run()
    if clean.returncode:
        raise RuntimeError(f"restored baseline failed:\n{clean.stdout}")
    print("restored baseline: passed", flush=True)


if __name__ == "__main__":
    main()
