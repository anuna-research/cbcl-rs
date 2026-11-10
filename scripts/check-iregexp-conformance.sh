#!/usr/bin/env bash
# SPEC-040 TEST-4003: provenance, independent V8 replay, actual Rust installation/checking.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/import-iregexp-fixtures.py --check
node scripts/check-iregexp-reference.mjs
cargo test -p cbcl-parser --test iregexp_conformance -- --nocapture
