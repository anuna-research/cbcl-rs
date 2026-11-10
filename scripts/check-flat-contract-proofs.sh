#!/usr/bin/env bash
# SPEC-041 reproducible proof audit and independent Rust/Lean agreement check.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_TOOLCHAIN="$(cat lean-cbcl/lean-toolchain)"
if rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
    lean-cbcl/LeanCbcl/FlatContracts lean-cbcl/FlatContracts{Oracle,Audit}.lean; then
  echo 'Unchecked proof placeholder or axiom in flat-contract model' >&2
  exit 1
fi
lake -d lean-cbcl build cbcl-flat-contract-oracle
lake -d lean-cbcl env lean lean-cbcl/FlatContractsAudit.lean
cargo test -p cbcl-parser --test flat_contracts_lean -- --ignored --nocapture
cargo test -p cbcl-parser --test flat_contracts
