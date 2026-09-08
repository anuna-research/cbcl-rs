#!/usr/bin/env bash
# Run cargo-mutants against CBCL critical-path modules.
#
# Usage:
#   ./scripts/run-mutation-tests.sh          # full run
#   ./scripts/run-mutation-tests.sh --list   # list mutants only (dry run)

set -euo pipefail

KILL_RATE_THRESHOLD=90
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

# ---------- pre-flight ---------

if ! command -v cargo-mutants &>/dev/null; then
    echo "ERROR: cargo-mutants is not installed."
    echo ""
    echo "Install it with:"
    echo "  cargo install cargo-mutants"
    echo ""
    echo "Or via cargo-binstall:"
    echo "  cargo binstall cargo-mutants"
    exit 1
fi

command -v python3 >/dev/null || { echo "ERROR: python3 is required to read mutation results." >&2; exit 1; }

# ---------- build arguments ----------

CRITICAL_FILES=(
    "crates/cbcl-parser/src/parser.rs"
    "crates/cbcl-parser/src/message_parser.rs"
    "crates/cbcl-core/src/r1.rs"
    "crates/cbcl-core/src/r3.rs"
    "crates/cbcl-core/src/template.rs"
    "crates/cbcl-core/src/msg_tag.rs"
    "crates/cbcl-core/src/evaluator.rs"
    "crates/cbcl-core/src/role.rs"
    "crates/cbcl-core/src/r6.rs"
    "crates/cbcl-core/src/projection.rs"
)

FILE_FLAGS=()
for f in "${CRITICAL_FILES[@]}"; do
    FILE_FLAGS+=(--file "$f")
done

EXTRA_ARGS=()
if [[ "${1:-}" == "--list" ]]; then
    EXTRA_ARGS+=(--list)
fi

# ---------- run cargo-mutants ----------

echo "=== CBCL Mutation Testing ==="
echo "Targeting packages: cbcl-core, cbcl-parser"
echo "Critical-path modules: ${#CRITICAL_FILES[@]} files"
echo ""

# A fresh directory prevents a failed run from reusing an earlier result.
# Retain artifacts for inspection; cargo-mutants puts its own logs here too.
MUTATION_OUTPUT=$(mktemp -d "${TMPDIR:-/tmp}/cbcl-mutants.XXXXXX")
echo "Mutation artifacts: $MUTATION_OUTPUT/mutants.out"
MUTATION_STATUS=0
cargo mutants \
    --in-place \
    --output "$MUTATION_OUTPUT" \
    --package cbcl-core \
    --package cbcl-parser \
    "${FILE_FLAGS[@]}" \
    "${EXTRA_ARGS[@]}" || MUTATION_STATUS=$?

# If we only listed mutants, exit early.
if [[ "${1:-}" == "--list" ]]; then
    exit "$MUTATION_STATUS"
fi

# 2 = missed mutants; 3 = mutant timeouts. Both are scored by our policy.
# All other failures (including baseline failure, interrupts and tool errors)
# must remain failures, regardless of any partial output.
case "$MUTATION_STATUS" in
    0|2|3) ;;
    *) echo "FAIL: cargo-mutants exited with status $MUTATION_STATUS." >&2
       exit "$MUTATION_STATUS" ;;
esac

python3 "$SCRIPT_DIR/check-mutation-results.py" \
    "$MUTATION_OUTPUT/mutants.out" "$KILL_RATE_THRESHOLD"
