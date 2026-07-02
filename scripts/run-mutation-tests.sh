#!/usr/bin/env bash
# Run cargo-mutants against CBCL critical-path modules.
#
# Usage:
#   ./scripts/run-mutation-tests.sh          # full run
#   ./scripts/run-mutation-tests.sh --list   # list mutants only (dry run)

set -euo pipefail

KILL_RATE_THRESHOLD=90

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

cargo mutants \
    --in-place \
    --package cbcl-core \
    --package cbcl-parser \
    "${FILE_FLAGS[@]}" \
    "${EXTRA_ARGS[@]}" \
    2>&1 | tee /tmp/cbcl-mutants-output.txt

# If we only listed mutants, exit early.
if [[ "${1:-}" == "--list" ]]; then
    exit 0
fi

# ---------- parse results ----------

OUTPUT=/tmp/cbcl-mutants-output.txt

CAUGHT=$(grep -cE '(CAUGHT|caught)' "$OUTPUT" 2>/dev/null || echo 0)
MISSED=$(grep -cE '(MISSED|missed)' "$OUTPUT" 2>/dev/null || echo 0)
TIMEOUT=$(grep -cE '(TIMEOUT|timeout)' "$OUTPUT" 2>/dev/null || echo 0)
UNVIABLE=$(grep -cE '(UNVIABLE|unviable)' "$OUTPUT" 2>/dev/null || echo 0)

TOTAL=$((CAUGHT + MISSED + TIMEOUT))

if [[ "$TOTAL" -eq 0 ]]; then
    echo ""
    echo "WARNING: No mutants were generated or results could not be parsed."
    echo "Check the output above for details."
    exit 1
fi

# Timeouts count as caught (the test suite did detect the mutant).
KILLED=$((CAUGHT + TIMEOUT))
KILL_RATE=$(( (KILLED * 100) / TOTAL ))

echo ""
echo "=== Mutation Testing Results ==="
echo "  Caught:   $CAUGHT"
echo "  Timeout:  $TIMEOUT"
echo "  Missed:   $MISSED"
echo "  Unviable: $UNVIABLE"
echo "  Total:    $TOTAL"
echo "  Kill rate: ${KILL_RATE}%  (threshold: ${KILL_RATE_THRESHOLD}%)"
echo ""

if [[ "$KILL_RATE" -lt "$KILL_RATE_THRESHOLD" ]]; then
    echo "FAIL: Kill rate ${KILL_RATE}% is below the ${KILL_RATE_THRESHOLD}% threshold."
    echo "Review missed mutants in mutants.out/ to identify gaps in test coverage."
    exit 1
else
    echo "PASS: Kill rate ${KILL_RATE}% meets the ${KILL_RATE_THRESHOLD}% threshold."
    exit 0
fi
