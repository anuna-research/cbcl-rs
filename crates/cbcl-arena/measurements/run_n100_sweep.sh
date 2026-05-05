#!/usr/bin/env bash
# Demo 3 (PSI + Yao) live-LLM N=100 sweep, single provider.
# Implements Aaron's Q1 (2026-05-05): lift Demo 3 from N=20 to N=100.
#
# Usage:
#   ./run_n100_sweep.sh <backend>
# Where <backend> is one of: glm | codex | haiku
#
# Cells run in priority order so partial-completion still ships the headline
# rows. Outputs:
#   measurements/N100-<provider>-2026-05-05/run.log       (combined log)
#   measurements/N100-<provider>-2026-05-05/cell-<n>-<cell>.log  (per-cell)
#   crates/cbcl-arena/transcripts/<provider>-<cell>-NNN.jsonl    (raw)

set -u
set -o pipefail

BACKEND="${1:-}"
if [[ -z "$BACKEND" ]]; then
    echo "usage: $0 <backend>  (one of: glm | codex | haiku)" >&2
    exit 2
fi

case "$BACKEND" in
    glm)   PROVIDER_TAG="glm"   ;;
    codex) PROVIDER_TAG="codex" ;;
    haiku) PROVIDER_TAG="haiku" ;;
    *)     echo "unknown backend: $BACKEND" >&2 ; exit 2 ;;
esac

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

ARCHIVE_DIR="crates/cbcl-arena/measurements/N100-${PROVIDER_TAG}-2026-05-05"
mkdir -p "$ARCHIVE_DIR"
RUN_LOG="$ARCHIVE_DIR/run.log"

N=100

# Cells in priority order. Format: "<demo>:<cell>".
# demo ∈ {psi, yao}; cell is the harness --cell argument.
CELLS=(
    "psi:native"               # P1 — headline puzzle
    "psi:native-attacker"      # P2 — symmetry argument for native leak=0
    "yao:native"               # P3 — salt-leak post-fix (Aaron Q4)
    "yao:native-attacker"      # P4 — symmetry
    "psi:disciplined"          # P5 — disciplined × attacker
    "psi:cooperative"          # P6 — disciplined × cooperative
    "psi:free"                 # P7 — free-chat × attacker
    "yao:disciplined"          # P8
    "yao:cooperative"          # P9
    "yao:free"                 # P10
)

echo "Demo 3 N=100 sweep" | tee -a "$RUN_LOG"
echo "Backend:    $BACKEND" | tee -a "$RUN_LOG"
echo "Started:    $(date -u +%Y-%m-%dT%H:%M:%SZ)" | tee -a "$RUN_LOG"
echo "Cells:      ${#CELLS[@]} cells × N=$N" | tee -a "$RUN_LOG"
echo "Repo HEAD:  $(git rev-parse --short HEAD)  ($(git rev-parse --abbrev-ref HEAD))" | tee -a "$RUN_LOG"
echo "" | tee -a "$RUN_LOG"

SWEEP_START=$(date +%s)
SUCCEEDED=0
FAILED=0
FAILED_CELLS=""

for i in "${!CELLS[@]}"; do
    SPEC="${CELLS[$i]}"
    DEMO="${SPEC%%:*}"
    CELL="${SPEC##*:}"
    POS=$((i + 1))

    EXAMPLE="glm_${DEMO}"
    CELL_LOG="$ARCHIVE_DIR/cell-${POS}-${DEMO}-${CELL}.log"

    echo "[$POS/${#CELLS[@]}] $DEMO $CELL — backend $BACKEND, N=$N" | tee -a "$RUN_LOG"
    echo "    log: $CELL_LOG" | tee -a "$RUN_LOG"

    CELL_START=$(date +%s)
    if cargo run --release --quiet -p cbcl-arena --example "$EXAMPLE" -- \
            --backend "$BACKEND" --cell "$CELL" --n "$N" \
            >"$CELL_LOG" 2>&1
    then
        CELL_END=$(date +%s)
        CELL_SECS=$((CELL_END - CELL_START))
        echo "    OK  ($CELL_SECS s)" | tee -a "$RUN_LOG"
        SUCCEEDED=$((SUCCEEDED + 1))
    else
        CELL_END=$(date +%s)
        CELL_SECS=$((CELL_END - CELL_START))
        echo "    FAIL ($CELL_SECS s) — see $CELL_LOG" | tee -a "$RUN_LOG"
        FAILED=$((FAILED + 1))
        FAILED_CELLS="$FAILED_CELLS $DEMO/$CELL"
    fi
    echo "" | tee -a "$RUN_LOG"
done

SWEEP_END=$(date +%s)
TOTAL_SECS=$((SWEEP_END - SWEEP_START))

echo "Sweep finished: $(date -u +%Y-%m-%dT%H:%M:%SZ)" | tee -a "$RUN_LOG"
echo "Total wall-time: $TOTAL_SECS s ($((TOTAL_SECS / 60)) min)" | tee -a "$RUN_LOG"
echo "Succeeded: $SUCCEEDED / ${#CELLS[@]}" | tee -a "$RUN_LOG"
echo "Failed:    $FAILED${FAILED_CELLS:+ —$FAILED_CELLS}" | tee -a "$RUN_LOG"

if [[ $FAILED -gt 0 ]]; then
    exit 1
fi
exit 0
