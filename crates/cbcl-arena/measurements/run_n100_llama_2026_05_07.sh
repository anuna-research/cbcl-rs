#!/usr/bin/env bash
# Llama 4 Maverick (Meta) N=100 sweep, 2026-05-07.
#
# Adds a fourth provider to the Demo 3 evaluation slate. Runs all 10
# cells (5 PSI + 5 Yao) at N=100, 4 shards per cell = 40 parallel
# processes. Routes through OpenRouter at deepseek/meta-llama/llama-4-maverick.
#
# Usage: ./run_n100_deepseek_2026_05_07.sh

set -u
set -o pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

N_TOTAL=100
SHARDS=4
N_PER_SHARD=$((N_TOTAL / SHARDS))
DATE_TAG="2026-05-07"
ARCHIVE="crates/cbcl-arena/measurements/N100-llama-$DATE_TAG"
TRANSCRIPTS="crates/cbcl-arena/transcripts"

mkdir -p "$ARCHIVE"
MASTER_LOG="$ARCHIVE/master.log"
{
  echo "Llama 4 Maverick (Meta) N=100 sweep"
  echo "Date:       $DATE_TAG"
  echo "N per cell: $N_TOTAL ($SHARDS shards x $N_PER_SHARD)"
  echo "Repo HEAD:  $(git rev-parse --short HEAD)  ($(git rev-parse --abbrev-ref HEAD))"
  echo "Started:    $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo
} | tee "$MASTER_LOG"

echo "== Cleanup ==" | tee -a "$MASTER_LOG"
removed=$(find "$TRANSCRIPTS" -maxdepth 1 -name 'lm4m-*.jsonl' | wc -l | tr -d ' ')
find "$TRANSCRIPTS" -maxdepth 1 -name 'lm4m-*.jsonl' -delete
echo "  removed $removed lm4m-*.jsonl files (smoke contamination)" | tee -a "$MASTER_LOG"
echo | tee -a "$MASTER_LOG"

echo "== Pre-build ==" | tee -a "$MASTER_LOG"
build_start=$(date +%s)
if cargo build --release --quiet -p cbcl-arena --example glm_psi --example glm_yao 2>&1 | tee -a "$MASTER_LOG"; then
  echo "  build OK in $(( $(date +%s) - build_start ))s" | tee -a "$MASTER_LOG"
else
  echo "  BUILD FAILED, aborting" | tee -a "$MASTER_LOG"
  exit 1
fi
echo | tee -a "$MASTER_LOG"

echo "== Launch ==" | tee -a "$MASTER_LOG"

declare -a JOBS JOB_PIDS JOB_LOGS

launch_shard() {
  local demo="$1" cell="$2" shard_idx="$3"
  local example="glm_${demo}"
  local bin="target/release/examples/${example}"
  local trial_start=$((shard_idx * N_PER_SHARD))
  local log="${ARCHIVE}/cell-${demo}-${cell}-shard${shard_idx}.log"
  ( "$bin" \
        --backend llama --cell "$cell" \
        --n "$N_PER_SHARD" --trial-start "$trial_start" \
        > "$log" 2>&1 ) &
  local pid=$!
  JOBS+=("deepseek $demo $cell shard$shard_idx")
  JOB_PIDS+=("$pid")
  JOB_LOGS+=("$log")
}

launch_cell() {
  local demo="$1" cell="$2"
  local s
  for ((s = 0; s < SHARDS; s++)); do
    launch_shard "$demo" "$cell" "$s"
  done
}

for cell in free disciplined cooperative native native-attacker; do
  launch_cell psi "$cell"
  launch_cell yao "$cell"
done

echo "  launched ${#JOB_PIDS[@]} background processes" | tee -a "$MASTER_LOG"
echo | tee -a "$MASTER_LOG"

echo "== Waiting for completion ==" | tee -a "$MASTER_LOG"
sweep_start=$(date +%s)

failed=0
for i in "${!JOB_PIDS[@]}"; do
  pid="${JOB_PIDS[$i]}"
  job="${JOBS[$i]}"
  log="${JOB_LOGS[$i]}"
  if wait "$pid"; then
    rc=0
  else
    rc=$?
  fi
  elapsed=$(( $(date +%s) - sweep_start ))
  if [ "$rc" -eq 0 ]; then
    wall=$(grep -E 'Wall-time' "$log" | tail -1 | sed 's/.*Wall-time: //')
    echo "  [DONE  +${elapsed}s] $job  wall=$wall" | tee -a "$MASTER_LOG"
  else
    echo "  [FAIL  +${elapsed}s rc=$rc] $job  log=$log" | tee -a "$MASTER_LOG"
    failed=$((failed + 1))
  fi
done

total=$(( $(date +%s) - sweep_start ))
{
  echo
  echo "Sweep complete in ${total}s ($((total/60))m $((total%60))s); $failed shards failed"
  echo "Archive:   $ARCHIVE"
  echo "Master log: $MASTER_LOG"
} | tee -a "$MASTER_LOG"

if [ "$failed" -gt 0 ]; then
  exit 1
fi
