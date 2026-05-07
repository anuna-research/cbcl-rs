#!/usr/bin/env bash
# Demo 3 N=100 parallel re-run, 2026-05-07.
#
# Replaces the 2026-05-05 sweep cells that died from quota cascades. All
# Codex cells re-run (wire format changed: Codex-proxy/Responses API ->
# OpenAI-direct/Chat Completions, gpt-5.5; temperature defaults to 1
# because gpt-5.5 rejects temperature=0). Haiku only the five broken
# cells re-run; the five working cells keep their 2026-05-05 transcripts.
#
# Each cell is fanned out 4x at the trial level: --n 25 --trial-start
# {0,25,50,75} per process. With 15 cells that's 60 parallel processes;
# tier-4 OpenAI (4M TPM, 10k RPM) and a topped-up OpenRouter handle the
# load comfortably.
#
# Usage: ./run_n100_parallel_2026_05_07.sh

set -u
set -o pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

N_TOTAL=100
SHARDS=4                   # 4 sub-runs per cell
N_PER_SHARD=$((N_TOTAL / SHARDS))   # = 25
DATE_TAG="2026-05-07"
ARCHIVE_BASE="crates/cbcl-arena/measurements"
TRANSCRIPTS="crates/cbcl-arena/transcripts"

CODEX_DIR="$ARCHIVE_BASE/N100-codex-$DATE_TAG"
HAIKU_DIR="$ARCHIVE_BASE/N100-haiku-$DATE_TAG"
mkdir -p "$CODEX_DIR" "$HAIKU_DIR"

MASTER_LOG="$ARCHIVE_BASE/N100-parallel-$DATE_TAG.master.log"
{
  echo "Demo 3 parallel re-run"
  echo "Date:       $DATE_TAG"
  echo "N per cell: $N_TOTAL ($SHARDS shards x $N_PER_SHARD)"
  echo "Repo HEAD:  $(git rev-parse --short HEAD)  ($(git rev-parse --abbrev-ref HEAD))"
  echo "Started:    $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo
} | tee "$MASTER_LOG"

# ---------------------------------------------------------------------------
# 1. Cleanup transcripts for cells we are re-running (append-mode writer
#    would otherwise stack new turns onto stale lines). Preserve the five
#    Haiku N=100 cells that landed cleanly on 2026-05-05.
# ---------------------------------------------------------------------------
echo "== Cleanup ==" | tee -a "$MASTER_LOG"

codex_removed=$(find "$TRANSCRIPTS" -maxdepth 1 -name 'gpt55-*.jsonl' | wc -l | tr -d ' ')
find "$TRANSCRIPTS" -maxdepth 1 -name 'gpt55-*.jsonl' -delete
echo "  removed $codex_removed gpt55-*.jsonl files (full Codex re-run)" | tee -a "$MASTER_LOG"

haiku_targets=(
  'hk45-cooperative'
  'hk45-free'
  'hk45-yao-disciplined'
  'hk45-yao-cooperative'
  'hk45-yao-free'
)
haiku_removed=0
for prefix in "${haiku_targets[@]}"; do
  c=$(find "$TRANSCRIPTS" -maxdepth 1 -name "${prefix}-*.jsonl" | wc -l | tr -d ' ')
  find "$TRANSCRIPTS" -maxdepth 1 -name "${prefix}-*.jsonl" -delete
  haiku_removed=$((haiku_removed + c))
done
echo "  removed $haiku_removed hk45 broken-cell files (preserved working hk45 cells)" | tee -a "$MASTER_LOG"
echo | tee -a "$MASTER_LOG"

# ---------------------------------------------------------------------------
# 2. Pre-build release binaries so parallel cargo invocations don't compete.
# ---------------------------------------------------------------------------
echo "== Pre-build ==" | tee -a "$MASTER_LOG"
build_start=$(date +%s)
if cargo build --release --quiet -p cbcl-arena --example glm_psi --example glm_yao 2>&1 | tee -a "$MASTER_LOG"; then
  echo "  build OK in $(( $(date +%s) - build_start ))s" | tee -a "$MASTER_LOG"
else
  echo "  BUILD FAILED, aborting" | tee -a "$MASTER_LOG"
  exit 1
fi
echo | tee -a "$MASTER_LOG"

# ---------------------------------------------------------------------------
# 3. Launch every (cell, shard) pair as an independent background job.
#    Each job writes to its own log file under the provider's archive
#    dir; transcripts go to crates/cbcl-arena/transcripts/.
# ---------------------------------------------------------------------------
echo "== Launch ==" | tee -a "$MASTER_LOG"

declare -a JOBS JOB_PIDS JOB_LOGS

launch_shard() {
  local backend="$1" demo="$2" cell="$3" archive_dir="$4" shard_idx="$5"
  local example="glm_${demo}"
  local bin="target/release/examples/${example}"
  local trial_start=$((shard_idx * N_PER_SHARD))
  local log="${archive_dir}/cell-${demo}-${cell}-shard${shard_idx}.log"
  # Invoke the prebuilt binary directly so parallel processes don't race
  # on Cargo metadata (60 simultaneous `cargo run` invocations can lock
  # contention on target/.cargo-lock and target/.rustc_info.json).
  ( "$bin" \
        --backend "$backend" --cell "$cell" \
        --n "$N_PER_SHARD" --trial-start "$trial_start" \
        > "$log" 2>&1 ) &
  local pid=$!
  JOBS+=("$backend $demo $cell shard$shard_idx")
  JOB_PIDS+=("$pid")
  JOB_LOGS+=("$log")
}

launch_cell() {
  local backend="$1" demo="$2" cell="$3" archive_dir="$4"
  local s
  for ((s = 0; s < SHARDS; s++)); do
    launch_shard "$backend" "$demo" "$cell" "$archive_dir" "$s"
  done
}

# --- Codex: all 10 cells, 4 shards each (40 processes) ---
for cell in free disciplined cooperative native native-attacker; do
  launch_cell codex psi  "$cell" "$CODEX_DIR"
  launch_cell codex yao  "$cell" "$CODEX_DIR"
done

# --- Haiku: 5 broken cells, 4 shards each (20 processes) ---
launch_cell haiku psi  free          "$HAIKU_DIR"
launch_cell haiku psi  cooperative   "$HAIKU_DIR"
launch_cell haiku yao  free          "$HAIKU_DIR"
launch_cell haiku yao  disciplined   "$HAIKU_DIR"
launch_cell haiku yao  cooperative   "$HAIKU_DIR"

echo "  launched ${#JOB_PIDS[@]} background processes" | tee -a "$MASTER_LOG"
echo | tee -a "$MASTER_LOG"

# ---------------------------------------------------------------------------
# 4. Wait for all jobs and report.
# ---------------------------------------------------------------------------
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
  echo "Codex archive: $CODEX_DIR"
  echo "Haiku archive: $HAIKU_DIR"
  echo "Master log:    $MASTER_LOG"
  echo
  echo "Per-cell aggregates can be recomputed from transcripts:"
  echo "  ls $TRANSCRIPTS/{gpt55,hk45}-*.jsonl"
} | tee -a "$MASTER_LOG"

if [ "$failed" -gt 0 ]; then
  exit 1
fi
