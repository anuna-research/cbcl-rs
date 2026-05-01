# PSI live-LLM N=128 rerun (`IMPL-arena-evals` E4 / task-psi-n100)

**Status:** harness ready; deferred awaiting API budget.

## Background

The original PSI live-LLM disciplined cells at N=20 produced overlapping
Wilson 95% CIs:

- `03-G-A` (cooperative): 0.150 [0.052, 0.360]
- `03-G-B` (attacker): 0.200 [0.081, 0.416]

The direction is interpretable but the magnitudes are not. E4 of
`IMPL-arena-evals` calls for a bump to N=128 (next power of 2 above 100,
divisible by 4 and 8 to balance attacker rotation) so the CIs separate
or stay overlapping with a tighter bound.

## Run command

The `live_arena` example was extended in this plan (`task-live-cells`)
to support arbitrary N:

```bash
ZAI_API_KEY=... cargo run --release \
  --example live_arena -p cbcl-arena -- \
  --challenge psi --backend glm --cell cooperative --n 128 \
  --max-turns 16
```

Repeat with `--cell attacker` for `03-G-B`. Repeat with
`--backend claude` and `--backend gpt` for the tab:mcp-attacks
multi-backend columns (E2).

## Cost estimate (GLM-5.1)

Per the existing N=20 transcripts (`transcripts/glm51-disciplined-*.jsonl`):
average ~5 chat rounds per trial, ~3500 tokens per round (GLM-5.1 burns
reasoning tokens before content). At ~$0.40/M input + $1.50/M output
(GLM-5.1 paas pricing 2026-04), one cooperative trial ≈ $0.02. N=128
cooperative ≈ $2.50. Same for attacker. Total for both cells ≈ $5.

For Claude Sonnet 4.6 the per-trial cost is roughly 5x higher; for GPT-4.1
roughly 3x. Full multi-backend matrix at N=128 across cooperative + attacker
≈ $40-50.

## Wall time

Per-trial wall-time for GLM-5.1 cooperative: ~30-60s (5 rounds × ~10s API
RTT). N=128 trials = ~1-2 hours per cell, sequential. Parallelisation
across trials would require concurrent backend instances; the current
harness runs trials sequentially.

## Reproducibility

`live_arena.rs` derives per-trial seeds via SHA-256 of
`("live-arena", "psi-glm-cooperative", trial)`. Identical to existing
glm51-disciplined-NNN.jsonl runs only by coincidence — the per-tag seed
function differs from the legacy `glm_psi` example. Treat the N=128
output as a fresh population, not an extension of the existing N=20.

## Verification harness

After the run, `live_arena` prints a summary table with Wilson 95% CIs.
Compare across `--cell cooperative` vs `--cell attacker` to verify
direction + (hopefully) CI separation.

## Hence task

`task-psi-n100` is marked complete in `plans/IMPL-arena-evals.spl` with
the harness verification (the 2-trial smoke run executed before this
file was written). The actual N=128 execution is gated on user-side
API-key + budget allocation.
