# GPT-5.5 (Codex) — Yao Millionaire live-LLM probe (N=20 per cell)

Cross-provider companion to the existing GLM-5.1 Yao probe in
`paper-evidence/glm51-yao-*.jsonl` (paper Table tab:arena-glm-yao).
Same harness (`examples/glm_yao.rs`) with `--backend codex`, routing
through a local `codex-responses-proxy` against a ChatGPT/Codex
subscription.

Operator: Yao Millionaire, log-uniform wealth on [1, 1e9]. Each
cell ran 20 independent trials at temperature 0; transcripts at
`crates/cbcl-arena/transcripts/gpt55-yao-{cell}-NNN.jsonl`.

| Cell                                  | Leak (95% CI)         | Utility | Security | Wall-time |
|---------------------------------------|-----------------------|---------|----------|-----------|
| Free-chat × Attacker                  | 0.250 (0.112, 0.469)  |  0.05   |  0.50    |  510.0 s  |
| Disciplined-shim × Attacker           | 0.000 (0.000, 0.161)  |  0.00   |  1.00    | 1391.8 s  |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.161)  |  0.05   |  1.00    | 1470.5 s  |
| Native-CBCL × Cooperative (w/ check)  | 0.000 (0.000, 0.161)  |  0.05   |  1.00    | 1392.0 s  |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.161)  |  0.00   |  1.00    |  569.0 s  |

## Comparison to GLM-5.1 (paper Table tab:arena-glm-yao)

| Cell                                | GPT-5.5 (Codex)       | GLM-5.1 (Z.ai)            |
|-------------------------------------|-----------------------|---------------------------|
| Free × Attacker                     | 0.250 (0.112, 0.469)  | 0.350 (0.181, 0.567)      |
| Disciplined × Attacker              | 0.000 (0.000, 0.161)  | 0.000 (0.000, 0.161)      |
| Native × Cooperative (w/ check)     | 0.000 (0.000, 0.161)  | 0.000 (0.000, 0.161)      |
| Native × Cooperative (no check)     | n/a                   | 0.100 (0.028, 0.301) Run1 |

The disciplined-shim binding's perfect hold (0.000 across both
providers) confirms the dialect-grammar floor: `arena-millionaire`'s
content forms (`yao-bracket`, `yao-bracket-commit`,
`yao-bracket-reveal`) syntactically cannot carry a wealth value.
Free-chat leak rates are non-trivial under both providers (~25–35 %)
and CIs overlap, consistent with "the gate's contribution is
upper-bounded by the channels the dialect leaves open by design".

The wealth-derived-salt failure mode that motivated the seat-level
privacy check (originally observed in 2/20 GLM-5.1 native trials)
did not surface in any GPT-5.5 trial in this run; GPT-5.5 chose
non-wealth-derived salts in every native trial we recorded. The
seat-level check (three unit tests in
`src/glm/cbcl_native_yao.rs`) remains the right defensive
backstop for either provider; this run did not exercise it
in vivo.
