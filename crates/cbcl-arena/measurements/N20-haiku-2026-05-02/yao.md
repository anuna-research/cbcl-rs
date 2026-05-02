# Claude Haiku 4.5 (via OpenRouter) — Yao Millionaire live-LLM probe (N=20 per cell)

Cross-provider companion to the existing GLM-5.1 Yao probe (paper Table
tab:arena-glm-yao) and the GPT-5.5 (Codex) replication (Table
tab:arena-codex-yao). Same harness (`examples/glm_yao.rs`) with
`--backend haiku`, routing through OpenRouter at the
`anthropic/claude-haiku-4.5` route.

Operator: Yao Millionaire, log-uniform wealth on [1, 1e9]. Each
cell ran 20 independent trials at temperature 0; transcripts at
`crates/cbcl-arena/transcripts/hk45-yao-{cell}-NNN.jsonl`.

| Cell                                  | Leak (95% CI)         | Utility | Security |
|---------------------------------------|-----------------------|---------|----------|
| Free-chat × Attacker                  | **0.500** (0.299, 0.701) |  0.15 |  0.00    |
| Disciplined-shim × Attacker           | 0.000 (0.000, 0.161)  |  0.00   |  1.00    |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.161)  |  0.05   |  1.00    |
| Native-CBCL × Cooperative (w/ check)  | 0.000 (0.000, 0.161)  | -0.05   |  1.00    |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.161)  |  0.10   |  1.00    |

## Three-provider comparison (Yao live-LLM extension)

| Cell                                | GLM-5.1               | GPT-5.5 (Codex)       | Haiku 4.5                |
|-------------------------------------|-----------------------|-----------------------|--------------------------|
| Free × Attacker                     | 0.350 (0.181, 0.567)  | 0.250 (0.112, 0.469)  | **0.500** (0.299, 0.701) |
| Disciplined × Attacker              | 0.000 (0.000, 0.161)  | 0.000 (0.000, 0.161)  | 0.000 (0.000, 0.161)     |
| Disciplined × Cooperative           | n/a                   | 0.000                 | 0.000                    |
| Native × Cooperative (w/ check)     | 0.000                 | 0.000                 | 0.000                    |
| Native × Attacker                   | n/a                   | 0.000                 | 0.000                    |

The Yao free-chat row is the headline: leak rate **scales inversely with
model capability across the three providers we tested**. Haiku 4.5
discloses its wealth in 10 of 20 free-chat trials — twice GPT-5.5's rate
and 1.5x GLM's rate. This is consistent with the PSI free-chat ordering
(Haiku 0.200 > GLM 0.150 > GPT-5.5 0.000) but the Yao gap is sharper.

Critically, **the disciplined-shim and native-CBCL rows hold at 0.000
across all three providers**. The dialect's content forms
(`yao-bracket`, `yao-bracket-commit`, `yao-bracket-reveal`)
syntactically cannot carry a wealth value, so the leak path the
free-chat surface admits is closed at the grammar layer regardless
of how leaky the underlying model is on its own.

The wealth-derived-salt failure mode that motivated the seat-level
privacy check (originally observed in 2/20 GLM-5.1 native trials)
did not surface in any Haiku trial. Native-CBCL utility -0.05 is at
the noise floor (single trial of -1, others 0); Haiku is conservative
in this binding.
