# Claude Haiku 4.5 (OpenRouter) — Yao Millionaire live-LLM probe (N=100 per cell)

Replication at the larger sample size. Same harness (`examples/glm_yao.rs`)
with `--backend haiku`, routing through OpenRouter at the
`anthropic/claude-haiku-4.5` route. The Native-CBCL cell runs with the
seat-level salt-leak privacy check (`src/glm/cbcl_native_yao.rs`) active.

Operator: Yao Millionaire, log-uniform wealth on [1, 1e9].
Each cell ran 100 independent trials at temperature 0.
Transcripts: `crates/cbcl-arena/transcripts/hk45-yao-{cell}-NNN.jsonl`.

| Cell                                  | Leak (95% CI)         | Utility | Security |
|---------------------------------------|-----------------------|---------|----------|
| Free-chat × Attacker                  | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |
| Disciplined-shim × Attacker           | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |
| Native-CBCL × Cooperative (w/ check)  | 0.000 (0.000, 0.037)  | -0.05   |  1.00    |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.037)  |  0.03   |  1.00    |

The seat-level salt-leak privacy check on the Native-CBCL × Cooperative
cell holds across N=100 trials with Wilson 95% CI [0.000, 0.037].

## Three-provider Yao comparison at N=100

| Cell                                | GLM-5.1               | GPT-5.5 (Codex)       | Haiku 4.5             |
|-------------------------------------|-----------------------|-----------------------|-----------------------|
| Free × Attacker                     | 0.230 (0.158, 0.322)  | 0.000 (0.000, 0.037)  | 0.000 (0.000, 0.037)  |
| Disciplined × Attacker              | 0.000                 | 0.000                 | 0.000                 |
| Disciplined × Cooperative           | util=0.07, leak 0     | util=0.00, leak 0     | util=0.00, leak 0     |
| Native × Cooperative (w/ check)     | util=0.10, leak 0     | util=0.10, leak 0     | util=-0.05, leak 0    |
| Native × Attacker                   | leak 0                | leak 0                | leak 0                |

Across all three providers, Yao native cells show 0/100 leaks at N=100.
The Free × Attacker cell is the only Yao cell with any leak rate
above the Wilson 95% CI floor, and only on GLM at this sample size.
