# GLM-5.1 — Yao Millionaire live-LLM probe (N=100 per cell)

Replication at the larger sample size. Same harness (`examples/glm_yao.rs`),
same operator, attacker library, and dialect as the N=20 sweep.
The Native-CBCL cell runs with the seat-level salt-leak privacy check
(`src/glm/cbcl_native_yao.rs`) active.

Operator: Yao Millionaire, log-uniform wealth on [1, 1e9].
Each cell ran 100 independent trials at temperature 0.
Transcripts: `crates/cbcl-arena/transcripts/glm51-yao-{cell}-NNN.jsonl`.

| Cell                                  | Leak (95% CI)         | Utility | Security |
|---------------------------------------|-----------------------|---------|----------|
| Free-chat × Attacker                  | 0.230 (0.158, 0.322)  |  0.05   |  0.54    |
| Disciplined-shim × Attacker           | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.037)  |  0.07   |  1.00    |
| Native-CBCL × Cooperative (w/ check)  | 0.000 (0.000, 0.037)  |  0.10   |  1.00    |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |

## Comparison to N=20 (paper Table tab:arena-glm-yao)

| Cell                                | N=100                          | N=20                          |
|-------------------------------------|--------------------------------|-------------------------------|
| Free × Attacker                     | 0.230 (0.158, 0.322)           | 0.350 (0.181, 0.567)          |
| Disciplined × Attacker              | 0.000 (0.000, 0.037)           | 0.000 (0.000, 0.161)          |
| Native × Cooperative (w/ check)     | 0.000 (0.000, 0.037)           | 0.000 (0.000, 0.161)          |
| Native × Attacker                   | 0.000 (0.000, 0.037)           |                  —            |

Headline: the seat-level salt-leak privacy check holds across N=100 trials
on the Native-CBCL × Cooperative cell, with Wilson 95% CI now tightened to
[0.000, 0.037] (cf. [0.000, 0.161] at N=20). The disciplined-shim grammar
floor on Yao remains at 0/100 across attacker peers (the dialect's
content forms `yao-bracket`, `yao-bracket-commit`, `yao-bracket-reveal`
syntactically cannot carry a wealth value). Free-chat leak rate at
N=100 is 0.230 [0.158, 0.322], lower than the N=20 point estimate but
within overlapping CIs.
