# GLM-5.1 — PSI live-LLM probe (N=100 per cell)

Replication of the N=20 sweep (`measurements/N20-*-2026-05-02/psi.md`) at the
larger sample size requested by reviewers / Aaron's email of 2026-05-05.
Same harness (`examples/glm_psi.rs`), same operator, attacker library, and
dialect as the N=20 sweep. `--backend glm`, routed via `ZAI_API_KEY`.

Operator: PSI, set size 4, universe 100 nouns, uniform overlap.
Each cell ran 100 independent trials at temperature 0.
Transcripts: `crates/cbcl-arena/transcripts/glm51-{cell}-NNN.jsonl`.

| Cell                                  | Leak (95% CI)         | Utility | Security | Wall-time |
|---------------------------------------|-----------------------|---------|----------|-----------|
| Free-chat × Attacker                  | 0.110 (0.063, 0.186)  |  0.01   |  0.78    |       —   |
| Disciplined-shim × Attacker           | 0.170 (0.109, 0.255)  |  0.44   |  0.66    |       —   |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.037)  |  2.08   |  1.00    |       —   |
| Native-CBCL × Cooperative             | 0.000 (0.000, 0.037)  |  1.08   |  1.00    | 11035 s   |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |       —   |

Total wall-time across PSI cells: see `run.log` (full sweep PSI + Yao = 49539 s ≈ 825 min).

## Comparison to N=20 (paper Table tab:arena-glm-psi)

| Cell                          | N=100                          | N=20                          |
|-------------------------------|--------------------------------|-------------------------------|
| Free × Attacker               | 0.110 (0.063, 0.186)           | 0.150 (0.052, 0.360)          |
| Disciplined × Attacker        | 0.170 (0.109, 0.255)           | 0.200 (0.081, 0.416)          |
| Disciplined × Cooperative     | util=2.08, leak 0              | util=2.00, leak 0             |
| Native × Cooperative          | util=1.08, leak 0              | util=0.40, leak 0             |
| Native × Attacker             | leak 0                         | leak 0                        |

Notable change: native-CBCL × cooperative utility lifts from 0.40 → 1.08.
The N=20 number was a small-sample low estimate; the N=100 number places
GLM within 0.4 of Haiku on this cell. The other cells reproduce the N=20
picture with tighter Wilson 95% CIs.
