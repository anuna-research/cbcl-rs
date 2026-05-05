# GPT-5.5 (Codex) — PSI live-LLM probe (N=100 per cell)

Replication of the N=20 cross-provider companion sweep at the larger sample
size. Same harness (`examples/glm_psi.rs`) with `--backend codex`, routing
through a local `codex-responses-proxy` on `127.0.0.1:8787` against a
ChatGPT/Codex subscription.

Operator: PSI, set size 4, universe 100 nouns, uniform overlap.
Each cell ran 100 independent trials at temperature 0.
Transcripts: `crates/cbcl-arena/transcripts/gpt55-{cell}-NNN.jsonl`.

| Cell                                  | Leak (95% CI)         | Utility | Security | Wall-time |
|---------------------------------------|-----------------------|---------|----------|-----------|
| Free-chat × Attacker                  | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |       —   |
| Disciplined-shim × Attacker           | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |       —   |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |       —   |
| Native-CBCL × Cooperative             | 0.000 (0.000, 0.037)  |  0.18   |  1.00    |  3645 s   |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.037)  |  0.01   |  1.00    |  4322 s   |

Total wall-time across PSI + Yao cells: see `run.log` (15535 s ≈ 258 min).

## Comparison to N=20 (paper Table tab:arena-codex-psi)

| Cell                          | N=100                          | N=20                          |
|-------------------------------|--------------------------------|-------------------------------|
| Free × Attacker               | 0.000 (0.000, 0.037)           | 0.000 (0.000, 0.161)          |
| Disciplined × Attacker        | 0.000 (0.000, 0.037)           | 0.100 (0.028, 0.301)          |
| Disciplined × Cooperative     | util=0.00, leak 0              | util=2.00, leak 0             |
| Native × Cooperative          | util=0.18, leak 0              | util=0.00, leak 0             |
| Native × Attacker             | leak 0                         | leak 0                        |

Two notable shifts from N=20.

1. Disciplined × Cooperative utility dropped from 2.00 (17/20 successful
   intersections) to 0.00 (0/100). At N=100 GPT-5.5 abstains by submitting
   empty intersection claims rather than computing a result; security
   stays at 1.00. The most plausible explanation is variant-routing on the
   Codex-proxy endpoint between 2026-05-02 and 2026-05-05, since neither
   model handle pins a stable variant-date string.

2. Disciplined × Attacker leak dropped from 0.100 (2/20) to 0/100. Same
   variant-routing explanation likely. The Wilson 95% CI on 2/20 was
   [0.028, 0.301]; the N=100 CI is [0.000, 0.037].

GPT-5.5 produced 0/100 leaks across every PSI cell, which (combined with
the Yao result in `yao.md`) makes Codex the most-conservative provider in
this sweep. The trade-off is utility: GPT-5.5 abstains across both shim
and native cooperative cells, where the other two providers complete the
protocol at non-trivial rates.
