# GPT-5.5 (Codex) — Yao Millionaire live-LLM probe (N=100 per cell)

Replication at the larger sample size. Same harness (`examples/glm_yao.rs`)
with `--backend codex`, routing through a local `codex-responses-proxy`
on `127.0.0.1:8787` against a ChatGPT/Codex subscription.
The Native-CBCL cell runs with the seat-level salt-leak privacy check
(`src/glm/cbcl_native_yao.rs`) active.

Operator: Yao Millionaire, log-uniform wealth on [1, 1e9].
Each cell ran 100 independent trials at temperature 0.
Transcripts: `crates/cbcl-arena/transcripts/gpt55-yao-{cell}-NNN.jsonl`.

| Cell                                  | Leak (95% CI)         | Utility | Security |
|---------------------------------------|-----------------------|---------|----------|
| Free-chat × Attacker                  | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |
| Disciplined-shim × Attacker           | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |
| Native-CBCL × Cooperative (w/ check)  | 0.000 (0.000, 0.037)  |  0.10   |  1.00    |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.037)  |  0.00   |  1.00    |

## Comparison to N=20 (paper Table tab:arena-codex-yao)

| Cell                                | N=100                          | N=20                          |
|-------------------------------------|--------------------------------|-------------------------------|
| Free × Attacker                     | 0.000 (0.000, 0.037)           | 0.250 (0.112, 0.469)          |
| Disciplined × Attacker              | 0.000 (0.000, 0.037)           | 0.000 (0.000, 0.161)          |
| Native × Cooperative (w/ check)     | 0.000 (0.000, 0.037)           | 0.000 (0.000, 0.161)          |
| Native × Attacker                   | 0.000 (0.000, 0.037)           | 0.000 (0.000, 0.161)          |

Notable: GPT-5.5's Yao free-chat leak rate dropped from 0.250 (5/20,
the wealth-as-threshold pattern documented in the §4.5 main text)
to 0/100, with no harness or prompt change between runs. The pattern
remains documented as an N=20 finding on a specific 2026-05-02 GPT-5.5
variant; the N=100 result is consistent with a more conservative
variant served by the Codex proxy on 2026-05-05.

The seat-level salt-leak privacy check on the Native-CBCL × Cooperative
cell holds across N=100 trials with Wilson 95% CI [0.000, 0.037].
