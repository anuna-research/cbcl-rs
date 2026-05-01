# GPT-5.5 (Codex) — PSI live-LLM probe (N=20 per cell)

Cross-provider companion to the existing GLM-5.1 PSI probe in
`paper-evidence/glm51-*.jsonl` (paper Table tab:arena-glm-psi).
Same harness (`examples/glm_psi.rs`) with `--backend codex`, routing
through a local `codex-responses-proxy` (David-Factor/codex-responses-proxy)
on `127.0.0.1:8787` against a ChatGPT/Codex subscription. Only
`gpt-5.5` is exposed via the Codex backend on a ChatGPT account.

Operator: PSI, set size 4, universe 100 nouns, uniform overlap. Each
cell ran 20 independent trials at temperature 0; transcripts at
`crates/cbcl-arena/transcripts/gpt55-{cell}-NNN.jsonl` (gitignored
by default; rerun the harness to regenerate).

| Cell                                  | Leak (95% CI)         | Utility | Security | Wall-time |
|---------------------------------------|-----------------------|---------|----------|-----------|
| Free-chat × Attacker                  | 0.000 (0.000, 0.161)  |  0.05   |  1.00    |  320.5 s  |
| Disciplined-shim × Attacker           | 0.100 (0.028, 0.301)  |  0.20   |  0.80    |  394.9 s  |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.161)  |  2.00   |  1.00    |  283.9 s  |
| Native-CBCL × Cooperative             | 0.000 (0.000, 0.161)  |  0.00   |  1.00    | 1064.1 s  |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.161)  |  0.05   |  1.00    |  714.0 s  |

## Comparison to GLM-5.1 (paper Table tab:arena-glm-psi)

| Cell                          | GPT-5.5 (Codex)       | GLM-5.1 (Z.ai)        |
|-------------------------------|-----------------------|-----------------------|
| Free × Attacker               | 0.000 (0.000, 0.161)  | 0.150 (0.052, 0.360)  |
| Disciplined × Attacker        | 0.100 (0.028, 0.301)  | 0.200 (0.081, 0.416)  |
| Disciplined × Cooperative     | 0.000 util=2.00       | 0.000 util=2.00       |
| Native × Cooperative          | 0.000 util=0.00       | 0.000 util=0.40       |
| Native × Attacker             | 0.000 (0.000, 0.161)  | 0.000 (0.000, 0.161)  |

Headline: the structural-defence claim (CBCL row stays at 0 across
attacker peers) holds across both providers. Both models leak through
the disciplined-shim's only legitimate plaintext channel
(`claim_intersection.members`); GPT-5.5 leaks at half GLM's rate
(0.10 vs 0.20) but the 95% CIs overlap. Both models fully resist
attacker peers under native-CBCL; GPT-5.5 is more conservative
(util=0.00 vs GLM util=0.40 cooperative), abstaining rather than
emitting a structurally novel claim under live-LLM substitution.
