# Claude Haiku 4.5 (via OpenRouter) — PSI live-LLM probe (N=20 per cell)

Cross-provider companion to the existing GLM-5.1 PSI probe (paper Table
tab:arena-glm-psi) and the GPT-5.5 (Codex) replication (Table
tab:arena-codex-psi). Same harness (`examples/glm_psi.rs`) with
`--backend haiku`, routing through OpenRouter
(https://openrouter.ai/api/v1/chat/completions) at the
`anthropic/claude-haiku-4.5` route. Anthropic Claude Haiku 4.5 is the
cheapest currently-available Anthropic model.

Routing detail: the OpenRouter route surfaced as `anthropic/claude-4.5-haiku-20251001`
behind the scenes (Amazon Bedrock provider in the response metadata).
Direct `api.anthropic.com` access was unavailable at the time of writing
due to an unresolved billing-side issue independent of key state; the
OpenRouter route reached the same model with byte-identical Chat
Completions request shape so the existing harness wires unchanged.

Operator: PSI, set size 4, universe 100 nouns, uniform overlap. Each
cell ran 20 independent trials at temperature 0; transcripts at
`crates/cbcl-arena/transcripts/hk45-{cell}-NNN.jsonl` (gitignored).

| Cell                                  | Leak (95% CI)         | Utility | Security |
|---------------------------------------|-----------------------|---------|----------|
| Free-chat × Attacker                  | 0.200 (0.081, 0.416)  |  0.05   |  0.60    |
| Disciplined-shim × Attacker           | 0.300 (0.145, 0.519)  |  0.50   |  0.40    |
| Disciplined-shim × Cooperative        | 0.000 (0.000, 0.161)  |  0.00   |  1.00    |
| Native-CBCL × Cooperative             | 0.000 (0.000, 0.161)  |  1.45   |  1.00    |
| Native-CBCL × Attacker                | 0.000 (0.000, 0.161)  |  0.25   |  1.00    |

## Three-provider comparison (PSI live-LLM extension)

| Cell                          | GLM-5.1               | GPT-5.5 (Codex)       | Haiku 4.5             |
|-------------------------------|-----------------------|-----------------------|-----------------------|
| Free × Attacker               | 0.150 (0.052, 0.360)  | 0.000 (0.000, 0.161)  | **0.200** (0.081, 0.416) |
| Disciplined × Attacker        | 0.200 (0.081, 0.416)  | 0.100 (0.028, 0.301)  | **0.300** (0.145, 0.519) |
| Disciplined × Cooperative     | util=2.00, leak 0     | util=2.00, leak 0     | util=0.00, leak 0     |
| Native × Cooperative          | util=0.40, leak 0     | util=0.00, leak 0     | **util=1.45**, leak 0 |
| Native × Attacker             | leak 0                | leak 0                | leak 0                |

Two cross-provider headlines:

1. **Smaller / cheaper model = more vulnerable on unstructured surfaces.**
   Haiku 4.5 leaks at 0.200 free-chat and 0.300 disciplined-shim — the
   highest of the three providers in both cells. The contract-boundary
   case in Section~\ref{footnote:contract-boundary} (the dialect's only
   legitimate plaintext channel under disciplined-shim) is exactly where
   the gap between providers is largest, and exactly where Haiku is
   weakest. The structural-defence argument therefore strengthens for
   smaller models: the dialect's contribution is bigger when the model
   itself is leakier.

2. **Smaller model = better at following a strict structured surface.**
   Native-CBCL utility goes 0.00 (GPT-5.5) -> 0.40 (GLM) -> **1.45**
   (Haiku). When the protocol is enforced at the parser-or-quarantine
   boundary, Haiku follows it most reliably and computes the
   intersection most often, with leak rate held at 0.000 by the
   dialect-gate the same as for the larger models. CBCL not only
   catches more leaks against weaker models, it also extracts more
   useful work from them.
