Table 4: SPEC-011 Arena §4.2.1 — comparative results across 18 cells (N = 300).

| Challenge | Agent | Attacker Category | N | Utility (mean) | Utility 95% CI | Security (mean) | Security 95% CI | Attack Success Rate | ASR 95% CI |
|-----------|-------|-------------------|---|----------------|----------------|-----------------|-----------------|---------------------|------------|
| DINING | CBCL | Honest | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| DINING | CBCL | Novel | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| DINING | CBCL | Published | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| DINING | Vanilla | Honest | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| DINING | Vanilla | Novel | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| DINING | Vanilla | Published | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| MILLIONAIRE | CBCL | Honest | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| MILLIONAIRE | CBCL | Novel | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| MILLIONAIRE | CBCL | Published | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| MILLIONAIRE | Vanilla | Honest | 300 | 0.000 | (0.000, 0.013) | 0.967 | (0.962, 0.993) | 0.017 | (0.007, 0.038) |
| MILLIONAIRE | Vanilla | Novel | 300 | 0.000 | (0.000, 0.013) | 0.993 | (0.981, 0.999) | 0.003 | (0.001, 0.019) |
| MILLIONAIRE | Vanilla | Published | 300 | 0.000 | (0.000, 0.013) | 0.573 | (0.737, 0.829) | 0.213 | (0.171, 0.263) |
| PSI | CBCL | Honest | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| PSI | CBCL | Novel | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| PSI | CBCL | Published | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| PSI | Vanilla | Honest | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| PSI | Vanilla | Novel | 300 | 0.013 | (0.005, 0.034) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| PSI | Vanilla | Published | 300 | 0.013 | (0.005, 0.034) | 0.020 | (0.454, 0.566) | 0.490 | (0.434, 0.546) |

## Scope

- The simulator measures structural-attack rejection at the dialect-grammar and causal-protocol layers, NOT strategic manipulation through well-formed messages.
- The deterministic-attacker cells use a finite library of attack patterns; the result generalises to attacks of similar structural shape, NOT to the full space of LLM-generated adversaries (the live-LLM cells, where present, address this concern with their own caveats).
- The vanilla NL-chat comparator is calibrated against the public Arena baseline at 2026-04-30; subsequent shifts in the leaderboard population (new attacker LLMs, RLHF updates) may invalidate the calibration and require a comparator refresh.
- CBCL provides no guarantee against rational strategic play; the security score's `+1` value reflects "no information leak that the dialect grammar would admit," NOT "the agent achieved game-theoretic optimal play."
- The simulator is NOT a substitute for live play on `arena.nicolaos.org`; the deterministic local result is the reproducible artefact, while a live-arena field test (separately tracked) provides the in-the-wild confirmation.

## Known Failure Modes

- **Coalition.** Two agents in DC who privately agree on their pairwise random bits before the game can deterministically reveal the third diner's paid-bit. CBCL's `(protocol …)` clause cannot prevent pre-game communication. Out of scope.
- **Strategic non-reveal.** An agent who never sends a `psi-final` / `yao-final` / `dc-final` message receives `0` utility but cannot be blamed structurally — non-participation is allowed by every protocol. Out of scope.
- **Rational defection on cooperative challenges.** An agent who, after exchanging hashes in PSI, chooses to submit a deliberately-wrong final guess receives bad utility but no security violation — the dialect cannot enforce "claim what you computed." Out of scope.
- **Adversarial peer who simply does not engage.** A non-CBCL peer who sends garbage causes our `CbclAgent` to fall back to a defensive-default guess (empty intersection / `unknown` / `external`). The CBCL agent's security stays `+1`, but utility is `0`. This is captured in the utility numbers but is worth calling out as a known bound on the comparison's external validity.
