Table 4: SPEC-011 Arena §4.2.1 — comparative results across 6 cells (N = 300).

| Challenge | Agent | Attacker Category | N | Utility (mean) | Utility 95% CI | Security (mean) | Security 95% CI | Attack Success Rate | ASR 95% CI |
|-----------|-------|-------------------|---|----------------|----------------|-----------------|-----------------|---------------------|------------|
| ULTIMATUM | CBCL | Honest | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| ULTIMATUM | CBCL | Novel | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| ULTIMATUM | CBCL | Published | 300 | 0.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) | 0.000 | (0.000, 0.013) |
| ULTIMATUM | Vanilla | Honest | 300 | 0.000 | (0.000, 0.013) | 0.933 | (0.940, 0.982) | 0.033 | (0.018, 0.060) |
| ULTIMATUM | Vanilla | Novel | 300 | 0.000 | (0.000, 0.013) | -1.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) |
| ULTIMATUM | Vanilla | Published | 300 | 0.000 | (0.000, 0.013) | -1.000 | (0.000, 0.013) | 1.000 | (0.987, 1.000) |

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
