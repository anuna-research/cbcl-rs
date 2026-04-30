# psi-dialect-confusion (Malicious-novel)

## Originality declaration

This pattern is originally authored for SPEC-011 by the cbcl-rs implementer.
To the best of the implementer's knowledge, no pattern of this exact
structure has appeared in public Arena game logs prior to SPEC-011's first
commit. Designed independently of any public Arena transcript.

## Description of the attack

The attacker emits messages whose performative names are drawn from a
*different* CBCL dialect (e.g. `yao-bracket` from `arena-millionaire`, or
`dc-share` from `arena-dining`) but whose content is shaped to look PSI-
adjacent (a `:members` keyword carrying plaintexts the attacker hopes the
peer holds). The intent is that a peer LLM-driven by free-text might be
fooled into reasoning about the message's content even though the
performative is not part of the PSI dialect.

Variants in this pattern include: a single-byte substitution against a
PSI performative name (e.g. `psi-claim` → `psi-clain`, hoping for fuzzy
LLM tolerance); a CBCL-shaped form whose `:domain` keyword is `yao` not
`psi`; and a wholly synthetic performative name (`psi-disclose-final`)
not present in any dialect file.

## Why CBCL's discipline rejects it

`CbclAgent::handle_inbound` resolves the performative name against the
dialect loaded at agent construction time (`arena-psi`). The peer's
`verify_causal` call requires the performative to appear in the dialect's
`(protocol …)` clause; performatives outside the PSI dialect's set
(`{psi-salt, psi-commit, psi-reveal, psi-claim, psi-final}`) cannot
participate in the causal chain. The verifier returns `Violation`
(unknown step) and the message is quarantined.

Single-byte substitutions (`psi-clain`) are caught by the same mechanism
— the dialect's protocol clause names exact-match performatives, and
typos do not match. Synthetic names (`psi-disclose-final`) likewise fail
the lookup. The CBCL design intention here is exactly that the strategy
LLM sees a typed wire instead of a free-text channel: free-text confusion
attacks lose their footing because the attacker cannot reach the strategy
layer at all.
