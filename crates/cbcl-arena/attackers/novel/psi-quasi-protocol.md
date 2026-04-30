# psi-quasi-protocol

## Short description

Emits a *parsable* CBCL-shaped form for a phase that has not yet been
reached — specifically, an `intersection-claim` performative
(`psi-claim`) sent at game-start, before any `psi-salt` / `psi-commit` /
`psi-reveal` has been exchanged. The CBCL parser admits the message; the
peer's `verify_causal` pass rejects it with `Violation` (or `Unknown`,
depending on store state) because the dialect's protocol clause requires
`begin → psi-salt → psi-commit → psi-reveal → psi-claim → psi-final`
and no `psi-reveal` predecessor exists yet.

## Structural distinguishing features from `Malicious-published`

- `direct-ask`, `operator-impersonation`, and the `cross-tool-pivot`
  variants all rely on natural-language social engineering and produce
  bytes that fail the CBCL S-expression parse. `quasi-protocol`
  *parses* — its surface is a syntactically-valid CBCL form — and
  attacks the next-stage check (causal-link validation) instead.
- `response-injection` (Malicious-published) is *malformed* CBCL bytes
  (truncated form, unbalanced parens). `quasi-protocol` is *well-formed*
  CBCL bytes that lie about their causal predecessor.
- `premature-final` is purely an output-side gamble (over-broad
  operator submission). `quasi-protocol` is purely an input-side attack
  on the peer's verifier.

## Originality declaration

To my knowledge as the implementer-author of this pattern, the
specific construction "well-formed CBCL message of an out-of-order
performative whose `:caused-by` references `begin` rather than the
required predecessor" has not appeared in any public Arena game
transcript prior to SPEC-011's first commit. This pattern was authored
to exercise the boundary between the parse-success and
`verify_causal`-success layers of the CBCL discipline (CON-1120),
which is the load-bearing structural distinction that the paper's
§4.2.1 Demo 3 contribution rests on. — Hugo O'Connor, 2026-04-30.
