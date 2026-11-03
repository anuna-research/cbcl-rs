# Causal Locality

R6 clause (vi), the well-formedness condition under which
[[endpoint-projection]] is sound over CBCL's causal DAG: every endpoint role
of a performative `t` (its sender and every recipient) must also be an
endpoint role of each predecessor type named in `t`'s `:caused-by` clause.
The distinguished root `begin` counts every declared role among its endpoint
roles (the root convention), so first steps satisfy the clause.

Equivalent, in the raw-edge regime, to projectability onto every role: a
role can verify its obligations from the messages it alone sends or
receives, so a residual `Unknown` verdict only ever means "a message this
role will see has not yet arrived" — the knowledge-of-choice condition made
operational. Strictly stronger than classical branch merging; the price is
recipient widening, the payoff is no router, ordering, or reliable channels.

Specified in [[SPEC-014-role-layer-endpoint-projection]]; mechanised as
`Proto.causalLocal` in `lean-cbcl/LeanCbcl/EPP.lean` and both directions of
Theorem 1 in `lean-cbcl/LeanCbcl/Projectability.lean`.
