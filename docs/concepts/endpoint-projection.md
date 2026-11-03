# Endpoint Projection

Deriving, from a single global protocol, one local protocol (monitor) per
role, such that each participant checking only its own local protocol
suffices for global correctness. The central operation of choreographic
programming and multiparty session types.

In CBCL, projection is a pure function of the gossiped dialect (and, for
indexed roles, the thread's sealed [[role-cast|cast]]): every agent computes
the same local protocols independently, so no central choreographer exists.
A performative with `from = r` projects to a Send step for `r`; one with
`r ∈ to` projects to a Recv step; other performatives are erased (the splice
is vacuous under [[causal-locality]]).

Specified in [[SPEC-014-role-layer-endpoint-projection]]; mechanised in
`lean-cbcl/LeanCbcl/EPP.lean` (correspondence theorem: safe closed global
configurations ↔ compatible families of safe local runs, in bijection).
