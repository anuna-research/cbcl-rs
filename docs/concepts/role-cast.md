# Cast

The assignment of agents to roles for one thread, nominated by the
initiator in a `with-roles` wrapper at the thread's causal root and
tamper-evident because the root's content hash anchors every subsequent
`:caused-by` link. The wrapper is addressed to the entire cast (root
convention), so every role's local run contains it.

Nomination binds no one: a singleton role is *occupied* only when the
nominated key signs a message the projection attributes to that role
(ratification by signature); a non-nominee cannot squat the role, and an
agent declines by staying silent. An indexed role's membership is a key set
*sealed* at thread open, which is what makes occupant-counted `(all …)`
fan-ins decidable. A vacant role is a liveness condition (dependents stay
`Unknown`), never a safety violation.

Specified in [[SPEC-014-role-layer-endpoint-projection]]; consumed by the
sealed-bid auction of [[SPEC-004-sealed-bid-auction-demo]].
