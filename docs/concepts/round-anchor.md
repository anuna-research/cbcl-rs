# Round anchor

For a counted fan-in, the message its `:anchor` names. Each counted act
walks back to it through its own position's earlier acts, so an auction
`reveal` reaches the anchor `open` through its own `commit`. The anchor's
performative is fixed at installation. The *round membership* is the set of
positions of the counted role that exist in the anchor's authority past and
are not emptied there; a contested position is a member, and a position
created after the anchor is not.

The anchor plays the part of the lock in dynamic multirole session types: it
fixes the membership that senders and receivers count, without a barrier,
because one content-addressed message fixes the set for every verifier. The
fan-in's own authority past is the round's cut: it fixes which acts and
which removals the round saw, so no orderer is needed. A
[[capability-seat|seat]] granted after the anchor is admitted and not
counted; it joins a round with a later anchor.

Specified in [[SPEC-020-capability-seats]] (REQ-2046, ADR-2006), refining
the occupant-counted fan-in of [[SPEC-014-role-layer-endpoint-projection]].
