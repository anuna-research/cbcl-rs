# Round anchor

For an occupant-counted fan-in, the one message that every counted act cites
as its protocol predecessor. The thread root is the anchor when the counted
acts cite the root. The *round membership* is the set of positions whose
principal [[capability-seat|seat]] is live in the seat state of the anchor's
authority past.

The anchor plays the part of the lock in dynamic multirole session types: it
fixes the membership that senders and receivers count, without a barrier,
because one content-addressed message fixes the set for every verifier. A
seat granted after the anchor is admitted and not counted; it joins a round
with a later anchor.

Specified in [[SPEC-020-capability-seats]] (REQ-2046, ADR-2006), refining
the occupant-counted fan-in of [[SPEC-014-role-layer-endpoint-projection]].
