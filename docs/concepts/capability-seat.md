# Capability seat

One binding of a role in a thread, which keeps its identity while the key
holding it changes. A *root seat* comes from the [[role-cast|cast]] on the
thread's root; a `share` or `appoint` grant creates a further seat. The
authority to act in a seat is a [[warrant|warrant]], a signed
[[object-capability|capability]] in the thread's log. A seat is *live* while
its terminal warrant is live, *emptied* when a resign, revoke or cascade
ended it, and *contested* when equals issued two warrants for it.

The roles themselves, and their [[endpoint-projection|projection]], do not
change when seats change hands. A counted fan-in counts seats, not keys, so
a hand-over mid-round changes nothing the fan-in sees.

Specified in [[SPEC-020-capability-seats]], which refines the fixed cast of
[[SPEC-014-role-layer-endpoint-projection]]. The word carries its everyday
sense: a seat on a board is taken over, and the board is unchanged. Earlier
drafts said *position*; SPEC-020 ADR-2016 records the change.
