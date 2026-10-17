# Capability seat

The authority to send a set of acts in one role of a thread, held by one
key. A seat is a [[object-capability|capability]]: it is issued, narrowed
and withdrawn by signed meta acts in the thread's log. A *root seat* comes
from the [[role-cast|cast]] on the thread's root. A *granted seat* comes from
a `grant` that names the seat it derives from.

A seat never authorises more than the seat it derives from. An act made under
a granted seat names that seat with `:under`, so the verifier checks one
chain and never searches. The roles themselves, and their
[[endpoint-projection|projection]], do not change when seats change hands.

Specified in [[SPEC-020-capability-seats]], which refines the fixed cast of
[[SPEC-014-role-layer-endpoint-projection]].

The word *seat* is coined by SPEC-020; it is not a term of art. The nearest
established notions are a participant occupying a role in dynamic multirole
session types (Deniélou and Yoshida, 2011) and a capability for a role in
object-capability systems. A seat is kept apart from its *position*, the
role binding that persists while the key holding it changes.
