# Object capability

A reference that both designates a resource and conveys the authority to use
it. Holding the reference is the permission; no separate access list exists.
Authority spreads only by introduction: a holder passes it to a party it can
already reach. A holder can attenuate what it passes on, for example to a
subset of operations, and a chain of such grants can be revoked at any link.

CBCL adopts the certificate form of the idea. Grants are signed messages in
the thread's log, and each act names the grant it relies on. See
[[capability-seat]], [[confused-deputy]] and
[[SPEC-020-capability-seats]].
