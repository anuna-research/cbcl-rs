# Warrant

The signed authority of one key to send a set of acts in one
[[capability-seat|seat]]. A warrant is an [[object-capability|capability]]:
it is issued, narrowed and removed by signed meta acts in the thread's log.
A *root warrant* comes from the [[role-cast|cast]]; a *granted warrant*
comes from a `grant` that names the warrant it derives from. Within one role
a warrant never authorises more than the warrant it derives from. An
appointment into another role starts that role's act set instead, bounded by
the appointer's right to appoint. A *proxy* is a warrant that acts in its
delegator's seat.

An act made under a granted warrant names it with `:warrant`, so the
verifier checks one chain and never searches, which closes the
[[confused-deputy|confused deputy]]. A removal binds every act whose
authority past contains it, and no other.

Specified in [[SPEC-020-capability-seats]]. The nearest established notion
is the SPKI authorisation certificate; the session-type literature speaks of
a participant occupying a role. Earlier drafts said *seat* for this object;
SPEC-020 ADR-2016 records the change.
