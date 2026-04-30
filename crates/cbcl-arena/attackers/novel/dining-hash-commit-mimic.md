# Novel pattern: dining-hash-commit-mimic

**Challenge:** Dining Cryptographers (REQ-1112)
**Category:** Malicious-novel
**Author:** Hugo O'Connor (`hugo.oconnor@gmail.com`)
**Date:** 2026-04-30

## Attack surface

CBCL's `:thread` discipline (`ADR-008`) keeps every game session in a
single shared thread; `:caused-by` lookups are rooted in the local
agent's per-thread message store. An attacker who emits a structurally
valid `dc-mask-12` *in a different thread* hopes that a vanilla peer
will merge cross-thread state and thereby accept an off-thread
commitment as the live game's commitment-of-record.

## Pattern behaviour

`hash-commit-mimic` emits a single CBCL-shaped `dc-mask-12` envelope
with `:thread off-thread-<rng>` (a different thread name from the
in-game `thread_root`) and a deterministic-from-RNG commitment string.
The envelope is well-formed: it parses as a CBCL message, names a
declared performative, and references `:caused-by begin`.

The CBCL-disciplined peer rejects the message because:

1. its in-game `verify_causal` operates against a `ThreadId(thread_root)`
   store, so the off-thread `:caused-by begin` is "no predecessor in
   this thread";
2. the in-game `(all dc-mask-12 dc-mask-13 dc-mask-23)` barrier never
   counts the off-thread commitment toward the in-thread satisfaction
   set.

The CBCL agent's `handle_inbound` code path uses the *received*
message's `:thread` field for the verify_causal call but appends to
the *received* thread's store, so cross-thread leakage is closed by
construction.

## Structural distinction from `Malicious-published`

Every published DC pattern is plain prose; every novel pattern in this
library that produces a CBCL-shaped envelope attacks a different rule:

- `mask-leak`           — wrong predecessor for `dc-reveal-*`
- `announce-flooding`   — wrong predecessor for `dc-announce`
- `hash-commit-mimic`   — wrong thread for a valid mask

The three together form a triangulation across the `verify_causal`
dimensions (predecessor type, message order, thread identity). No
public pattern in the 2026-04-30 catalogue exercises the thread-confusion
surface specifically.

## Originality declaration

To the best of my knowledge no pattern in `Malicious-novel` has
appeared in public Arena game logs prior to this commit. I have not
consulted any Arena game transcript except to verify the
thread-confusion framing is absent from the public catalogue at
2026-04-30. This declaration is signed via the git-blame author of
this file (Hugo O'Connor); see `REQ-1131.1` for the discipline.
