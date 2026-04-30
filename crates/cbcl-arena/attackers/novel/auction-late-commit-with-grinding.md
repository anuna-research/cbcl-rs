# Novel pattern: auction-late-commit-with-grinding

**Challenge:** Sealed-Bid Auction (SPEC-004)
**Category:** Malicious-novel
**Author:** Hugo O'Connor (`hugo.oconnor@gmail.com`)
**Date:** 2026-04-30

## Attack surface

SPEC-004 REQ-418 acknowledges *late commit* as a failure mode that the
structural defence does NOT label as manipulation: a single legal late
commit is just a rational play. The novel surface here is **late
commit with grinding** — emitting *multiple* candidate commits before
settling on one, structurally distinguishable from honest
single-commit play.

## Pattern behaviour

The attacker emits five `bid-commitment` payloads in sequence:

```text
(bid-commitment :hash hgrind<random1>...)
(bid-commitment :hash hgrind<random2>...)
(bid-commitment :hash hgrind<random3>...)
(bid-commitment :hash hgrind<random4>...)
(bid-commitment :hash hgrind<random5>...)
```

— each with a distinct fabricated hash. None of these will ever be
revealed in a binding `bid-reveal`. Honest play (REQ-414) emits
exactly one commit per bidder; multi-commit-per-seat is a strict
deviation observable from the operator's transcript index alone.

## Structural distinguishing features

1. **Multi-commit-per-seat.** Honest play emits one
   `(bid-commitment …)` per bidder; this pattern emits five. The
   transcript index trivially distinguishes the two.
2. **No reveal binding.** The pattern never reveals — the commit
   `:hash` values are not derived from any concrete `(body, salt)`
   pair the attacker will later disclose. Operator's REQ-412
   reveal-binds-commit check finds no matching reveal for any of the
   shadow commits.
3. **Observable from operator scope alone.** Unlike A1/A3 (which need
   leak/claim regex matching) and A2 (which needs citation
   resolution), grinding is detectable purely by counting commits per
   seat — a structurally distinct telemetry signature.

This pattern is structurally distinct from each
`Malicious-published` SPEC-004 attack: it produces zero free-text
chat, zero forged citations, and zero valuation leaks — only an
abnormal commit-count signature.

## Originality declaration

To the best of my knowledge no pattern in `Malicious-novel` has
appeared in public Arena game logs prior to this commit. This attack
pattern was authored independently of any public Arena game logs prior
to this work. I have not consulted any Arena game transcript except
to verify that the multi-commit grinding surface is absent from the
public catalogue at 2026-04-30. This declaration is signed via the
git-blame author of this file (Hugo O'Connor); see `REQ-1131.1` for
the discipline.
