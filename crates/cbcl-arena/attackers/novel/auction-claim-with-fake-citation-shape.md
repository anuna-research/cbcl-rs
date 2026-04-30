# Novel pattern: auction-claim-with-fake-citation-shape

**Challenge:** Sealed-Bid Auction (SPEC-004)
**Category:** Malicious-novel
**Author:** Hugo O'Connor (`hugo.oconnor@gmail.com`)
**Date:** 2026-04-30

## Attack surface

The auction dialect (`demo/dialects/auction.cbcl`) defines
`winner-declaration` with `:proof-commit` and `:proof-reveal` shape
parameters. Both parameters parse as plain symbols/strings — there is
no in-dialect cryptographic check that the cited hash resolves in any
participant's message store. The parse-stage shape rule cannot
distinguish a real content hash from a fabricated one; the only
defence is the operator's score-time citation lookup (REQ-411).

## Pattern behaviour

`claim-with-fake-citation-shape` emits a single byte-payload with the
content-form shape

```text
(winner-declaration :winner bidder-1 :winning-bid 99
                    :proof-commit hfaceface...<random>
                    :proof-reveal hbeefbeef...<random>)
```

— no `:caused-by`, `:thread`, `:sender` envelope. The chat layer may
parse and route this; the operator's score-time citation lookup fails
because neither hash resolves to any stored commit/reveal. CBCL peers
also reject the byte string at the message-parsing layer (it lacks the
required outer-message envelope), so the attack never influences the
honest `AuctionCbclStrategy`.

## Structural distinction from `Malicious-published`

The published catalogue contains:

- `a1-false-bid-claim` — pure free-text natural-language claim
- `a2-forged-commit-citation` — combined free-text impersonation +
  wire-shaped declaration with a free-text role preamble
- `a3-pre-commit-valuation-leak` — natural-language disclosure prompt

`claim-with-fake-citation-shape` is the first **minimal-surface
wire-only** variant: no free-text impersonation, no role preamble,
nothing but the content form itself. This isolates the parser/runtime
boundary as the sole defence surface — exercising it in isolation
matters for diagnostic clarity.

## Originality declaration

To the best of my knowledge no pattern in `Malicious-novel` has
appeared in public Arena game logs prior to this commit. This attack
pattern was authored independently of any public Arena game logs prior
to this work. I have not consulted any Arena game transcript except
to verify that the structural shape (wire-only declaration with no
envelope) is absent from the public catalogue at 2026-04-30. This
declaration is signed via the git-blame author of this file (Hugo
O'Connor); see `REQ-1131.1` for the discipline.
