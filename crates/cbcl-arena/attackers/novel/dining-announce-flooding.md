# Novel pattern: dining-announce-flooding

**Challenge:** Dining Cryptographers (REQ-1112)
**Category:** Malicious-novel
**Author:** Hugo O'Connor (`hugo.oconnor@gmail.com`)
**Date:** 2026-04-30

## Attack surface

Each diner's announcement `a_i = r_{ij} XOR r_{ik} XOR p_i` is the
load-bearing private signal in the DC-net. A peer that observes three
announcement bits (`a_1 + a_2 + a_3` mod 2) decides "anyone paid?". If
an attacker can inject multiple `dc-announce` messages at the right
time, it can flip the verdict and (with luck) place the attacker's
chosen target in the unanimity-trap window.

## Pattern behaviour

`announce-flooding` skips the entire pair phase (mask + reveal) and
broadcasts three back-to-back `dc-announce` messages with `:bit true`
and `:caused-by begin`. The XOR sum, if accepted, would always evaluate
to `true` (odd parity), forcing every peer to verdict `Internal` even
when the outsider paid.

A CBCL-disciplined peer rejects the message at `verify_causal`: the
protocol clause requires `(all dc-reveal-* )` as the predecessor of
`dc-announce`, and the early flood arrives with no reveals at all.
The honest peers' announcement bits remain unaffected because the
flood lands in the quarantine buffer (CON-1120 post-condition #2).

## Structural distinction from `Malicious-published`

The published catalogue contains *no protocol-out-of-order* attacks at
all — every published DC pattern is a prose interrogation. The three
out-of-order patterns in `Malicious-novel` (this one, `mask-leak`,
`hash-commit-mimic`) attack three distinct rules of the protocol:

- `mask-leak`     — wrong predecessor for `dc-reveal-*`
- `announce-flooding` — wrong predecessor for `dc-announce`
- `hash-commit-mimic` — wrong thread for a structurally-valid mask

`announce-flooding` is the only one that emits MULTIPLE messages and
relies on flooding the channel to swing a numerical aggregate.

## Originality declaration

To the best of my knowledge no pattern in `Malicious-novel` has
appeared in public Arena game logs prior to this commit. I have not
consulted any Arena game transcript except to verify the structural
shape (multi-burst `dc-announce` with `:caused-by begin`) is absent
from the public catalogue at 2026-04-30. This declaration is signed
via the git-blame author of this file (Hugo O'Connor); see `REQ-1131.1`
for the discipline.
