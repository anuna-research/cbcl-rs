# Dining Cryptographers — coalition attack (threat-model expansion)

**Author:** Hugo O'Connor (`hugo.oconnor@gmail.com`)
**Date:** 2026-04-30
**Owning code:** `crates/cbcl-arena/src/attackers/dining.rs`
  (`CoalitionAttacker`, `CoalitionScope`)

## Originality declaration

This file declares an originally-authored *expansion* of SPEC-011's
stated DC threat model. All previous DC attackers in `dining.rs`
(`HonestCooperative`, the five `Published` patterns, the four
single-seat `Novel` patterns) assume a **single-attacker** adversary.
SPEC-011 §TM-1102 codifies this scope explicitly. The
`CoalitionAttacker` introduced alongside this document MODELS a
two-seat adversary that has **already exchanged a shared random bit
out-of-band** before any in-game message is sent — this is not within
SPEC-011's stated threat model and is signalled here to keep the
paper's claims honest.

The pattern is novel in this codebase. To the best of my knowledge no
public Arena game log at 2026-04-30 carries a transcript pair labelled
as a 2-seat coalition for DC; this declaration is signed via the git
log author of this file.

## Mechanism

For three diners with a 2-coalition (seats 1 and 2 colluding against
the honest seat 3), the standard DC-net result is:

```
a_1 = paid_1 XOR pair_bit_12 XOR pair_bit_13
a_2 = paid_2 XOR pair_bit_12 XOR pair_bit_23
a_3 = paid_3 XOR pair_bit_13 XOR pair_bit_23
```

The coalition controls seats 1 and 2 and therefore knows
`pair_bit_12` (both members of (1,2) compute it from the shared
`pair_seed`), `pair_bit_13` (member 1 derives it), and `pair_bit_23`
(member 2 derives it). On observing `a_3`, the coalition computes:

```
paid_3 = a_3 XOR pair_bit_13 XOR pair_bit_23
```

`paid_3` is recovered deterministically. The coalition has broken
seat 3's anonymity.

## CBCL's defence is dialect-level, not cryptographic

A naive reading of the result is "CBCL's pairwise commit-and-reveal
machinery defeats the coalition". It does not. The coalition can
mechanically execute the standard DC-net algorithm against a CBCL
peer just as well as against a vanilla peer because the pair-bit
derivation is deterministic from the shared `pair_seed` (see
`agents::cbcl::dining::DiningCbclStrategy::pair_bit`). Both vanilla
and CBCL diners produce identically-distributed announcement bits, so
the coalition's deduction succeeds in both cases at the bit level.

What CBCL **does** prevent is the *coordination channel* required
before the game starts. The dining dialect's `(then ...)` chain
admits no performative for "share-a-coalition-bit-out-of-band". A
CBCL-disciplined seat cannot emit such a message: parsing rejects
free-form prose, and `verify_causal` rejects any well-formed
s-expression whose performative is absent from the protocol. So in
the CBCL world a coalition can only function if there is an
out-of-band channel (via the wider operating environment) — CBCL
neither provides nor blesses any such channel.

The `CoalitionAttacker` MODELS exactly such an out-of-band channel:
its constructor takes a `pre_game_bit: bool` and `pair_seed: String`
that the test harness supplies, simulating a coalition that exchanged
shared randomness outside the simulator's scope. Against a Vanilla
peer, this is a complete attack: the coalition learns `paid_3`.
Against a CBCL peer, the coalition's deduction succeeds at the bit
level, but the security loss is correctly attributed to "the threat
model was extended to include out-of-band coordination" rather than
"CBCL was breached".

## CoalitionScope

```rust
pub enum CoalitionScope {
    /// 2-of-3 coalition (e.g. seats 1 and 2 vs seat 3).
    Pairwise,
    /// 3-of-3 coalition (degenerate: every diner is in the coalition).
    Triadic,
}
```

`Pairwise` is the load-bearing case for the paper's discussion of
threat-model boundaries. `Triadic` is documented for completeness but
is degenerate: if all three seats collude they trivially know every
`paid_i`; nothing is hidden.

## Why model this despite being out of SPEC-011's scope

Two reasons:

1. **Honest threat-model boundary.** Demonstrating where CBCL helps
   *and where it does not* is more credible than asserting blanket
   defeat of every adversary. This file makes the boundary explicit.

2. **Empirical row in Demo 3.** Without the coalition row, Demo 3's
   DC column reports a perfect-defence outcome that is partly an
   artefact of the single-attacker assumption. Adding a coalition
   column shows where the paper's structural-defence claim
   strengthens (against in-channel attackers) and where it does not
   strengthen (against pre-game out-of-band collusion).

## Wiring deferral

The full measurement-matrix wiring (introducing a separate
attack-category column in `measurement.rs`) is deferred to a separate
task to keep this change scoped. The current change exposes
`CoalitionAttacker` and `CoalitionScope` and demonstrates the
load-bearing claim through unit tests; downstream measurement
consumption is left for a follow-up.
