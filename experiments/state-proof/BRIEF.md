---
mode: explanation
status: experiment
owner: CBCL maintainer
---
# Bounded Halo2 state checkpoint experiment

The user requested a prototype following the Spindle Halo2 approach. The base is
`origin/state-rules-spec` at `c9093e86597cf6f1b10d0ed9bc3713dda3c88843`.
The generating tool is OpenAI Codex. The session instructions identify GPT-6,
without a more specific model version. No private or production data is used.

## Hypothesis and scope

A real Halo2 circuit can prove valid growth of an accepted message set and the
resulting CBCL state, using a verifier-derived finite relation. Existing
[[SPEC-019-state-rules]] admission and fold functions define that relation.
The prototype targets proof correctness; it makes no projection-speed claim.

The public profile contains one installed role-free dialect, one thread, and at most eight
candidate messages with externally authenticated signer labels. Each valid
subset is independently derived by the verifier: admit to a fixed point, then
fold. SHA-256 commitments use domain separation and length-prefixed inputs.
The circuit checks exact table membership, both state commitments, monotone set
growth, and the exact added-message batch commitment. This is a bounded
specialisation of the existing semantics, not a circuit implementation of the
parser, SHA-256, signature verification, or general admission algorithm.

The failure to avoid is a proof of an arbitrary state that merely accompanies a
valid input commitment. Admission and output must be connected by constraints,
not by the prover's ordinary host-side precheck.

## Experiment acceptance

- P1: actual proofs verify for an accepted transition and match native folding.
- P2: a shape-invalid, signer-mismatched, wrong-thread or pending message cannot
  enter a proved accepted set, including when the honest precheck is bypassed.
- P3: modified before/after set, state, profile or batch commitments fail.
- P4: deletion from the grow-only set and an incorrect batch fail in the circuit.
- P5: reordered candidates compile identically; duplicate identities and exceeded
  resource bounds fail before exponential enumeration or proof setup.
- P6: a new authenticated candidate profile does not inherit trust from an old
  profile. Exact profile and expected statement are verifier-owned inputs.

Core evidence is unit/integration tests and one real serialized proof roundtrip.
Targeted circuit mutation must turn a negative test red. Measurements record
compile, setup, prove, verify, transcript bytes and the public candidate count.
Native parser fuel is capped at 256 expression steps per input to bound stack depth.
The exploration timebox is this implementation session, capped at eight public
candidates and sequential proving; no maximum-budget proof is run.

## Risk, isolation and next step

Tier 1 cryptographic experiment. The user explicitly authorised the prototype.
It is an opt-in workspace crate, with no changes to production admission, fold,
wire formats, signing, or existing bindings. No network service is introduced.
Proof bytes have bounded, strict JSON recognition before backend verification.
The prototype retains all candidates: the accepted-set commitment is not a
replacement for conflict/replacement history. Signatures and authenticated
history completeness remain outside the proof.

A checkpoint's prior root must already be trusted or verified. This circuit has
no recursion or proof accumulation. New candidate universes require a new
profile and keys; fixed-universe chaining alone does not solve unbounded
history. Snapshot enumeration is O(2^n); transition enumeration is O(3^n) before native admission costs, and the verifier reconstructs the relation once.

The next specification step is a scalable transition circuit with authenticated
state paths, candidate-byte binding and a declared authentication boundary.
The maintainer owns that decision. The experiment remains isolated until then;
independent cryptographic review and a human domain review remain open. Prototype
success does not approve production use or mark the parent specification complete.
