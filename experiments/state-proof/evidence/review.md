---
mode: explanation
status: static-review
---
# Fresh-session review record

Reviewer: `/root/proof_review`, a separate fresh-context agent session.
Generating tool: OpenAI Codex (GPT-6 per session instructions).
The reviewing model version was inherited, not independently identified.
This is not the cross-model or human cryptographic review required for production.

The reviewer received the experiment brief and implementation, with an explicit
mandate to find unsound constraints, statement-binding faults, authentication
assumptions, resource hazards and candidate-order dependence. The reviewer did
not modify files or execute tests.

Initial findings:

- Byte bounds alone did not bound recursive parsing depth. Resolution: use the
  native parser with fuel 256; deep source and candidate tests return errors.
- Independently valid snapshots did not prove admission against the previous
  context. Resolution: compile explicit valid before/after pairs with native
  admission starting from all previous accepted acts, then enforce that relation.

On the revised implementation, the reviewer found no additional apparent circuit
soundness defect. They checked copy wiring, fixed relation constants, one-hot
subset equality, transition accumulation, both commitment limbs, zero
initialisation, final-one enforcement, and witness-independent key layout.
They bounded the eight-candidate layout at k<=14 under this configuration.

The reviewer recommended targeted transition-constraint mutation because
ordinary role-free corpus cases can make that check redundant. The implementation
now supplies a dishonest final transition sum in a test-only witness, and the
mutation runner removes its recurrence constraint. The named test executes and
fails under that mutation. A separate mutation removes an after-state public
binding and also produces an executed assertion failure.

Remaining review: independent cross-model and human domain review, formal
compiler/circuit equivalence, and cryptographic deployment audit are unverified.
The experiment remains isolated and is not production-authorised.
