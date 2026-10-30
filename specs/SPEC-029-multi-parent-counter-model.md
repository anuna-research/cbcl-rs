---
id: SPEC-029
title: Multi-parent collective counter model
version: 0.1.0
status: implemented
last-updated: 2026-10-31
---

# Multi-parent collective counter model

## Orientation

Allow a validator on either of two conflicting version branches to advance into
a version covering both. This is a Lean-first protocol extension; Rust remains
unchanged. A merge carries obligations, credits and cancellation refunds by unique
transaction ID. Parent balances are never added together.

```text
       A ---\
      /      \
root          M --> further spending
      \      /
       B ---/
```

A validator advances only from a direct parent and carries its entire immutable
signed history into the target's held set. Adoption does not clear old signatures,
fences or releases. Target allocation is recomputed from genesis plus verified
final credits minus held costs plus cancellation-backed refunds. Version adoption
is local; transaction quorums establish spend-certified versions. Those versions
must form an ancestry chain, even though uncertified branches form a DAG.

This replaces the single-successor checkpoint handoff with forward DAG adoption;
it is not an extra quorum on the old one-successor rule. Conservative full-history
coverage may require owner-authorized cancellation to reclaim partial proposals.
Contention may still stall. No consensus or unconditional recovery guarantee is
added. Signature/identifier binding and durable local state remain assumptions.
The numeric model covers a fixed finite catalogue and resource vectors; funded
refinement requires each transaction to debit or credit, but not both, any one
resource coordinate. It models verified certificate delivery rather than packets.

[[SPEC-029-multi-parent-counter-model#CON-2900]] defines graph and handoff rules;
[[SPEC-029-multi-parent-counter-model#CON-2901]] defines the proof obligations;
[[SPEC-029-multi-parent-counter-model#TEST-2900]] defines executable acceptance.

## Amendment Channels

The user authorizes multi-parent development after requesting Lean-first work.
Rust does not change before the model and adversarial review pass. This Tier 1
protocol uses the existing at-most-f Byzantine assumption among 3f+1 validators.
No channel can introduce a global balance oracle, consensus or timeout refunds.
Human review remains a production-release requirement. BCP 14 keywords state
measurable obligations.

## REQ-2900: Genuine branch join

Validators on distinct parents MUST be able to adopt one covering merge when its
local guards hold. The transition MUST preserve old evidence and use unique-ID
accounting. It MUST NOT require choosing one parent or resetting old votes.
Validates: [[SPEC-029-multi-parent-counter-model#TEST-2900]].

## REQ-2901: Derived asynchronous safety

Arbitrary executions MUST preserve nonnegative resources and funded business
refinement. Late certificates and cancellation refunds MUST remain safe. Certified
spending versions MUST be comparable by ancestry. These conclusions MUST be derived
from local guards rather than supplied as endpoint-safety assumptions.
Validates: [[SPEC-029-multi-parent-counter-model#TEST-2900]].

## CON-2900: Version DAG and conservative adoption

```text
VersionId := Fin(V+1), root := 0
Parents(v) := List(Fin(v.val)) lifted into VersionId
Manifest(v) := { held, refunded, credited: Set<TxId>, allocation: ResourceVector }
```

Topological numbering is a finite-proof representation of a DAG, not a consensus
sequence or authority consulted by validators. Every parent precedes its child;
nonroot parent sets are nonempty and distinct. Every parent manifest is validated
before the child. Held/refunded/credited sets include the unions of all parent sets.
Held operations precede the target in the topological numbering. Refunds are held
and have actual cancellation quorums; credits have actual effects quorums.

A valid version uses exact genesis-based books. An honest adopter's current version
belongs to Parents(target). Every historical signature ID belongs to the target
held set, including released or zero-cost transactions. Candidate validity
alone does not activate a globally decided epoch. Honest signatures remain limited
by the fixed target allowance and local per-version scaled charges. No field is
reset when adopting. Actor, issuer and cancellation authorization use the existing
ideal-signature/pinned-role assumptions; the resource proof abstracts the packet
representation and explicit message delivery from
[[SPEC-028-collective-actor-refinement]]. This abstraction is stated in evidence.

The model's `Config.disjoint` MUST require zero cost or zero credit for every
transaction/resource coordinate. This supports separate mint/burn coordinates;
it does not establish gross-debit affordability for simultaneous debit and credit
on one coordinate. The fixed finite transaction/version catalogue bounds each
model instance. Infinite refinement ranges over infinite steps within that
catalogue, not an unbounded extension by fresh identifiers.

The executable harness knows the proof-only honest core to permit unrestricted
Byzantine behavior. A deployed validator cannot use that test. Certificate checks
refer to verified aggregate evidence; packet receipt, per-validator delivery,
identifier codecs and durable storage are abstracted. `known` is a verified
metadata cache, not a global decision authority. Delaying adoption models delayed
receipt; the harness also permits adoption earlier than a concrete delivery
trace. The theorem is a safety overapproximation, not a network equivalence proof.

## CON-2901: Proof route

Prove immutable journals, validated known versions, forward local ancestry,
full historical coverage and independent capacity preservation. Quorum intersection
then derives comparable certified versions and coverage of every earlier certified
operation. Choose a maximal certified version only in the proof, never in admission.
Partition finalized costs into prior held obligations and current-version costs.
Use exact books, actual credits and the fixed-version double-counting theorem to
derive nonnegativity and funded refinement. Prove cancellation/effects exclusion
and safe releases. Keep ideal signature validation, complete payload binding,
physical durability, codec extraction and fairness outside the numeric theorem.

## TEST-2900: Runnable model and rejection evidence

Kernel-check preservation, ancestry, old-certificate coverage, numeric safety and
refinement. Execute root-to-A/B split and M adoption from both branches, spend after
merging, late certificates, owner cancellation/refunds, duplicate histories and
invalid parent-sum allocation. Preserve the partial-renewal counterexample as a
rejected unsafe pattern. Mutated journal, books, version and cancellation guards
must fail real executable or theorem checks. Obtain fresh Orientation and
independent adversarial review; no sorry, custom axioms or native_decide.
Validates: [[SPEC-029-multi-parent-counter-model#REQ-2900]],
[[SPEC-029-multi-parent-counter-model#REQ-2901]].

## Implementation and evidence

The Lean numeric model is implemented in
`lean-cbcl/LeanCbcl/ConsensusFree/MultiParent.lean`, with executable cases in
`lean-cbcl/MultiParentAudit.lean`. The interpreter and specification are model
artifacts; Rust still uses the previously verified single-parent protocol.
The coordinator owns packet-level DAG refinement and Rust integration as follow-on
work, separate from this model's acceptance.

Kernel builds, executable assertions and isolated weakened-guard checks support
[[SPEC-029-multi-parent-counter-model#TEST-2900]]. Fresh Orientation comprehension
and independent cross-model adversarial review accepted the documented scope.
Detailed recorded evidence is [[multi-parent-evidence]], with review outcomes in
[[multi-parent-adversarial-review]] and [[multi-parent-orientation-review]].
These output pages live outside the specs-only vault scan; their resolution is a
vault-integration backlog owned by the coordinator. Pre-existing vault dead links
remain; no clean-vault claim is made.
