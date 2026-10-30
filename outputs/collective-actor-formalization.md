---
title: Collective actor protocol formalization
mode: reference
status: implemented-proof
---

# Collective actor protocol formalization

[[SPEC-028-collective-actor-refinement]] adds an explicit executable actor protocol
over the existing consensus-free resource engine. This pass changes Lean, specs,
documentation and validation artifacts only. Rust remains at b5b4c6d.

## Model and derived properties

`CollectiveProtocol.lean` defines actor-or-pool identities, typed request payloads,
instance domains, concrete cast/role tables, ideal signature verification and
per-validator canonical request receipts. Manifest authorization is computed from
eligible authenticated proposers rather than supplied as an authorized flag.
Genesis admission checks actual initializer authority and binds derived headroom to
the declared cap. A pool identity has no signing key. Context and payload tables
remain immutable throughout an execution.

`ControlInvariant` and its initialization, step and run theorems preserve valid
receipts and honest vote provenance. Honest cancellation fences retain both the
original operation and its signer's cancellation request. Honest checkpoint votes
retain eligible proposer requests. Quorum theorems obtain an honest receipt holder
from quorum intersection, establishing actual actor/role/phase authorization.
Byzantine validators retain generic receipt-free behavior; the partition is the
existing at-most-f fault model, not an extra trusted signing restriction.

`execute_erases` and `run_erases` map protocol actions to generic transitions and
receipt/rejection events to stuttering. `admitted_run` supplies provenance, generic
reachable-state invariants and funded business refinement. `infinite_refinement`
covers every index of an arbitrary actual execution, without fairness or liveness.
No signing guard tests a global business balance. Numeric safety comes from the
existing local-budget/cross-epoch theorem.

`declared_cap_bound` derives exact genesis resource sum from an admitted cap check;
`declared_ceiling` combines conserved resource sum with nonnegative headroom.
`declared_floor` follows nonnegative rights. Signed floors/caps may be negative;
rights and headroom remain nonnegative. Raw initialState/resource lemmas alone do
not establish genesis authorization or cap admission.

`released_cannot_finalize`, `receipt_run_mono` and
`honest_successor_choice_persists` retain cancellation and journal guarantees across
arbitrary future events. `recover_control` validates abstract complete-log replay
from admitted genesis. `replay_same_log` states determinism, not physical durability
or reconstruction of missing records. Abstract logs include rejected attempts;
Rust journals reject corrupt acknowledged records and use different representations.

## Executed validation

| Check | Evidence | Result |
|---|---|---|
| Full module proof build | `collective-actor-lean.log` | Pass |
| Library build | `collective-actor-workspace.log` | Pass |
| Owner/role/issuer/genesis and funded traces | `CollectiveActorAudit.lean`, `collective-actor-audit.log` | Pass |
| Imported independent adversaries | `CollectiveActorAdversarialReview.lean`, `collective-actor-independent-import.log` | Pass |
| Independent theorem/axiom audit | `CollectiveActorProofReview.lean`, `collective-actor-review-axioms.log` | Pass |
| Executable guard mutations | `check_actor_review_mutations.py`, `collective-actor-review-mutations.json` | Pass |
| Blinded comprehension | [[collective-actor-orientation-review]] | Pass after clarification |
| Independent design/proof review | [[collective-actor-adversarial-review]] | No blocking structural finding |

The audit kernel-checks concurrent seller receipts/finality, actual issuer checks
independent of operation role, signed negative-floor/cap cases, wrong actor/domain/
pool identities, cross-actor cancellation-refund checkpoint installation, subsequent
spending and attempted old finality. It checks raw remaining rights 95 and displayed
value 85 for floor -10, avoiding confusion between inventory and bounded value.
The reclamation trace leaves rights 40 and headroom 70 after a cancelled old spend,
a refund checkpoint by the other seller and a new finalized spend.

The mutation runner extracts actual executable declarations into temporary files
and appends independent kernel-checkable propositions. It requires a successful
baseline and false-decide failures for every guard mutation; type/import failures
or surviving mutants fail its exit status. Mutations cover local operation/cancel/
checkpoint receipts, cancellation signer, instance, checkpoint role, genesis cap
and signature payload phase. Standard axiom output is limited to propext,
Quot.sound and Classical.choice. No sorry, custom axioms or native_decide are used.

## Rust comparison and limits

The independent review maps model admission to retained Rust candidates, original-
signer fences, eligible checkpoint requests and existing journal/quorum checks.
It identifies representation differences: Rust stores the first accepted proposal,
while the model retains all eligible canonical request identities; Rust has local
certificate bytes and journal acknowledgments, while the model uses abstract
system evidence. No exact executable Rust/model equivalence is claimed.

Ideal verified signatures and identifiers bound to complete immutable payloads are
inputs. Rebinding a domain to different data is outside the model. Crypto, codecs,
physical durability, storage pruning and complete/latest balance reads are not
proved. No consensus, multi-parent merge, timeout unlock or liveness claim is added.
Human security review remains a production-release obligation. No deployment occurs.
