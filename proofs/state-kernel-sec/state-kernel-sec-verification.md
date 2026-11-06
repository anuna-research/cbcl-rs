# State-kernel strong eventual consistency verification

Implements [[SPEC-037-state-kernel-sec]] through [[IMPL-024-state-kernel-sec]].
Branch: `draft/state-register-semantics`; parent: `66a129b`.
Date: 2026-11-06. Steward: Codex `/root`.

## Established results and premises

Strong convergence ranges over every typed expression constructor and arbitrary
compiled field lists, using unique-address accepted histories. Observations agree
extensionally: sets by membership, maps by supported keys and reads, histograms by
support/counts, and scalar/tagged results by equality. Equal histories may have
different list order. Replacement, domains and arbitration retain existing semantics.

One shared immutable Context supplies decoding, signer order, installed protocol
context and causal/resource evidence providers. Port laws require the same provider
to return the same evidence for equal accepted sets. This is not a resource
classification/finality proof. Independently extensional but different providers
would not suffice, and are not what the theorem assumes.

The existing StateRefinement execution relation supplies receive, duplicate,
accept, reject, wait and idle transitions. A ValidHistory specifies finite
prerequisites closed in the common history with strictly lower natural ranks.
Admission must not reject valid acts before dependencies arrive; once dependencies
are accepted it must accept in every valid accepted superset. A Replica supplies
that Behavior, no extraneous receipts, eventual receipt of each valid act, and
weak fairness for continuously pending/admitted acts on every time suffix.

Fairness is about actual acceptance-labelled transitions, not eventual accepted
membership. The proof establishes pending-or-accepted, acceptance persistence,
finite dependency completion, and eventual incorporation by rank induction.
An act accepted at one compliant replica eventually reaches every other one.
A finite complete history then gives a single stabilization time. At arbitrary
later times both replicas have equal accepted sets and observations.

Union laws are associative, commutative and idempotent modulo accepted membership.
They do not reconcile conflicting addresses or establish admission-preserving
runtime merge. Address consistency follows from existence of compliant Replica
executions: receipt forbids address conflicts and delivery covers the intended history.

The nonempty witness delivers the dependent child first, then its parent, then
accepts both. A second legal execution receives both and idles forever; it fails
fairness and accepts neither. Growing unique-address tick snapshots have a count
that never stabilizes. This last example is a snapshot sequence, not a fully
instantiated infinite Replica execution.

## Executed checks

Commands and source fingerprints are recorded in `checks.json`; deliberate
semantic failures are in `mutations.json`.

- Lean library build and linter, including new examples.
- Central axiom audit plus inspection that new capstones use standard axioms only.
- Isolated mutations: dropping an accepted act during interpretation; discarding
  current history during merge; acceptance forgetting prior acts; acceptance
  labels which never insert their candidate. Each invalidates formerly passing
  correctness proofs. Missing imports or parse errors do not count as kills.
- Diff whitespace, requirement links/anchors and USDD specification lint.
- Zetl retains pre-existing dead links/SPL errors; no new originating errors.

No runtime code or wire format changes. Existing Rust validation is separate
from these typed Lean consistency proofs. There is no transport, production
scheduler, resource-finalization, rendering or universal business-progress claim.

## Independent review and comprehension

Reviewer `/root/whole_kernel_spec_review` checked SPEC-037 and all three new Lean
modules. It found a contract ambiguity about individually extensional providers;
the implementation uses one shared Context, and documentation now states that
cross-replica coherence explicitly. It checked transition fairness, continuous
enabling, no false rejection, dependency rank induction, completion times and
nonvacuity. No proof-design blockers remained. Subsequent review accepted merge,
dissemination and tick additions with the qualifications recorded above.

Reviewer `/root/hlc_orientation_check` initially inferred that a replacement
reference creates an admission dependency. This exposed ambiguous prose. The
Orientation now explicitly describes a required causal predecessor and says
replacement references alone do not block admission. Its second Orientation-only
review correctly predicted finite completion, ongoing writes, and all premises
and exclusions. No ambiguity remained. Reviews were read-only and performed no
builds; they are independent tool sessions under one steward, not separate
cryptographic Elephant peers.

Planning theory `spec-037`:
`ca5a6163419e50225c610e24bb523e0e5bcc7522503aed512629c4bb82e356bf`.
The ephemeral local store is not relied on for durable evidence; this committed
plan and verification record preserve the outcome.
