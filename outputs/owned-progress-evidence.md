# Correct-owner progress: proof and implementation evidence

Date: 2026-11-02. Scope: [[SPEC-034-owned-progress-closure]], following
[[SPEC-033-owned-counter-lifecycle]]. Status: component proofs and concrete
progress repairs implemented; universal owner/product completion remains open.

## Findings and repairs

An honest validator could miss an ancestor adoption, later receive its metadata,
and remain unable to sign the current payment. Retrying only the current payment
was insufficient. Publications now retain transitive act/version/certificate
prerequisites, import them to a fixed point, and perform ordinary journaled
adoptions along a compatible history-covering path. The path may traverse
certified pre-seal ancestors; fresh spending outside the owned root remains
forbidden. Incompatible multi-parent routes are skipped rather than blocking a
compatible route.

A validator could possess an operation certificate the owner had never received.
Returning only an effects vote left the owner without the prerequisite proof for
observed finality. Effects responses now include the operation certificate, and
finalized responses include the retained certificate chain. Owners import public
feedback through the normal verifier without signing a validator decision.

Partially supplied dependencies remain pending. Every successful journal event
is individually durable; failure later in a catch-up service retains its valid
prefix. Restart and retry resume that prefix. Relay input contains public evidence,
not local signing/adoption decisions. Real transaction authentication remains a
separate host layer. Bounds preserve native object/signature limits and pinned
identities rather than imposing an incompatible aggregate manifest limit.

## Formal components

`OwnedProgress.lean` derives import of a finite verified acyclic dependency closure
from an executable fair retry queue. Its retiring execution stops requiring work
only after owner-observed completion. An honest quorum suffices for eventual
owner observation, without requiring delivery of private Byzantine votes.

`OwnerFunding.lean` proves admission/reservation invariants, the equality between
view minus reservations and available funds, and affordability of an accepted
unissued head against full allocation. Final receipt adds credits without charging
the already reserved debit twice. Request and incoming-credit IDs are explicitly
unique and disjoint; authenticated external income is accounted once.

These are component models with stated interface assumptions. They do not yet
prove that every reachable Rust owner/validator execution instantiates those
interfaces. The older conditional finite-batch drain lemma still has stronger
signature-fairness assumptions; it is not a universal runtime progress theorem.

## Independent review

A fresh-context Orientation reader (`progress_orientation`) correctly recovered
the owner-observation, retained dependency, funding and capstone boundaries.
The independent implementation reviewer (`progress_impl_review`, gpt-6-astra)
inspected the actual Rust and Lean changes. Review found and drove fixes to
pre-seal catch-up, cached-target validation, preflight limits and incoming-credit
identity assumptions. Review covers the component results and concrete repairs;
it does not approve an unseen universal completion proof.

## Remaining proof obligations

Compose initialized executable owner, validator and delivery transitions into a
per-admitted-request observed `Complete` theorem. Derive honest signing readiness,
issued-envelope availability, finite drain, seal uniqueness, compatible history,
and phase progress rather than assuming them. Bind the dependency catalogue and
funding state to actual source data. Establish universal Rust correspondence
separately; shared traces and mutations are regression evidence.

Progress is scoped to one correct durable owner history, at most f Byzantine
validators among 3f+1, eventual reliable delivery, fair honest service and journal
commits, retained evidence and sufficient configured capacity. Arbitrary collective
contention, conflicting owners and permanent environmental failure are outside
this claim. No consensus or timeout refund has been introduced.

## Verification

`python3 tools/verify-owned-lifecycle.py --mutations` passed: Lean build,
standard-axiom audits, shared lifecycle oracle, all owned runtime regressions
and real Ed25519/durable journal lifecycle tests. Six Rust behavior mutations
(slot reuse, seal closure, authorization domain, historical fence, skipped
catch-up and one-shot evidence import) were detected. Three weakened Lean
guards (history, dependency readiness and reservation accounting) were rejected
by the kernel. Restored Rust source passed again.

The owned parser suite has 24 passing tests. It includes an early Byzantine
quorum followed by silence, reordered multi-parent ancestry, incomplete evidence,
failed journal writes/restart, cached-target tampering, missing host signatures,
owner certificate feedback and native-limit compatibility. A proposed redundant
structural-check mutation was removed from the negative controls: another
recognizer still rejected its input, so it was not evidence of detection at the
intended seam. The cached-target regression itself passes.

The full Lean library builds (116 jobs). Changed Rust files pass rustfmt and
`git diff --check`. Workspace-wide rustfmt still reports pre-existing differences
in untouched parser/Erlang files; those files were not reformatted here.

Final workspace validation: `cargo test --workspace --offline` passed with
1,570 tests passing and 30 ignored. The initial attempt exhausted disk during
compilation; `cargo clean --profile dev` removed generated artifacts, then the
complete run passed with incremental compilation and debug symbols disabled.
`cargo check -p cbcl-core --no-default-features --offline` also passed.

The workspace emitted its existing macOS Erlang NIF installation notice; no
new compiler warning was reported. The SPEC-034 plan records verified catch-up,
component model and scoped review milestones. The universal capstone is open.

Subsequent composed product completion is recorded in
[[owned-deadlock-proof-evidence]]. Its initialized Lean theorem closes the product
capstone; universal Rust refinement remains a distinct obligation.
