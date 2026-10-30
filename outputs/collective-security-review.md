# Collective security review

Disposition: no unresolved implementation blocker found after the reserved resource identity fix. This is an independent adversarial review of the uncommitted collective extension on state-rules-spec over a992286. Tier 1 human security review remains a production deployment obligation; this report does not replace it.

Trace: [[SPEC-027-collective-bounded-counters#REQ-2700]], [[SPEC-027-collective-bounded-counters#REQ-2701]], [[SPEC-027-collective-bounded-counters#CON-2701]]. The implementation owner acts on this report by retaining the regression and completing the remaining workspace validation.

## Resolved finding: reserved resource scope admitted as an actor

The original collective context accepted a programmatically constructed root cast containing seller `$collective`. The textual lexer rejects `$`, but `SExpr::Atom(Atom::Symbol(...))`, cast reconstruction, and the public message/act APIs did not enforce that restriction. As a result the resource sentinel entered `actors`, and `checkpoint_request(manifest)` could generate a signing request whose actor was the resource sentinel. This violated the declared actor/resource separation even though the examined charge accounting still used one pool and no capacity inflation was demonstrated.

The implementation now rejects a collective cast containing the sentinel before creating the context. The reviewer reproduced acceptance in an isolated source copy with only that new guard removed, then reproduced rejection in the fixed source using a separate fresh Cargo target directory. The narrow retained probe is [[collective-reserved-scope-probe.rs]]; append it to a temporary copy of the quorum runtime integration test to reuse its fixtures. The production regression `collective_reserved_resource_scope_cannot_be_an_authenticated_actor` also passed.

Observed mutant command: `CARGO_TARGET_DIR=/private/tmp/cbcl-bounded-counter/target cargo test --manifest-path /private/tmp/cbcl-collective-review-isolated/Cargo.toml -p cbcl-parser --test collective_review_probe review_reserved_pool -- --nocapture`. The acceptance assertion passed. A subsequent shared-target run was discarded because the mutant build reused the same artifact location. Source files in the reviewed worktree were never mutated by the reviewer.

Observed fixed command: `CARGO_TARGET_DIR=/private/tmp/cbcl-review-fixed-target cargo test -p cbcl-parser --test collective_review_probe review_reserved_pool -- --nocapture`. The rejection assertion passed after a fresh dependency/core build. The temporary duplicate integration test was removed after validation.

## Other reviewed paths

Signer changes do not create independent budgets: actor-to-resource resolution precedes epoch ownership checks; local charges accumulate by shared epoch; active epoch lookup and finalized debits use the resource account. Signed acts retain the actual actor. Increment authority is checked against actor issuers independently of business role admission. Cancellation votes are checked against `op.act.signer`, while collective checkpoint requests require a cast actor admitted by an operation role. Full sealed candidate inclusion, monotone cumulative held/refunded/credited sets, and one-successor choices remain enforced by the existing protocol.

Collective genesis rejects negative/noninteger rights, over-ceiling initial rights, malformed root/predecessor context, and unauthorized opener roles. Structural shape recognition enforces numeric bounds. Account mode retains canonical ownership omission, the old initial-rights representation, and tuple-shaped JSON transfer serialization through `Some(tuple)`. Removing the new ownership member from an account rule successfully deserializes to the default. Caller role caches are reconstructed for context creation and certified intent construction; actual authorization uses pinned genesis.

Independent execution: `CARGO_TARGET_DIR=/private/tmp/cbcl-review-fixed-target cargo test -p cbcl-parser --test quorum_runtime` completed successfully, including the new reserved identity, malformed genesis, JSON declaration, shared spending, cancellation/refund, late-certificate, ceiling, cache substitution, and account compatibility cases. Workspace-wide and no_std/serde checks remain the implementation owner's validation responsibility.

## Lean scope

[[Collective.lean]] specializes the existing Currency configuration to `Fin 1` resource ownership and independent `Fin K` actors. The authorization predicate retains actual-actor signature and role checks and applies the issuer predicate to `actor tx` for minting. Setting the generic pool issuer predicate to true is sound here because the actor-specific mint check is already conjoined into `ownerSigned`. Resource source equality follows from the singleton resource type; the refinement, nonnegativity, floor, and ceiling results reuse the existing generic protocol assumptions. `lake build LeanCbcl.ConsensusFree.Collective` completed successfully after the implementation owner's explicit dimension/namespace fixes.

Cancellation signer identity and checkpoint proposer roles are Rust restrictions tested at the runtime boundary, not explicit actor-specific theorems of this adapter. Signature validity, role admission, and genesis headroom correspondence are modeled inputs, not verified cryptography or parser extraction. The adapter proves the declared specialization; it does not prove Rust correspondence, consensus recovery, multi-parent merges, or liveness under contention.
