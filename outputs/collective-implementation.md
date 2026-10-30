---
title: Collective bounded counter implementation evidence
mode: reference
status: implemented-library
---

# Collective bounded counter implementation evidence

[[SPEC-027-collective-bounded-counters]] extends the Rust runtime from a992286 with
collective ownership. Distinct actors authorize ordinary business messages while
costs, credits, epochs, manifests and local signing charges belong to one pool.
The existing consensus-free single-parent protocol is reused. Multi-parent version
merges and consensus recovery are not implemented.

## Behavior and compatibility

Ownership defaults to account and canonical omission preserves existing hashes.
Collective declarations require quorum-budget, scalar initial rights, explicit
roles, and increment/decrement mappings without account allocation/transfer options.
An optional ceiling derives pool headroom from genesis. Account transfer tuples are
now optional internally; their JSON representation remains compatible.

Genesis reconstructs casts and caches, checks scalar amounts and ceiling, and
rejects the reserved pool identity as an actor. Certified intent reconstruction
also ignores forged Instance caches. Every operation retains its original signer.
Issuer authority is checked against that actor, independently of the shared scope.
Cancellation requires that actor's signature. Checkpoint authorization permits cast
actors admitted by an operation role and still requires complete sealed journals,
exact cumulative accounting and distinct authenticated quorums.

Collective Rust views contain one resource-map entry and render scalar rights and
optional headroom with ownership collective. Completeness remains unknown. Signing,
authentication, protocol admission and physical durable journals remain host layers.

## Executed checks

| Requirement | Evidence | Result |
|---|---|---|
| Shared pool and real-actor authorization | `collective-runtime-tests.log`; concurrent sellers, finality timing, direct received role/issuer attacks | Pass |
| Safe lifecycle | Cross-actor refunds, late effects, recovery, storage failure, stale CAS, shared successor choice | Pass |
| Declaration and compatibility | Invalid ownership/options, JSON/text, explicit account hashes, legacy serde, malformed genesis and cache substitution | Pass |
| Retained account behavior | `collective-workspace-tests.log`; full workspace with all features | Pass |
| no_std / serde | `collective-no-std.log`; core with serde and parser without default features | Pass |
| Behavioral sensitivity | `collective-mutations.json` and per-mutant logs; compiler failures do not count as killed Rust mutants | Pass |
| Lean specialization | `collective-lean.log`, `collective-lean-audit.log`, `collective-lean-workspace.log` | Pass |
| Independent adversarial review | [[collective-security-review]] | No unresolved blocker reported |
| Orientation comprehension | [[collective-orientation-review]] | Pass |
| Spec lint | `collective-spec-lint.log` | No errors or warnings |

The red gate in `collective-red-gate.log` executes the new cases against the old
recognizer and fails on unsupported ownership. The mutation runner uses a temporary
source workspace and separate target directory. It preserves the legacy guard
mutations and adds shared actor charging, cancellation identity, checkpoint role
and reserved resource identity mutations. Every mutated behavior produces an
executed assertion failure. Final source hashes are in `collective-checks.json`.

Independent review found that typed casts could admit the reserved resource scope
as a key despite the textual lexer rejecting it. An isolated guard mutation
reproduced acceptance, and the fixed fresh build rejects. The maintained regression
covers the typed/serde path. The reviewer discarded an ambiguous shared-target build;
final main-workspace validation follows a core cache clean, and independent final
checks use a separate fresh target. No mutated source was installed in the worktree.

Clippy completes with pre-existing warnings elsewhere; no new warnings are reported
for changed ownership/runtime/test code. The specs-only vault scan retains existing
cross-vault links plus the evidence link outside its scan root. The maintainer owns
vault-root unification; requirement/contract/test links resolve.

## Lean and proof limits

`LeanCbcl/ConsensusFree/Collective.lean` separates `Fin K` transaction actors from a
single `Fin 1` resource owner. Actual-actor signature, role and mint issuer predicates
feed the existing generic configuration. Theorems establish shared source, actor
policy, finite asynchronous refinement, resource nonnegativity and floor/ceiling.
`CollectiveAudit.lean` kernel-checks the two-actor 100 minus 3 minus 2 trace and role/
issuer rejection. Its axiom audit uses only the existing standard Lean axioms.

Actual cancellation-signer and checkpoint-proposer restrictions are tested Rust
strengthenings of the generic model, not new actor-specific adapter theorems.
Signature verification, role admission and genesis bindings remain modeled inputs.
Rust extraction/correspondence and multi-parent/liveness proofs are not supplied.
Human security review remains required before a production deployment; this change
implements a local library feature and deploys no validator service.
