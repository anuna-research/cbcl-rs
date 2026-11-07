---
title: Protocol model
mode: explanation
---

# Protocol model

This page states the whole interaction model as one theorem over sets and functions, then lists the Lean declaration behind each claim. Every citation below was checked against the statement in `lean-cbcl/` at the time of writing; where the Lean result is weaker or differently shaped than the prose, the gap is named rather than smoothed over.

The stages follow the diagram in the README: full recognition, record sets, citations, the three-valued check, admission, and derived state.

## Definition (interaction model)

Fix an alphabet Σ and an installed environment E. The model consists of:

```text
L_E ⊆ Σ*                            language recognised by E
h    : L_E → H                       content address
from : L_E → K                       claimed signer
cites: L_E → ℘(H)                    the :caused-by references
auth : L_E → {0,1}                   host authentication of from(m)
cast_t : Role → ℘(K)                 the cast fixed at the root of thread t
P                                    the causal protocol of the dialect in scope
verify : L_E × P × ℘(L_E) → V        V = {Violation, Unknown, Valid}
f_D  : ℘_fin(L_E) → State            the state rules of dialect D
```

For a finite set S ⊆ L_E define the admission operator on ℘(S):

```text
Φ_S(X) = { m ∈ S | auth(m) = 1
                  ∧ from(m) ∈ cast_t(role(m))
                  ∧ cites(m) ⊆ h(X)
                  ∧ verify(m, P, X) = Valid }
```

and set `A(S) = lfp Φ_S` and `σ(S) = f_D(A(S))`.

## Hypotheses

- **H1, recognition.** Membership in L_E is decided by a deterministic pushdown recogniser that consumes the whole input.
- **H2, addressing.** h is injective on L_E.
- **H3, authentication.** `auth(m) = 1` only if the key behind `from(m)` signed the attestation of h(m). The core takes this as a host-supplied predicate.
- **H4, verdicts.** verify is monotone under the knowledge order (`Unknown` below the two incomparable terminal verdicts), `S₁ ⊆ S₂ ⇒ verify(m,P,S₁) ≤ₖ verify(m,P,S₂)`, and merge-consistent, `verify(m,P,S₁) ⊔ verify(m,P,S₂) ⊑ verify(m,P,S₁ ∪ S₂)`.
- **H5, state rules.** f_D depends on its argument only as a set: invariant under permutation and duplication.
- **H6, installation.** `E ⊕ D` is defined only when D passes R1 to R3 and is fresh, and dispatch into D is by a prefix-free `lang` token.

## Theorem (interaction protocols over sets of recorded speech acts)

Under H1 to H6, for every participant i whose received inputs are x₁, x₂, … ∈ Σ*:

1. **Records form a set.** `S_i = { x_k | x_k ∈ L_E }` is independent of the order and multiplicity of the x_k. Merging two participants' records is `S_i ∪ S_j`, which is associative, commutative and idempotent.
2. **Admission is well defined and monotone.** Φ_S is monotone on ℘(S), so `A(S)` exists, is reached by finitely many iterations from ∅, and `A(S) ⊆ S`. An act once accepted stays accepted as S grows.
3. **State is a function of the accepted set.** `σ_i = f_D(A(S_i))`, and `A(S_i) = A(S_j)` as sets implies `σ_i = σ_j`.
4. **Terminal verdicts are stable.** If `verify(m,P,S)` is `Valid` or `Violation` then `verify(m,P,S')` is the same verdict for every `S' ⊇ S`. Only `Unknown` can change, and it can resolve either way.
5. **Recognition survives extension.** For any finite sequence of admitted installations, `L_{E ⊕ D₁ ⊕ … ⊕ Dₙ}` is a DCFL, and every declaration of E is still present in `E ⊕ D`.
6. **Replicas converge.** Two replicas that eventually receive every act of a finite valid history, and that fairly schedule enabled acceptances, have accepted sets equal to that history from some time on, and from then their derived states agree.

## Proof sketch

1. By H1 the predicate `x ∈ L_E` is total, so S_i is a filtered image. The merge laws are those of set union.
2. Each conjunct of Φ_S is monotone in X: the citation condition grows with X by inclusion, and `verify(m,P,X) = Valid` is preserved under X ⊆ X' by H4. ℘(S) is finite, so the least fixed point exists and Kleene iteration reaches it in at most |S| steps.
3. Apply H5 to A(S_i).
4. The only store-sensitive branch of verify is a single citation whose lookup succeeds; by H2 the larger store returns the same witness, so the verdict is unchanged. Fan-in and fan-out are strong Kleene meet and join, which are monotone in the knowledge order.
5. The core grammar is LL(1). Each installation is a deterministic union made safe by the prefix-free dispatch token of H6, which avoids the general non-closure of DCFLs under union. Induction on the number of installations gives the DCFL property.
6. Eventual receipt plus fairness drives every act of the history into each accepted set; acceptance is never retracted; equal accepted sets give equal states by claim 3.

## What the Lean development proves

Paths are under `lean-cbcl/LeanCbcl/`.

| Claim | Lean declaration | What it states | Gap from the prose |
|------:|------------------|----------------|--------------------|
| 1 | `merge_associative`, `merge_commutative`, `merge_idempotent`, `merge_setEq` in `StateKernelSEC.lean` | `merge` of act lists is a set union up to `SetEq` | none |
| 1 | `step_received`, `step_accepted` in `StateKernelDelivery.lean` | receipt and acceptance persist across every execution step | none |
| 1, H1 | `IsRealtimeDCFL` in `FiniteDPDA.lean`; `InstalledSyntax.environmentDCFL`; `Raw.check_correct` in `InstalledLexer.lean` | a finite real-time DPDA whose acceptance is equivalent to the declared language, over all words including malformed ones, with the executable checker proved to agree | the lexer is the spec's definition of the lexical language, not a proof against the Rust parser |
| 2 | `Admission`, `Admission.admit` in `AdmissionStratification.lean` | admission is a shape stage on one act plus a causal stage over accepted skeletons, returning `accepted`, `pending` or `rejected` | the least-fixed-point form above is a description of the monitor, not a Lean definition |
| 2 | `r7Admission_sticky` | an `accepted` verdict survives store growth for the deployed admission form | monotonicity is proved for `r7Admission`, not for an arbitrary `Admission` |
| 2 | `admit_ignores_data`, `fold_reads_data` | admission never reads state fields; a state rule does | none |
| 3 | `fold_perm_invariant`, `fold_dedup_invariant` in `State.lean` | every data rule is a set function of the accepted acts under `NodupAddr`; inserting a present act is the identity | stated per rule; protocol progress is in `StateProgress.lean` |
| 3 | `strong_convergence`, `clause_strong_convergence`, `duplicate_observation` in `StateKernelSEC.lean` | `SetEq` accepted lists with unique addresses give `Equivalent` observations for every expression and compiled clause | requires a shared evidence `Context` that respects set equality |
| 4 | `verify_monotone`, `verify_eventually_consistent`, `verify_all_is_meet` in `Verify.lean` | monotone and merge-consistent under the valid-is-sticky preorder `⊑`; `all` is the meet | `⊑` is `a ⊑ b ↔ (a = valid → b = valid)`, so this theorem alone says nothing about `Violation` |
| 4 | `verify_knowledge_monotone`, `verify_valid_stable`, `verify_violation_stable` in `VerifyKnowledge.lean` | monotone under the flat knowledge order `kle` of `Lattice/KnowledgeOrder.lean`: a terminal verdict on S is the verdict on every S' ⊇ S, and only `Unknown` can move | none; this is SPEC-003 REQ-302 as stated |
| 5 | `InstalledSyntax.dcfl_preserved_many`, `accepted_installations_dcfl`, `verified_fresh_installations_dcfl` in `InstalledDCFL.lean`; the `Raw` versions in `InstalledLexer.lean` | DCFL membership of the token language and the raw Unicode-scalar language after any finite installation sequence, for any admission policy | Rust's additional admission gates are not modelled as equivalent |
| 5 | `previous_declarations_preserved`, `fresh_names_preserved`, `verified_sequence_unique` in `InstalledDCFL.lean` | prior declarations survive installation; freshness keeps names unique | none |
| 5 | `r7Store_isTraceDCFL` in `AdmissionStratification.lean`; `R6DCFLPreservation.lean` | the accepted store trace language is regular, hence DCFL | the R6 model follows `verify_causal` branch by branch; the file discloses where it idealises |
| 6 | `eventual_acceptance`, `eventual_dissemination`, `finite_history_stabilizes`, `strong_eventual_consistency` in `StateKernelDelivery.lean` | under the `Replica` premises, every valid act is eventually accepted, reaches other replicas, accepted sets stabilise to the history, and observations agree at all late times | conditional on `ValidHistory` (finite lower-ranked dependencies, dependency-based admission, no false rejection) and on `Replica` (eventual receipt, fairness, `auth` as a premise) |

Two declarations that sound relevant are not what their names suggest. `dcfl_preserved_under_protocol` and `dcfl_preserved_under_shape` in `DCFLPreservation.lean` prove only that those clauses are built from S-expression constructors; the file says so itself. The DCFL results are the `InstalledSyntax` ones in the table.

## Discharging the hypotheses

H1, H4, H5 and H6 are theorems in the table above. The remaining items are of three kinds: hypotheses that a host must discharge, correspondence between Lean and Rust, and a model that is deliberately outside this theorem.

**H2 and H3 are parameters, not gaps in a proof.** `verify_knowledge_monotone` uses `MessageStore.lookup_monotone`, which needs the same witness for the same address in the larger store, so a content-hash collision would break claims 2 and 4. `Replica` takes `auth : Act → Prop` as a premise, so claims 3 and 6 hold for whatever `auth` the host supplies. Discharging them means: a collision-resistant hash for H2, and for H3 a binding from each key identity to key material that the host checks before passing a signer to the core. The core keeps no key directory, so today that binding is a host configuration; the alternative is to make identities self-certifying by letting the name part of `@suite:name` be the encoded public key, after which the root cast carries the binding and H3 reduces to signature verification. That choice is open; see the identity paragraph in the README.

**Rust correspondence is tested, not proved.** The Lean models are checked against the Rust implementation by differential tests rather than extraction: `crates/cbcl-core/tests/monotonicity_tests.rs` checks that `Valid` stays `Valid` and `Violation` stays `Violation` under store growth, `crates/cbcl-core/tests/lean_parity.rs` checks the verdict lattice tables and the preorders against `Lattice/Result.lean`, `crates/cbcl-core/tests/eventual_consistency_tests.rs` checks merge behaviour, `crates/cbcl-parser/tests/admission_state_free.rs` checks that the Rust admission has the stratified form of `AdmissionStratification.lean`, and `test-vectors/state/` fixes fold outputs that both sides must reproduce. The Lean README states that neither the Rust parser nor the installation gates are proved equivalent to the Lean recogniser.

**Bounded resources are a separate model.** They add a resource check to Φ_S. `BoundedCounter.lean` proves local conservation and the floor and ceiling bounds (`increment_conserves`, `decrement_conserves`, `transfer_conserves`, `transfer_headroom_conserves`, `floor_preserved`, `ceiling_preserved`, `both_bounds`). The consensus-free quorum profile is modelled in `ConsensusFree/`, with its own safety and liveness results under a pinned validator roster. What neither proves is merge safety of the account-ownership resource DAG without certification: `escrow.rs` states that a `ready` verdict is conditional on non-forking issuance by the host's gate. That is the condition under which claim 3 extends to balances.
