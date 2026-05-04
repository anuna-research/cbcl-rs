---
id: SPEC-005
title: Lean Mechanisation of Causal Protocols and Verification Lattice
status: draft
version: 0.1.0
date: 2026-04-28
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-001 (CBCL — homoiconic safe self-extending agent communication, R1–R3 mechanised)
  - SPEC-002 (structural contracts — causal protocols, shapes, R5)
  - SPEC-003 (verification lattice — three-valued result, monotonicity)
prior-art:
  - SPEC-001 Lean 4 mechanisation under lean-cbcl/ (R1, R2, R3 + parser extraction)
  - Conway et al. 2012 (BloomL — lattices in Lean-style theorem provers)
  - Davey & Priestley 2002 (Introduction to Lattices and Order — formalisation reference)
  - Mathlib4 (Order.Lattice, Order.BoundedLattice — Mathlib lattice infrastructure)
  - de Moura & Ullrich 2021 (The Lean 4 Theorem Prover and Programming Language)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-005: Lean Mechanisation of Causal Protocols and Verification Lattice

## Overview

SPEC-001 mechanises CBCL's R1–R3 safety properties in Lean 4 and extracts a verified parser binary. SPEC-002 and SPEC-003 introduce the next layer of behavioural contracts — causal protocol verification, the three-valued result lattice, monotonicity under store growth, and eventual consistency — and prove these properties **informally**, in markdown prose, with property-based and example-based tests in Rust providing empirical evidence.

This specification defines the Lean 4 mechanisation work that elevates the SPEC-002 and SPEC-003 contracts to the same rigour level as SPEC-001. It is a **planning document** — the work it describes is deferred. Its purpose is to make the verification gap visible at requirement granularity, scope the mechanisation effort honestly, and provide a concrete file-by-file plan that future implementers can execute against.

The headline theorem is the SPEC-003 lattice-homomorphism: **`verify : Store × Protocol × Message → Result` is a monotone function from the message-store G-Set lattice to the three-valued bounded lattice `{Unknown, Valid, Violation}`, and joins for `(all ...)` fan-in are preserved.** Mechanising this single theorem closes the largest informal gap in the cbcl-rs theorem inventory.

### Design Provenance

**SPEC-001 precedent.** The existing mechanisation under `lean-cbcl/` proves R1 (no recursion in templates) via DFS-based detection, R2 (resource bounds) via a fuel-bounded evaluator, and R3 (core preservation) via deterministic union. A verified parser is extracted from the proof. SPEC-005 follows the same conventions: Lean 4, Mathlib4 dependency where useful, mirror naming with the Rust implementation (`R1NoRecursion.lean` mirrors `r1.rs`), and one Lean module per Rust module where the proof effort warrants it.

**SPEC-003 prose proofs as the starting point.** The case analysis for monotonicity in SPEC-003 (REQ-304) is the proof skeleton. Mechanisation translates each case into a Lean lemma. The risk is that prose proofs hide load-bearing assumptions; a sympathetic translation will discover them.

**Mathlib lattice infrastructure.** Mathlib4 provides `Order.BoundedLattice`, `Order.Hom.Lattice` (lattice homomorphisms), and finite-set lattice instances. SPEC-005 depends on these rather than re-deriving lattice theory from scratch. ADR-510 records this choice.

### Scope

This specification covers:

- Lean 4 formalisation of the message-store G-Set lattice, the three-valued result lattice, and the lattice-homomorphism property of `verify`
- Mechanisation of the meet/join truth tables in REQ-303 as bounded-lattice instances
- Mechanisation of monotonicity (REQ-304) and eventual consistency (REQ-307)
- Mechanisation of the SPEC-002 R5 sub-checks (acyclicity, reachability, definedness, step-uniqueness) at a level of rigour matching the existing R1 proof
- Mechanisation of REQ-209 and REQ-225 (DCFL preservation under causal protocols and shape constraints)
- A `verified-by:` annotation scheme applied to every REQ in SPEC-002 and SPEC-003

This specification does **not** cover:

- Mechanisation of blame attribution (REQ-230, REQ-232, REQ-233) — implementation-specific, not theorem-shaped
- Mechanisation of the runtime pipeline (REQ-231) — orchestration code, not a theorem
- Mechanisation of shape-checking semantics beyond DCFL preservation (REQ-220–224) — well-covered by property tests
- Verified extraction of a Rust verifier from Lean — orthogonal to the lattice claim, useful but a separate project
- Counted sequences, non-monotonic extensions, or any post-CBCL extension

---

## Functional Requirements

### REQ-510: Three-valued result lattice formalisation

The system SHALL define a Lean type `VerificationResult` with constructors `Unknown`, `Valid`, `Violation` and SHALL prove it forms a `BoundedLattice` (or equivalent Mathlib4 typeclass instance) with:

- `⊥ = Unknown`
- meet `⊓` (`Conjunction`) and join `⊔` (`Disjunction`) instances matching the truth tables in SPEC-003 REQ-303
- the algebraic axioms of a bounded lattice (associativity, commutativity, absorption, identity, idempotence)

The mechanisation MUST discharge each lattice axiom with an explicit case-by-case proof or by `decide` (the result type is finite).

Trace:
- TEST-510
- CON-510

### REQ-511: Message store G-Set lattice formalisation

The system SHALL define a Lean type `MessageStore` modelling the SPEC-003 message-store G-Set with operations `append`, `lookup`, `union`, `subset`. It SHALL prove:

1. `(MessageStore, ⊆)` is a `JoinSemiLattice` with `union` as join
2. `union` is associative, commutative, idempotent
3. `append M S = union {M} S`
4. The lookup function is monotone: `S₁ ⊆ S₂ → ∀ h, lookup h S₁ = some M → lookup h S₂ = some M`

Trace:
- TEST-511
- CON-511

### REQ-512: `verify` monotonicity theorem

The system SHALL prove the central monotonicity theorem in Lean:

```lean
theorem verify_monotone
    (M : Message) (P : CausalProtocol)
    (S₁ S₂ : MessageStore) (h : S₁ ⊆ S₂) :
    verify M P S₁ ⊑ verify M P S₂
```

The proof MUST handle every case in the SPEC-002 verification function: `Single`, `Any`, `All`, `Begin`, missing `:caused-by`, unknown predecessor, invalid predecessor.

Trace:
- TEST-512
- CON-512

### REQ-513: `verify` lattice-homomorphism for fan-in

For `(all p₁ … pₙ)` fan-in, the system SHALL prove:

```lean
theorem verify_all_is_meet_of_components :
    verify M P_All S = (verify M P_p₁ S) ⊓ (verify M P_p₂ S) ⊓ … ⊓ (verify M P_pₙ S)
```

This is the structural form of monotonicity: rather than re-proving monotonicity for each new fan-in shape, monotonicity follows from the lattice-homomorphism via Mathlib's `OrderHom` or `LatticeHom` machinery.

Trace:
- TEST-513
- CON-513

### REQ-514: Eventual-consistency theorem

The system SHALL prove that for any two converging message stores, the verification result converges:

```lean
theorem verify_eventually_consistent
    (M : Message) (P : CausalProtocol)
    (S₁ S₂ : MessageStore) :
    verify M P S₁ ⊔ verify M P S₂ ⊑ verify M P (S₁ ∪ S₂)
```

This is a direct consequence of REQ-512 + REQ-513 if the proof is structured around lattice-homomorphism. It is stated as a separate theorem because eventual consistency is a top-level user-visible claim (REQ-307).

Trace:
- TEST-514
- CON-514

### REQ-515: R5 sub-check soundness theorems

The system SHALL prove, in Lean, the soundness of each R5 sub-check from SPEC-002 REQ-208 at a rigour level matching the existing SPEC-001 R1 proof:

1. `check_acyclicity` returns `[]` iff the dependency graph has no cycle (REQ-204)
2. `check_reachability` returns `[]` iff every step is reachable from `begin` (REQ-205)
3. `check_performative_definedness` returns `[]` iff every referenced performative appears in the defined set (REQ-206)
4. `check_step_uniqueness` returns `[]` iff every `StepDecl` has at most one predecessor entry and no duplicate successors (REQ-207, post-fix). Per-clause predecessor pushes from the `(then …)` parser collapse into the same `StepDecl`, so `predecessors.length ≥ 2` indicates two clauses targeting the same successor with different predecessors — exactly the duplicate-step-declaration case REQ-207 rejects.

Each theorem is stated as the iff form (soundness + completeness). Soundness is mandatory; completeness is preferred but acceptable to defer to a follow-on commit if the DFS/BFS variant proves intractable in Lean (the existing SPEC-001 work has a parallel deferred completeness theorem for the R1 DFS).

Trace:
- TEST-515
- CON-515

### REQ-516: DCFL preservation theorems

The system SHALL prove, in Lean:

1. **REQ-209 (DCFL preservation under causal protocols):** Adding a `(protocol …)` clause to a dialect does not extend the parser power. The proof reduces to: the `(protocol …)` clause is a CBCL S-expression parsed by the existing DCFL parser, and `protocol` is a deterministic dispatch token.
2. **REQ-225 (DCFL preservation under shape constraints):** Same argument for `(shape …)` clauses.

These theorems are conceptually trivial but currently unverified; the audit on the current branch flagged them as gaps. Mechanisation closes the audit.

Trace:
- TEST-516
- CON-516

### REQ-517: `verified-by` annotation in SPEC-002 and SPEC-003

The system SHALL add a `verified-by:` field to every REQ in SPEC-002 and SPEC-003 with one of the following values:

| Value | Meaning |
|---|---|
| `lean` | Mechanised in `lean-cbcl/` with no `sorry` |
| `lean-with-sorry` | Stated in Lean but proof contains `sorry` (transitional) |
| `property` | Property-based test in `crates/cbcl-core/tests/` |
| `example` | Example-based unit test |
| `prose` | Informal proof in spec; no mechanisation, no test |
| `n/a` | Implementation/orchestration requirement; no theorem to verify |

This annotation is a documentation deliverable, completed once at the start of SPEC-005 and updated as Lean theorems land. Each REQ in SPEC-002 / SPEC-003 carries one entry; conflicts (e.g. partial mechanisation) are resolved by listing all applicable values.

Trace:
- TEST-517

### REQ-518: Differential parity with Rust implementation

For every Lean theorem in REQ-510 through REQ-516, the corresponding Rust implementation SHALL be exercised by a property test that asserts the same property at the value level. If the Rust property test passes and the Lean theorem holds, the implementation and the model agree. If they disagree (Rust counterexample found), the discrepancy is a bug in the implementation, the Rust↔Lean translation, or the spec.

The differential parity tests live in `crates/cbcl-core/tests/` and are documented in TEST-518.

Trace:
- TEST-518

---

## Non-Functional Requirements

### NFR-510: Build hygiene

`lake build` in `lean-cbcl/` SHALL complete without error and without `sorry`-warnings for any theorem listed in SPEC-005 once that theorem is marked `verified-by: lean`. CI SHALL run `lake build` on every PR touching `lean-cbcl/` or any of SPEC-002, SPEC-003, SPEC-005.

Trace:
- TEST-550
- OBS-510

### NFR-511: Axiom discipline

The mechanisation SHALL NOT introduce new axioms beyond Mathlib4's standard set. Every `axiom` declaration is forbidden unless explicitly justified in an ADR. `#print axioms <theorem>` for each theorem in REQ-510 through REQ-516 SHALL produce only standard Lean / Mathlib axioms (`Classical.choice`, `propext`, `Quot.sound`).

This is the same discipline applied in the SPEC-001 mechanisation.

Trace:
- TEST-551
- OBS-511

### NFR-512: Proof maintenance cost

When the corresponding Rust implementation changes (verifier function refactor, lattice operation reorder, etc.), the Lean proof MUST be updated in the same PR — the proof and the implementation cannot drift. This is enforced by NFR-510 (CI runs `lake build`) and is a constitutional requirement: a stale proof is worse than no proof.

Trace:
- TEST-552

### NFR-513: Mechanisation time budget

The complete SPEC-005 implementation is budgeted at **2–4 calendar months** of focused Lean work for one experienced contributor, derived from comparable mechanisation efforts (Mathlib lattice instances, the existing SPEC-001 R1 proof took ~3 weeks). This is documented to set realistic expectations; over-runs are escalated rather than silently accepted.

Trace:
- TEST-553 (process gate, not a software test)

---

## Contracts

### CON-510: Three-valued result lattice module

```text
File: lean-cbcl/LeanCbcl/Lattice/Result.lean

namespace CBCL

inductive VerificationResult where
  | unknown
  | valid
  | violation : CausalViolation → VerificationResult

instance : BoundedLattice VerificationResult := ...

theorem result_meet_table : ...
theorem result_join_table : ...

end CBCL

Implements:
  REQ-510

Verified by:
  TEST-510
```

### CON-511: Message store G-Set module

```text
File: lean-cbcl/LeanCbcl/Lattice/Store.lean

namespace CBCL

structure MessageStore where
  messages : Set Message
  indexed_by_hash : ...

instance : JoinSemiLattice MessageStore := ...

theorem lookup_monotone :
  S₁ ⊆ S₂ → ∀ h M, lookup h S₁ = some M → lookup h S₂ = some M

end CBCL

Implements:
  REQ-511

Verified by:
  TEST-511
```

### CON-512: Verify module — monotonicity

```text
File: lean-cbcl/LeanCbcl/Verify.lean

def verify : Message → CausalProtocol → MessageStore → VerificationResult

theorem verify_monotone : ∀ M P S₁ S₂,
  S₁ ⊆ S₂ → verify M P S₁ ⊑ verify M P S₂

Implements:
  REQ-512

Verified by:
  TEST-512
```

### CON-513: Verify module — fan-in homomorphism

```text
File: lean-cbcl/LeanCbcl/Verify.lean

theorem verify_all_is_meet : ∀ M (preds : List Predecessor) S,
  verify M (CausalProtocol.all preds) S =
    preds.foldr (fun p acc => verify M p S ⊓ acc) ⊤

Implements:
  REQ-513

Verified by:
  TEST-513
```

### CON-514: Verify module — eventual consistency

```text
File: lean-cbcl/LeanCbcl/Verify.lean

theorem verify_eventually_consistent : ∀ M P S₁ S₂,
  verify M P S₁ ⊔ verify M P S₂ ⊑ verify M P (S₁ ∪ S₂)

Implements:
  REQ-514

Verified by:
  TEST-514
```

### CON-515: R5 sub-check soundness module

```text
File: lean-cbcl/LeanCbcl/R5.lean

theorem check_acyclicity_iff_no_cycle : ...
theorem check_reachability_iff_all_reachable : ...
theorem check_performative_definedness_iff_all_defined : ...
theorem check_step_uniqueness_iff_no_duplicates : ...

Implements:
  REQ-515

Verified by:
  TEST-515
```

### CON-516: DCFL preservation module

```text
File: lean-cbcl/LeanCbcl/DCFLPreservation.lean

theorem dcfl_preserved_under_protocol : ...
theorem dcfl_preserved_under_shape : ...

Implements:
  REQ-516

Verified by:
  TEST-516
```

---

## Architecture Decisions

### ADR-510: Mathlib4 dependency

**Decision:** Depend on Mathlib4 for `Order.BoundedLattice`, `Order.Hom.Lattice`, and finite-set lattice instances.

**Context:** The SPEC-001 mechanisation is largely Mathlib-free (it can be — R1–R3 are first-order and don't need lattice infrastructure). SPEC-005 needs lattice typeclasses; rebuilding these from scratch would double the proof effort and reproduce well-established Mathlib infrastructure.

**Trade-offs:**
- **Pro:** Mathlib provides battle-tested lattice typeclass hierarchies, automation, and lemma libraries.
- **Pro:** A SPEC-005 contributor with Mathlib experience can move fast.
- **Con:** Mathlib is a large dependency. `lake build` runtime increases significantly.
- **Con:** Mathlib version pinning becomes part of the maintenance surface.

**Rationale:** The marginal proof velocity gain is large enough to justify the dependency. The build-time cost is a developer-experience issue, not a soundness issue.

**Status:** accepted

### ADR-511: Mirror naming convention with Rust

**Decision:** Lean module names mirror Rust module names where the proof corresponds to a single Rust module. New Lean modules introduced by SPEC-005 (e.g. `Lattice/Result.lean`, `Lattice/Store.lean`) live in subdirectories that don't have Rust counterparts but follow the same kebab-case-to-PascalCase convention.

**Context:** SPEC-001 follows this convention (`R1NoRecursion.lean` mirrors `r1.rs`). Maintaining the convention makes it easy to find the Lean proof for a given Rust function and vice versa.

**Status:** accepted

### ADR-512: Soundness before completeness

**Decision:** When a theorem is naturally stated as `iff`, prove the soundness direction first (e.g. `check_acyclicity returns [] → no cycle exists`). Defer completeness (`no cycle exists → check_acyclicity returns []`) to a follow-on commit if it proves intractable.

**Context:** Soundness establishes "the check doesn't lie." Completeness establishes "the check doesn't miss." Both are valuable; soundness is more important for a verifier (false negatives — saying "valid" when it isn't — are worse than false positives — saying "violation" when it is fine, because the latter is detectable at runtime via the user reporting). The SPEC-001 mechanisation has the same structure (R1 DFS soundness is proved; completeness is open).

**Status:** accepted

### ADR-513: Differential parity testing as integration mechanism

**Decision:** Every Lean theorem ships with a corresponding Rust property test that asserts the same property at runtime. This catches Rust-implementation drift from the Lean model.

**Context:** A common failure mode in mechanisation projects is the Lean model and the Rust implementation drifting apart silently — proofs are correct about an abstract model that no longer matches the code. Differential parity catches this.

**Trade-offs:**
- **Pro:** Drift becomes visible immediately on test failure.
- **Pro:** Property tests document the Lean model in Rust, helping non-Lean contributors understand the proven properties.
- **Con:** Doubles the test surface.

**Rationale:** Drift is the single biggest risk for a long-lived mechanisation project. The cost is acceptable.

**Status:** accepted

### ADR-514: Defer extracted-Rust verifier

**Decision:** SPEC-005 does NOT attempt to extract a Rust verifier from the Lean proof. The existing Rust implementation remains the production code; Lean proofs are about the abstract model that mirrors it.

**Context:** The SPEC-001 mechanisation extracts a Lean→native parser binary. The same approach for the verifier is technically feasible but has additional cost: the Lean code needs to be reasonable for extraction (no `decide` over large finite types, careful handling of native types), and the extracted binary needs to be wired into the CBCL pipeline.

**Rationale:** Out of scope for the headline lattice theorem. A separate `SPEC-008-extracted-verifier` (proposed) could pick this up later.

**Status:** accepted

---

## Test Specifications

Each TEST below corresponds to a `lake build` artefact: the named theorem must compile without `sorry`. CI runs `lake build` on every commit and asserts success.

### TEST-510: Result lattice axioms

`lake build LeanCbcl.Lattice.Result` succeeds. `#print axioms` for the bounded-lattice instance produces only standard axioms.

**Technique:** Compile-time, by-decide for finite cases, manual proof for parametric cases.

Trace: REQ-510, NFR-511

### TEST-511: Store G-Set axioms

`lake build LeanCbcl.Lattice.Store` succeeds. `lookup_monotone` discharges without `sorry`.

**Technique:** Compile-time + Mathlib `Set` lemmas.

Trace: REQ-511, NFR-510

### TEST-512: `verify_monotone`

`lake build LeanCbcl.Verify` succeeds with `verify_monotone` proved.

**Technique:** Case analysis over `verify`'s match arms; appeal to `lookup_monotone` (REQ-511) for the key lemmas.

Trace: REQ-512, NFR-510

### TEST-513: `verify_all_is_meet`

`lake build LeanCbcl.Verify` succeeds with `verify_all_is_meet` proved.

**Technique:** Induction over predecessor list; appeal to associativity of meet.

Trace: REQ-513

### TEST-514: `verify_eventually_consistent`

`lake build LeanCbcl.Verify` succeeds with `verify_eventually_consistent` proved.

**Technique:** Direct from REQ-512 + REQ-513.

Trace: REQ-514

### TEST-515: R5 sub-check soundness

`lake build LeanCbcl.R5` succeeds with each soundness theorem in CON-515 proved.

**Technique:** DFS / BFS soundness arguments mirroring the existing R1 proof structure.

Trace: REQ-515

### TEST-516: DCFL preservation

`lake build LeanCbcl.DCFLPreservation` succeeds.

**Technique:** Reduction to the existing DCFL parser theorem.

Trace: REQ-516

### TEST-517: `verified-by` annotations complete

Static check: every REQ in SPEC-002 and SPEC-003 has a `verified-by:` field. CI step in `scripts/check-verified-by.sh` (or equivalent).

**Technique:** Markdown lint.

Trace: REQ-517

### TEST-518: Differential parity

For each theorem in REQ-510 through REQ-516, an idiomatic Rust property test in `crates/cbcl-core/tests/lean_parity.rs` asserts the same property over generated values, with default `proptest` configuration (1000 cases). The CI step runs the parity test alongside the Lean build.

**Technique:** Property-based testing.

Trace: REQ-518

### TEST-550: `lake build` clean

CI step `lake build` produces zero errors and zero warnings for theorems marked `verified-by: lean`.

**Technique:** Build status assertion.

Trace: NFR-510

### TEST-551: Axiom discipline

CI step runs `lean --print-axioms <theorem>` for each theorem in CON-510 through CON-516 and asserts only standard axioms appear.

**Technique:** Static check of Lean output.

Trace: NFR-511

### TEST-552: Proof-implementation parity

When the Rust implementation of `verify`, `MessageStore`, or any other module covered by Lean theorems changes, CI runs `lake build` and the parity tests in TEST-518. PR fails on either failure.

**Technique:** CI enforcement.

Trace: NFR-512

### TEST-553: Time-budget tracking

Process gate: at the end of each calendar month of mechanisation work, the SPEC-005 implementer reports progress against the NFR-513 budget. Over-runs >50% are escalated for stakeholder decision.

**Technique:** Process check, not a software test.

Trace: NFR-513

---

## Observability Signals

### OBS-510: Lean build status

```text
Metric: cbcl_lean_build_status
Type: gauge (0 = success, 1 = failure)
Labels:
  - target: result | store | verify | r5 | dcfl-preservation
```

Emitted by CI on every Lean build.

Trace: NFR-510

### OBS-511: Sorry count

```text
Metric: cbcl_lean_sorry_count
Type: gauge
Labels:
  - module: result | store | verify | r5 | dcfl-preservation
```

The number of `sorry` placeholders in each Lean module. Target is zero for all modules once their corresponding REQ is marked `verified-by: lean`.

Trace: NFR-510, NFR-511

### OBS-512: Axiom dependencies

```text
Metric: cbcl_lean_axiom_count
Type: gauge
Labels:
  - theorem: <name>
```

The number of non-standard axioms each top-level theorem depends on. Target is zero (only `Classical.choice`, `propext`, `Quot.sound` allowed).

Trace: NFR-511

---

## Risk Register

### RISK-510: Mathlib version churn

**Risk:** Mathlib4 evolves rapidly. A SPEC-005 proof may break on Mathlib bumps without warning.

**Mitigation:** Pin Mathlib version in `lakefile.toml`. Plan a quarterly Mathlib-update task that re-runs all proofs and patches breakages. Treat the patch effort as recurring maintenance, not a regression.

**Owner:** SPEC-005 implementer.

### RISK-511: Hidden assumptions in prose proofs

**Risk:** The SPEC-003 prose proofs may rely on assumptions that are false in the Lean model — e.g. that the protocol graph is finite, that `:caused-by` is well-founded, that messages have unique hashes. Mechanisation will surface these.

**Mitigation:** Treat each surfaced assumption as a SPEC-002 / SPEC-003 amendment, not a Lean-side workaround. The amendment process is the value of mechanisation, not a cost.

**Owner:** SPEC-005 implementer + SPEC-002/003 maintainers.

### RISK-512: Implementation-Lean drift

**Risk:** The Rust implementation may evolve (e.g. lattice operation reorder, additional verification cases) without corresponding Lean updates, silently invalidating the proven properties.

**Mitigation:** TEST-518 (differential parity) and NFR-512 (proof and code in same PR). Strictly enforced.

**Owner:** All contributors to the Rust verifier.

### RISK-513: Time-budget overrun

**Risk:** The 2–4 month NFR-513 budget may be unrealistic. Mechanisation projects routinely overrun.

**Mitigation:** Monthly check-in (TEST-553); escalate if behind. Acceptable to pause SPEC-005 partway and ship `lean-with-sorry` markers for the unproved theorems — partial mechanisation is more credible than no mechanisation as long as the gaps are visible.

**Owner:** SPEC-005 implementer.

### RISK-514: Soundness without completeness misleads

**Risk:** ADR-512 defers completeness for `iff`-statable theorems. Readers may misread `verified-by: lean` as a full iff proof when only soundness has been mechanised.

**Mitigation:** When only soundness has been mechanised, mark the REQ `verified-by: lean (soundness only)` — explicit annotation rather than ambiguous status.

**Owner:** SPEC-005 implementer.

---

## Open Questions

1. **Should `Begin` be a primitive or a desugaring?** The Rust `verify` treats `begin` specially (no predecessors required). The Lean proof is simpler if `Begin` is a top-level constructor; cleaner if it's `All []` (vacuous fan-in). Defer to implementer.

2. **How are content hashes modelled?** Real CBCL uses canonical-form SHA-256. The Lean model probably wants an opaque `ContentHash` type with injective `hash : Message → ContentHash`. The injectivity is an *assumption*, not a theorem (cryptographic). NFR-511 should explicitly allow this assumption.

3. **Is `MessageStore` modelled as `Set Message` or `HashMap ContentHash Message`?** The former is closer to the algebraic story (it's a G-Set); the latter is closer to the Rust implementation. ADR-511's mirror principle suggests the latter, but the lattice proof is easier with the former. Probably model as `Set` and add a separate `LookupSpec` for the indexed view.

4. **Do we need `decidable_eq` for `Message`?** The lattice operations need it for finite reasoning. CBCL messages have finite shape (finite S-expressions), so this is provable but tedious. Consider inheriting from a Mathlib instance.

5. **Should we extract the verifier to native code?** ADR-514 defers this to SPEC-008. Confirm with stakeholder before SPEC-005 starts that this is the right deferral.

---

## Future Work

- **SPEC-008 (proposed): Extracted verifier.** Like the SPEC-001 parser extraction, but for `verify`. Would produce a Rust binary or library function generated from Lean code with full proof carryover.
- **SPEC-009 (proposed): Mechanise blame attribution.** Currently out of scope per SPEC-005 §Scope. If REQ-230 / REQ-232 / REQ-233 grow more subtle (e.g. when role-annotated `(any …)` lands per the SPEC-004 future-work pointer), mechanisation may become worthwhile.
- **Mechanise the SPEC-004 demo dialect.** The `sealed-bid-auction` dialect's commit-reveal binding (REQ-412) is structurally a small theorem. Could be mechanised as a worked example demonstrating the SPEC-005 infrastructure on application-level dialects.
- **Cross-prover verification.** Replicate the SPEC-005 proofs in Coq or Isabelle as a robustness check. High cost; consider only if a reviewer specifically demands it.

---

## Status and Versioning

- **Status:** implementing. The IMPL-005 plan delivered the lattice + monotonicity + eventual-consistency theorems, the four R5 sub-check theorems (full iff for REQ-206/207, soundness only for REQ-204/205 per ADR-512), and the DCFL preservation theorems. CI runs `lake build` and the differential parity tests on every commit touching `lean-cbcl/`, SPEC-002, SPEC-003, or SPEC-005.
- **Predecessor:** none.
- **Successor:** none yet.
- **Owner:** Hugo O'Connor.
- **Last updated:** 2026-05-03.

### REQ-510..518 completion (as of IMPL-005 closeout)

| REQ | Status | Lean artefact | Notes |
|---|---|---|---|
| REQ-510 — result lattice | ✅ complete | `LeanCbcl/Lattice/Result.lean` | `BoundedLattice VerificationResult` instance, `result_meet_table` / `result_join_table` truth-table theorems. |
| REQ-511 — store G-Set | ✅ complete | `LeanCbcl/Lattice/Store.lean` | `union_assoc/comm/idem`, `lookup_monotone`. `ContentHash` injectivity recorded as documented axiom (NFR-511). |
| REQ-512 — `verify_monotone` | ✅ complete | `LeanCbcl/Verify.lean` | Discharged across every `verify` match arm. |
| REQ-513 — fan-in is meet | ✅ complete | `LeanCbcl/Verify.lean` | `verify_all_is_meet` proved. |
| REQ-514 — eventual consistency | ✅ complete | `LeanCbcl/Verify.lean` | `verify_eventually_consistent`, derived from `verify_monotone` + `join_mono`. |
| REQ-515 — R5 sub-checks | ✅ complete | `LeanCbcl/R5.lean` | Full iff for all four sub-checks: `check_acyclicity_iff_no_cycle` (REQ-204), `check_reachability_iff_all_reachable` (REQ-205), `check_performative_definedness_iff_all_defined` (REQ-206), `check_step_uniqueness_iff_no_duplicates` (REQ-207). Completeness for REQ-204/205 uses a König-style cycle bound and explicit-path simplification (`ReachableViaPath` + `reachableViaPath_to_simple`); see the section heads in `R5.lean`. |
| REQ-516 — DCFL preservation | ✅ complete | `LeanCbcl/DCFLPreservation.lean` | `dcfl_preserved_under_protocol` (REQ-209), `dcfl_preserved_under_shape` (REQ-225), plus `*_dispatch_deterministic` companions. Proofs are short by design: causal verification and shape checking are post-parse predicates over already-built `SExpr` trees (VPL ⊂ DCFL), so closure reduces to `allSExpr_isSExpr _`, and dispatch determinism reduces to `rfl` because `applyKeywordClause` is a Lean function. The triviality reflects correctness-by-construction — both features were placed at the right layer (post-parse semantics, not parser extension). |
| REQ-517 — `verified-by` annotations | ✅ complete | `scripts/check-verified-by.sh` | Every REQ in SPEC-002 / SPEC-003 carries a `verified-by:` field; lint runs in CI. |
| REQ-518 — differential parity | ✅ complete | `crates/cbcl-core/tests/` | TEST-518 parity tests pair each Lean theorem with a Rust property test. |

Status transitions from here:

- `implementing` → `implemented` once REQ-204 / REQ-205 completeness lands (lifting `dfsNoCycle_complete` / DFS-completeness to the fixed `|names|² + 1` fuel) and the spec-level `verified-by:` for those REQs is upgraded from `lean (soundness only)` to `lean`.

Partial completion is acceptable. The remaining gap is honestly recorded in SPEC-002 REQ-204 / REQ-205 via the `lean (soundness only)` annotation.

---

**END OF SPECIFICATION**
