---
id: IMPL-042
title: Boundary Canonicalisation Implementation
status: implemented
mode: reference
---

# Boundary Canonicalisation Implementation

| Field | Value |
|---|---|
| ID | IMPL-042 |
| Title | Boundary Canonicalisation Implementation |
| Governing contract | [[SPEC-042-boundary-canonicalisation#CON-4200]] |
| Next actor | Implementer supplies test evidence; independent reviewer challenges it |

The executable plan is the adjacent `IMPL-042-boundary-canonicalisation.spl`,
loaded in Elephant theory `cbcl-boundary-canonicalisation`.

| Task | Owner | Prerequisite | Acceptance |
|---|---|---|---|
| boundaries | Implementer | Maintainer boundary decision | [[SPEC-042-boundary-canonicalisation#TEST-4200]] through [[SPEC-042-boundary-canonicalisation#TEST-4205]]: regression, migration, integration and deliberate mutation evidence |
| review | Independent reviewer | Boundaries verified | Review boundary coverage, positional preservation, duplicate rejection and migration; resolve findings |
| canonical-proofs | Implementer | Maintainer formal-assurance request | [[SPEC-042-boundary-canonicalisation#TEST-4206]]: kernel proofs, complete-height recursion and allowlisted axiom dependencies |
| canonical-conformance | Implementer; independent reviewer challenges scope | Proofs built | [[SPEC-042-boundary-canonicalisation#TEST-4207]]: direct native/model comparison and deliberately broken native implementations are caught |

Message recognition and the authoring binder normalise once. Serialization and
addressing use the same projection for directly constructed Rust objects. The
generic S-expression encoder and receipt/fold functions remain unchanged.
Dialect creation sorts unordered shape conjunctions, and the signing projection
does the same for direct construction. Checkpoint coordination checks membership
and uniqueness. Existing historical fixtures remain immutable; a new explicit
migration manifest pins current addresses and rendered states.

## Verification

Evidence and independent findings are recorded in
[[SPEC-042-boundary-canonicalisation#Verification status]].
