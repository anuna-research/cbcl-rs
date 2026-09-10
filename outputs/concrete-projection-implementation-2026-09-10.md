Concrete projection refinement — 2026-09-10

Implements the separately authorized concrete-projection follow-up to the earlier
endpoint-projection recommendations. Authentication remains outside this change.

`LeanCbcl/ConcreteProjection.lean` supplies finite Single/Any/All syntax, complete
step records and optional protocol tables. Its algorithm models Rust's actual
Send/Recv loop, including sender precedence and last relevant insertion for duplicate
names, and copies the causal protocol unchanged. Envelope membership is modeled
from already-computed routes; route derivation itself is not proved.

`concreteStore_eq_project` connects concrete map selection to abstract endpoint
store projection. `concrete_verification_agrees` composes that result with the
copied protocol's agreement proof and EPP verification. Explicit premises are
consistent annotations, shared-root visibility, causal locality, safety and closure.
`checkAnnotationsConsistent_iff` supplies an executable consistency checker; no
claim is made that Rust installation currently enforces this condition. Optional
roles prevent unannotated names from acquiring an invented empty-string sender.
The theorem models complete payload stores, not envelope-only stores.

The root-preserving filtered view also satisfies protocol agreement. Legal
predecessor types are interpreted directly from clause references;
`retained_predecessor` connects causal locality to retention. This establishes the
vacuous-splice case, not a generalized rewrite of nonlocal edges. A rooted example
instantiates the composed verification theorem, and a bystander example checks
erasure. Clause evaluation is parametric and does not assert equivalence with the
deployed eager verifier.

The live Rust/Lean test calls production `project`, serializes its actual output
as Lean values, and uses kernel `decide` to compare against Lean computation. The
144 fixtures include four projections of one R6-clean rooted chain (two declared
roles and two absent-role totality cases), duplicate annotation cases,
self-addressing, missing annotations, empty/Unicode names, all clause variants,
optional/empty tables, and role/cast/occupant envelope gates. The clean cases also
check annotation consistency. This is source transcription evidence, not a proof
of Rust compilation or all Rust inputs. CI explicitly runs this otherwise ignored
test after building Lean. A Rust unit test pins the exact-single-root hash typing
exception; other single references and multiple references are unchanged.

Validation:

- `lake build`: passed (78 jobs).
- `lake exe runLinter LeanCbcl`: passed.
- `scripts/check-axioms.sh`: passed (71 theorems, allowlisted axioms only).
- `scripts/check-verified-by.sh`: passed.
- `cargo test -p cbcl-core --test projection_refinement -- --ignored`: passed,
  144 kernel-checked fixtures.
- `cargo test -p cbcl-core --lib projection::tests`: passed, 30 tests.
- Mutation checks rejected both dropping the protocol and suppressing Send
  insertion with a Lean/Rust mismatch; production code was restored afterward.
- `git diff --check`: passed.

README, EPP scope comments, manuscript and SPEC-014/016 now distinguish these
results from remaining obligations: deployed message/eager-verifier refinement,
cast/seal compatibility, derived-envelope delivery, authentication and generalized
nonlocal splicing. TEST-630 serialization roundtrip remains explicitly outstanding.
The earlier implementation report is historical and describes the preceding patch.

Fresh-context review by `/root/review_concrete_projection` found no remaining
internal gap after adding concrete store composition, optional-role semantics,
root preservation and the inhabited examples. The reviewer confirmed the remaining
installation applicability gap: conflicting duplicate annotations are not rejected
by installation and therefore are outside the theorem's explicit premise. Changing
installation policy is not part of this proof refinement. The updated manuscript
also compiles with pdflatex (font-cache access required an approved sandbox retry).
