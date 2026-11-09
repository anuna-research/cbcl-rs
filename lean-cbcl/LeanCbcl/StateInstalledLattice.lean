import LeanCbcl.StateInstalledClause

/-! Source-coherent installed lattice metadata. The displayed source and each
raw threshold query are generated from the same stored contribution function.
A freeze decorates the source observation; native factored queries still fold
that source's current raw carrier, while checking the decorated source's fault
channel first. -/
namespace CBCL.StateInstalledLattice
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler

/-- An installed state source and its metadata. -/
structure Field (V : Type) where
  /-- The lattice carrier used by this source. -/
  Carrier : Type
  /-- The join and bottom operations, with their lattice laws. -/
  algebra : BoundedJoinSemilattice Carrier
  /-- Decidable equality for carrier elements. -/
  equality : DecidableEq Carrier
  /-- The lattice element contributed by one accepted act. -/
  contribution : Act → Carrier
  /-- Render the retained carrier as the displayed value. -/
  project : Carrier → V
  /-- Render a threshold element in the author-facing value type. -/
  renderElement : Carrier → V
  /-- Decode an author-facing threshold element, rejecting unsupported values. -/
  decodeElement : V → Option Carrier
  renderDecode : ∀ q, (letI := algebra; q ≠ ⊤) → decodeElement (renderElement q) = some q

/-- Fold source contributions over the retained accepted-act set. -/
noncomputable def foldSet {V : Type} (field : Field V) (history : FinSet Act) : field.Carrier := by
  letI := field.algebra
  exact Quotient.lift (s := listSetoid Act) (fun A => lift field.contribution A)
    (fun _ _ same => lift_setEq field.contribution same) history

theorem foldSet_history {V : Type} (field : Field V) (A : List Act) :
    foldSet field (rawHistory A) = (letI := field.algebra; lift field.contribution A) := by
  rw [rawHistory_eq]
  rfl

/-- The top-error guard derived from the source's own lattice metadata. -/
def guardSpec {V : Type} (field : Field V) : ThresholdSpec :=
  ⟨field.Carrier,field.algebra,field.contribution,[],by simp [Incompatible]⟩

/-- Construct the guarded observation source from retained source metadata. -/
noncomputable def source {V : Type} (field : Field V) : Source V :=
  .guardThreshold (guardSpec field) (.snapshot (fun history => field.project (foldSet field history)))

/-- The same source metadata supplies both raw carrier and display projection. -/
theorem source_data {V : Type} (world : Act → Prop) (field : Field V) (A : List Act) :
    data world (sourcePlan (source field)) A =
      .snapshot (field.project (letI := field.algebra; lift field.contribution A)) := by
  simp [source,sourcePlan,data,foldSet_history]

/-- Literal pair checks over installed alternatives, rather than an assumed
incompatibility law supplied by a compiler-correctness premise. -/
def pairCheck {V : Type} (field : Field V) (queries : List field.Carrier) : Bool := by
  letI := field.algebra
  letI := field.equality
  exact queries.all (fun a => queries.all (fun b => decide (a = b ∨ a ⊔ b = ⊤)))

theorem pairCheck_iff {V : Type} (field : Field V) (queries : List field.Carrier) :
    pairCheck field queries = true ↔
      (letI := field.algebra; Incompatible (fun q => q ∈ queries)) := by
  letI := field.algebra
  letI := field.equality
  simp only [pairCheck,List.all_eq_true,decide_eq_true_eq,Incompatible]
  constructor
  · intro check a b ha hb different
    exact (check a ha b hb).resolve_left different
  · intro incompatible a ha b hb
    by_cases same : a = b
    · exact Or.inl same
    · exact Or.inr (incompatible a b ha hb same)

/-- Check that threshold alternatives are nonempty, distinct, non-top, and pairwise incompatible. -/
def alternativesCheck {V : Type} (field : Field V) (queries : List field.Carrier) : Bool := by
  letI := field.algebra
  letI := field.equality
  exact !queries.isEmpty && decide queries.Nodup &&
    queries.all (fun q => decide (q ≠ ⊤)) && pairCheck field queries

theorem alternativesCheck_iff {V : Type} (field : Field V) (queries : List field.Carrier) :
    alternativesCheck field queries = true ↔ queries.isEmpty = false ∧ queries.Nodup ∧
      (letI := field.algebra; ∀ q ∈ queries, q ≠ ⊤) ∧
      (letI := field.algebra; Incompatible (fun q => q ∈ queries)) := by
  letI := field.algebra
  letI := field.equality
  simp only [alternativesCheck,Bool.and_eq_true,Bool.not_eq_true,List.all_eq_true,
    decide_eq_true_eq,pairCheck_iff,and_assoc]
  cases queries.isEmpty <;> simp

/-- Threshold alternatives with successful installed admissibility checks. -/
structure Query {V : Type} (field : Field V) where
  /-- The installed alternatives of the threshold read. -/
  alternatives : List field.Carrier
  checked : alternativesCheck field alternatives = true

/-- Construct the checked threshold specification. -/
def Query.spec {V : Type} {field : Field V} (query : Query field) : ThresholdSpec :=
  ⟨field.Carrier,field.algebra,field.contribution,query.alternatives,
    ((alternativesCheck_iff field query.alternatives).mp query.checked).2.2.2⟩

/-- Source-relative element decoding and finite pair checks fail closed. -/
def prepareQuery {V : Type} (field : Field V) (elements : List V) : Option (Query field) := do
  let alternatives ← elements.mapM field.decodeElement
  if checked : alternativesCheck field alternatives = true then some ⟨alternatives,checked⟩ else none

/-- Construct a threshold rule from checked source-relative alternatives. -/
def queryRule {V : Type} {field : Field V} (query : Query field) (name : String) : StateInstalledCompiler.Rule V :=
  .thresholdLift query.spec field.renderElement name

/-- The query's contribution function cannot diverge from the source's. -/
theorem query_source_coherence {V : Type} (field : Field V) (query : Query field) :
    query.spec.contribution = field.contribution := rfl

/-- Executable native raw-query semantics, with actual observed-source errors. -/
theorem query_refinement {V : Type} (world : Act → Prop) (field : Field V)
    (query : Query field) (observedSource : Plan V) (A : List Act) :
    observe world (.embed field.renderElement (.threshold query.spec observedSource)) A =
      nativeLiftThreshold query.spec field.renderElement (observe world observedSource A) A :=
  lift_threshold_refinement world query.spec field.renderElement observedSource A

/-- Incompatibility is derived from the installed finite pair checks. -/
theorem query_quasi_determinism {V : Type} (world : Act → Prop) (field : Field V)
    (query : Query field) (observedSource : Plan V) {A B : List Act} {a b : query.spec.Carrier}
    (left : observe world (.threshold query.spec observedSource) A = .data (.reached a))
    (right : observe world (.threshold query.spec observedSource) B = .data (.reached b)) :
    a = b ∨ ∃ evidence, observe world (.threshold query.spec observedSource) (A++B) = .fault evidence :=
  threshold_quasi_determinism world query.spec observedSource left right

end CBCL.StateInstalledLattice
