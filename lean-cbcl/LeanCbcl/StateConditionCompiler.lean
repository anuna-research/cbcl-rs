import LeanCbcl.StateCondition
import LeanCbcl.StateOutputCompiler

/-! Closed condition code binds each leaf to an actual completed source plan and
its compiled singleton query. Observation dispatch reuses the source-owned scope
of StateOutputCompiler; no common condition cut is introduced. Integration into
the authored declaration walk remains a separate obligation. -/
set_option autoImplicit false
namespace CBCL.StateConditionCompiler
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler StateCondition StateThresholdDispatch

/-- Compiled leaves retain their actual source name, query and source plan. -/
inductive Code (V : Type) : Type 1 where
  | read (field : String) (query : Query V) (source : Plan V)
  | all (children : List (Code V))

/-- Compile only recognized conjunction shapes, admitted singleton queries and
actual completed source lookups. Bounds apply to the complete syntax tree. -/
noncomputable def compile {V : Type} (maxNodes : Nat) (plans : Plans V)
    (definitions : Definitions V) : Condition V → Option (Code V)
  | .read field element => if maxNodes = 0 then none else do
      let source ← plans.lookup field
      let definition ← definitions.lookup field
      let query ← compileQuery [element] definition
      return .read field query source
  | .all children =>
      if maxNodes < (Condition.all children).size ∨ children.length < 2 then none else do
        let compiled ← (children.map (compile maxNodes plans definitions)).mapM id
        return .all compiled

/-- Every leaf executes at its own retained source scope and complete fault pass. -/
noncomputable def Code.observe {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec)) :
    Code V → Observation Bool
  | .read field query source => boolean (query.run (referenceScope whole freezes field) (sourceValue whole source))
  | .all children => combine (children.map (Code.observe whole freezes))

/-- Independent syntax interpretation dispatches each original source policy. -/
noncomputable def interpret {V : Type} (maxNodes : Nat) (plans : Plans V) (definitions : Definitions V)
    (whole : List Act) (freezes : List (String × FreezeSpec)) : Condition V → Option (Observation Bool)
  | .read field element => if maxNodes = 0 then none else (plans.lookup field).bind (fun source =>
      (installedAt definitions field [element] (referenceScope whole freezes field) (sourceValue whole source)).map boolean)
  | .all children =>
      if maxNodes < (Condition.all children).size ∨ children.length < 2 then none else
        ((children.map (interpret maxNodes plans definitions whole freezes)).mapM id).map combine

/-- A compiled leaf is exactly the existing source-owned threshold output,
followed by condition-only Boolean normalization. -/
theorem leaf_observe {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (field : String) (query : Query V) (source : Plan V) :
    Code.observe whole freezes (.read field query source) =
      boolean ((Output.threshold "" field query source).observe whole freezes).2 := by
  simp only [Code.observe,Output.observe]

/-- A missing source plan rejects; declaration-order and source-kind eligibility
are enforced by the pending authored integration, not by this lookup lemma. -/
theorem absent_source {V : Type} (maxNodes : Nat) (plans : Plans V) (definitions : Definitions V)
    (field : String) (element : V) (absent : plans.lookup field = none) :
    compile maxNodes plans definitions (.read field element) = none := by
  simp [compile,absent]

/-- Zero condition budget rejects even a single read. -/
theorem zero_budget {V : Type} (plans : Plans V) (definitions : Definitions V)
    (field : String) (element : V) : compile 0 plans definitions (.read field element) = none := by
  simp [compile]

/-- Empty authored conjunctions reject instead of becoming the internal true identity. -/
theorem empty_rejected {V : Type} (maxNodes : Nat) (plans : Plans V) (definitions : Definitions V) :
    compile maxNodes plans definitions (.all []) = none := by
  simp [compile]

/-- Unary authored conjunctions reject even if their sole query would succeed. -/
theorem unary_rejected {V : Type} (maxNodes : Nat) (plans : Plans V) (definitions : Definitions V)
    (child : Condition V) : compile maxNodes plans definitions (.all [child]) = none := by
  simp [compile]

/-- Successful leaf compilation retains the real original source and singleton
query; it cannot invent a successful lookup or change an authored fixed bound. -/
theorem compile_read_origin {V : Type} (maxNodes : Nat) (plans : Plans V)
    (definitions : Definitions V) (field : String) (element : V) (code : Code V)
    (compiled : compile maxNodes plans definitions (.read field element) = some code) :
    ∃ source definition query, plans.lookup field = some source ∧
      definitions.lookup field = some definition ∧ compileQuery [element] definition = some query ∧
      code = .read field query source := by
  by_cases empty : maxNodes = 0
  · simp [compile,empty] at compiled
  cases found : plans.lookup field with
  | none => simp [compile,empty,found] at compiled
  | some source =>
    cases defined : definitions.lookup field with
    | none => simp [compile,empty,found,defined] at compiled
    | some definition =>
      cases queried : compileQuery [element] definition with
      | none => simp [compile,empty,found,defined,queried] at compiled
      | some query =>
        simp [compile,empty,found,defined,queried] at compiled
        exact ⟨source,definition,query,rfl,rfl,queried,compiled.symm⟩

/-- Compiled leaves refine the independent installed policy dispatch, with
source-owned raw scope selected independently of its displayed source payload. -/
theorem compile_leaf_refinement {V : Type} (maxNodes : Nat) (plans : Plans V)
    (definitions : Definitions V) (whole : List Act) (freezes : List (String × FreezeSpec))
    (field : String) (element : V) :
    (compile maxNodes plans definitions (.read field element)).map (Code.observe whole freezes) =
      if maxNodes = 0 then none else (plans.lookup field).bind (fun source =>
        (installedAt definitions field [element] (referenceScope whole freezes field)
          (sourceValue whole source)).map boolean) := by
  by_cases empty : maxNodes = 0
  · simp [compile,empty]
  simp only [empty,↓reduceIte]
  cases found : plans.lookup field with
  | none => simp [compile,empty,found]
  | some source =>
    simp only [Option.bind_some]
    rw [← compile_query_refinement definitions field [element]
      (referenceScope whole freezes field) (sourceValue whole source)]
    cases defined : definitions.lookup field with
    | none => simp [compile,empty,found,defined]
    | some definition =>
      cases queried : compileQuery [element] definition <;>
        simp [compile,empty,found,defined,queried,Code.observe]

/-- Two concrete leaves retain separate source cuts in the same conjunction. -/
theorem two_source_scopes {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (leftName rightName : String) (leftQuery rightQuery : Query V) (leftSource rightSource : Plan V) :
    Code.observe whole freezes (.all [.read leftName leftQuery leftSource,.read rightName rightQuery rightSource]) =
      combine [boolean (leftQuery.run (referenceScope whole freezes leftName) (sourceValue whole leftSource)),
        boolean (rightQuery.run (referenceScope whole freezes rightName) (sourceValue whole rightSource))] := by
  simp only [Code.observe,List.map_cons,List.map_nil]

/-- Compiled conjunctions keep the exact evidence union of every actual child. -/
theorem all_evidence {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (children : List (Code V)) :
    evidence (Code.observe whole freezes (.all children)) =
      ((children.map (Code.observe whole freezes)).map evidence).foldr unionError none := by
  simp only [Code.observe,combine_evidence]

/-- Compiled conjunction success cannot expose another successful Boolean. -/
theorem all_success {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (children : List (Code V)) (value : Bool)
    (success : Code.observe whole freezes (.all children) = .data (.reached value)) : value = true := by
  exact combine_success (children.map (Code.observe whole freezes)) value (by simpa only [Code.observe] using success)

universe u v

/-- Option traversal commutes with the fixed observation of each completed leaf. -/
theorem sequence_map {α : Type u} {β : Type v} (values : List (Option α)) (function : α → β) :
    (values.mapM id).map (List.map function) = ((values.map (Option.map function)).mapM id) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | none => simp
    | some first =>
      simp only [List.mapM_cons,List.map_cons,Option.map_some]
      rw [← ih]
      cases tail : rest.mapM id <;> rfl

/-- The complete recognized tree refines independent installed-source dispatch,
including all child scopes and fault channels, not caller-supplied read callbacks. -/
theorem compile_refinement {V : Type} (maxNodes : Nat) (plans : Plans V) (definitions : Definitions V)
    (whole : List Act) (freezes : List (String × FreezeSpec)) (condition : Condition V) :
    (compile maxNodes plans definitions condition).map (Code.observe whole freezes) =
      interpret maxNodes plans definitions whole freezes condition := by
  let P := fun condition : Condition V =>
    (compile maxNodes plans definitions condition).map (Code.observe whole freezes) =
      interpret maxNodes plans definitions whole freezes condition
  apply Condition.rec (motive_1 := P) (motive_2 := fun children => ∀ child ∈ children, P child)
  · intro field element
    simpa only [P,interpret] using compile_leaf_refinement maxNodes plans definitions whole freezes field element
  · intro children ih
    change P (.all children)
    unfold P
    by_cases invalid : maxNodes < (Condition.all children).size ∨ children.length < 2
    · simp [compile,interpret,invalid]
    have pointwise : children.map (fun child => (compile maxNodes plans definitions child).map (Code.observe whole freezes)) =
        children.map (interpret maxNodes plans definitions whole freezes) := by
      apply List.map_congr_left
      intro child member
      exact ih child member
    have sequence := sequence_map (children.map (compile maxNodes plans definitions)) (Code.observe whole freezes)
    simp only [List.map_map,Function.comp_def] at sequence
    rw [pointwise] at sequence
    cases assembled : (children.map (compile maxNodes plans definitions)).mapM id with
    | none =>
      simp only [assembled,Option.map_none] at sequence
      simp [compile,interpret,invalid,assembled,← sequence]
    | some codes =>
      simp only [assembled,Option.map_some] at sequence
      simp [compile,interpret,invalid,assembled,← sequence,Code.observe]
  · intro child impossible
    simp at impossible
  · intro head tail headProof tailProof child member
    rcases List.mem_cons.mp member with equal | member
    · simpa only [equal] using headProof
    · exact tailProof child member

end CBCL.StateConditionCompiler
