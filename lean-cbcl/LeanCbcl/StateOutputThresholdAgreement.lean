import LeanCbcl.StateOutputConvergence

/-! Successful emitted thresholds return installed alternatives. Singleton
policies agree independently of source presentation and raw scope. -/
set_option autoImplicit false
namespace CBCL.StateOutputThresholdAgreement
open State StateObservationPlan StateOutputCompiler

/-- Closure dispatch can only return a supplied alternative. -/
theorem closure_reached_member {V : Type} (alternatives : List V) (test : V → V → Bool)
    (value : StateReaderValues.Result V) (result : V)
    (reached : Query.run (.closure alternatives test) [] value = .data (.reached result)) :
    result ∈ alternatives := by
  unfold Query.run StateRuleRefinement.nativeClosureThreshold at reached
  cases current : StateReaderValues.unfrozen value with
  | fault evidence => simp [current] at reached
  | data datum =>
    simp only [current] at reached
    cases payload : datum.payload with
    | none => simp [payload] at reached
    | some raw =>
      cases found : alternatives.find? (fun q => test q raw) with
      | none => simp [payload,found] at reached
      | some selected =>
        have same : selected = result := by simpa [payload,found] using reached
        subst selected
        exact List.mem_of_find?_eq_some found

/-- Raw dispatch can only return a supplied alternative, including at a cut. -/
theorem raw_reached_member {V C : Type} (alternatives : List V) (test : V → C → Bool)
    (state : StateLift.FinSet Act → C) (history : List Act)
    (value : StateReaderValues.Result V) (result : V)
    (reached : Query.run (.raw alternatives test state) history value = .data (.reached result)) :
    result ∈ alternatives := by
  cases value with
  | fault evidence => simp [Query.run,StateInstalledCompiler.nativeRawThreshold] at reached
  | data datum =>
    cases found : alternatives.find? (fun q => test q (state (StateLVar.rawHistory history))) with
    | none => simp [Query.run,StateInstalledCompiler.nativeRawThreshold,found] at reached
    | some selected =>
      have same : selected = result := by
        simpa [Query.run,StateInstalledCompiler.nativeRawThreshold,found] using reached
      subst selected
      exact List.mem_of_find?_eq_some found

/-- The native installation check admits exactly one alternative. -/
theorem read_check_singleton (allowed : StateInstalledLegacy.Element → Bool)
    (elements : List StateInstalledLegacy.Value)
    (checked : StateInstalledLegacy.readCheck allowed elements = true) :
    ∃ element, elements = [.element element] ∧ allowed element = true := by
  cases elements with
  | nil => simp [StateInstalledLegacy.readCheck] at checked
  | cons value rest =>
    cases rest with
    | cons _ _ => simp [StateInstalledLegacy.readCheck] at checked
    | nil =>
      cases value <;> simp_all [StateInstalledLegacy.readCheck]

/-- Alternatives retained by ordinary emitted query strategies. Generic finite
extension code has its own carrier and is deliberately outside this projection. -/
def alternatives {V : Type} : Query V → Option (List V)
  | .closure elements _ | .raw elements _ _ => some elements
  | .finite _ _ => none

/-- Ordinary strategy projection recovers every successful result's membership. -/
theorem reached_member {V : Type} (query : Query V) (elements : List V)
    (history : List Act) (value : StateReaderValues.Result V) (result : V)
    (shape : alternatives query = some elements)
    (reached : query.run history value = .data (.reached result)) : result ∈ elements := by
  cases query with
  | closure queries test =>
    have same : queries = elements := Option.some.inj shape
    subst queries
    exact closure_reached_member elements test value result reached
  | raw queries test state =>
    have same : queries = elements := Option.some.inj shape
    subst queries
    exact raw_reached_member elements test state history value result reached
  | finite spec embed => simp [alternatives] at shape

/-- Actual ordinary query compilation retains exactly the authored alternatives. -/
theorem compiled_alternatives {V : Type} (definition : StateInstalledLowering.Definition V)
    (elements : List V) (query : Query V)
    (plain : StateAuthoredOutputReplay.PlainDefinition definition)
    (compiled : compileQuery elements definition = some query) :
    alternatives query = some elements := by
  cases definition with
  | native source policy =>
    cases policy with
    | none => simp [compileQuery] at compiled
    | some policy =>
      cases check : policy.check elements <;> simp [compileQuery,check] at compiled
      subst query
      rfl
  | factored term policy =>
    cases policy with
    | none => simp [compileQuery] at compiled
    | some policy =>
      cases check : policy.check elements <;> simp [compileQuery,check] at compiled
      subst query
      rfl
  | lattice field => simp [StateAuthoredOutputReplay.PlainDefinition] at plain
  | derived source post => simp [compileQuery] at compiled
  | pair left right post => simp [compileQuery] at compiled

/-- Independently compiled singleton queries cannot return different successful
answers, even when their source values and source-owned raw cuts differ. -/
theorem compiled_singleton_success_agreement {V : Type}
    (leftDefinition rightDefinition : StateInstalledLowering.Definition V)
    (element leftResult rightResult : V) (leftQuery rightQuery : Query V)
    (leftPlain : StateAuthoredOutputReplay.PlainDefinition leftDefinition)
    (rightPlain : StateAuthoredOutputReplay.PlainDefinition rightDefinition)
    (leftCompiled : compileQuery [element] leftDefinition = some leftQuery)
    (rightCompiled : compileQuery [element] rightDefinition = some rightQuery)
    (leftHistory rightHistory : List Act)
    (leftValue rightValue : StateReaderValues.Result V)
    (leftReached : leftQuery.run leftHistory leftValue = .data (.reached leftResult))
    (rightReached : rightQuery.run rightHistory rightValue = .data (.reached rightResult)) :
    leftResult = rightResult := by
  have left := reached_member leftQuery [element] leftHistory leftValue leftResult
    (compiled_alternatives leftDefinition [element] leftQuery leftPlain leftCompiled) leftReached
  have right := reached_member rightQuery [element] rightHistory rightValue rightResult
    (compiled_alternatives rightDefinition [element] rightQuery rightPlain rightCompiled) rightReached
  have first : leftResult = element := by simpa using left
  have second : rightResult = element := by simpa using right
  exact first.trans second.symm

end CBCL.StateOutputThresholdAgreement
