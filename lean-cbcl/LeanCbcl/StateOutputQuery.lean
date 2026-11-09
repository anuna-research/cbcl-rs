import LeanCbcl.StatePreparedOutputs

/-! Source-owned query strategies shared by ordinary and conjunction outputs.
The namespace remains StateOutputCompiler so existing query identities and
refinement statements retain their original names. -/
namespace CBCL.StateOutputCompiler
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateThresholdDispatch StatePreparedOutputs

/-- The closed installed threshold strategy inventory. -/
inductive Query (V : Type) : Type 1 where
  | closure (alternatives : List V) (test : V → V → Bool)
  | raw {C : Type} (alternatives : List V) (test : V → C → Bool) (state : FinSet Act → C)
  | finite (spec : ThresholdSpec) (embed : spec.Carrier → V)

/-- Execute compiled query code, preserving completed source faults. -/
noncomputable def Query.run {V : Type} : Query V → List Act → StateReaderValues.Result V → StateReaderValues.Result V
  | .closure alternatives test, _, value =>
    StateRuleRefinement.nativeClosureThreshold alternatives test (StateReaderValues.unfrozen value)
  | .raw alternatives test state, history, value => nativeRawThreshold alternatives test (state (StateLVar.rawHistory history)) value
  | .finite spec embed, history, value => match value with
    | .fault evidence => .fault evidence
    | .data _ => nativeLiftThreshold spec embed (StateReaderValues.unfrozen value) history

/-- Validate and compile the policy retained by the original source definition. -/
noncomputable def compileQuery {V : Type} (elements : List V) : Definition V → Option (Query V)
  | .native _ (some policy) => if policy.check elements then some (.closure elements policy.test) else none
  | .factored term (some policy) => if policy.check elements then some (.raw elements policy.test term.state) else none
  | .lattice field => match StateInstalledLattice.prepareQuery field elements with
    | none => none
    | some query => some (.finite query.spec field.renderElement)
  | _ => none

/-- Query compilation preserves independent installed-policy dispatch. -/
theorem compile_query_refinement {V : Type} (definitions : Definitions V) (source : String)
    (elements : List V) (raw : List Act) (value : StateReaderValues.Result V) :
    ((definitions.lookup source).bind (compileQuery elements)).map (fun query => query.run raw value) =
      installedAt definitions source elements raw value := by
  cases found : definitions.lookup source with
  | none => simp [installedAt,found]
  | some definition =>
    cases definition with
    | native data policy => cases policy <;> simp [compileQuery,installedAt,found,Query.run]
    | factored term policy => cases policy <;> simp [compileQuery,installedAt,found,Query.run]
    | lattice field =>
      cases query : StateInstalledLattice.prepareQuery field elements with
      | none => simp [compileQuery,installedAt,found,query]
      | some queryValue =>
        simp only [compileQuery,found,Option.bind_some,query,Option.map_some,Query.run,installedAt]
        cases value <;> rfl
    | derived _ _ | pair _ _ _ => simp [compileQuery,installedAt,found]

/-- A complete installed source observation at normalized full history. -/
noncomputable def sourceValue {V : Type} (whole : List Act) (source : Plan V) : StateReaderValues.Result V :=
  observe (fun act => act ∈ StateScopePool.normalize whole) source (StateScopePool.normalize whole)


end CBCL.StateOutputCompiler

namespace CBCL.StateOutputWitnessReplay
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler StateOutputCompiler

/-- Authored native and factored sources compile closure/raw query adapters.
Generic lattice-query code is distinguished because it can add a top fault. -/
def PlainQuery {V : Type} : Query V → Prop
  | .closure .. | .raw .. => True
  | .finite .. => False

/-- Every emitted query strategy preserves an existing source fault exactly. -/
theorem query_preserves_fault {V : Type} (query : Query V) (history : List Act) (e : Evidence) :
    query.run history (.fault e) = .fault e := by
  cases query <;> rfl

/-- Plain source-owned query adapters cannot invent a fault or change its
identities, including when the source carries a frozen display wrapper. -/
theorem plain_query_fault_iff {V : Type} (query : Query V) (plain : PlainQuery query)
    (history : List Act) (value : StateReaderValues.Result V) (e : Evidence) :
    query.run history value = .fault e ↔ value = .fault e := by
  cases query with
  | finite spec embed => contradiction
  | closure alternatives test =>
    cases value with
    | fault _ => rfl
    | data current =>
      cases current <;>
        simp only [Query.run,StateReaderValues.unfrozen,StateRuleRefinement.nativeClosureThreshold,Data.payload]
      all_goals first | exact iff_of_false (by contradiction) (by contradiction) | (split <;> simp)
  | raw alternatives test state =>
    cases value with
    | fault _ => rfl
    | data current =>
      simp only [Query.run,StateInstalledCompiler.nativeRawThreshold]
      split <;> simp


end CBCL.StateOutputWitnessReplay
