import LeanCbcl.StateAuthoredSourceProvenance
import LeanCbcl.StateConditionCompiler

/-! Bridge the actual authored condition installation gate to closed singleton
query compilation. Earlier-definition provenance and completed-plan existence
remain explicit at this layer; connecting their availability to the complete
authored walk remains a separate completeness obligation. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredConditionPreparation
open StateCondition State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler

/-- Source singleton admission constructs an actual compiled query using the
existing policy-refinement theorem, including each concrete policy inventory. -/
theorem admitted_query (definitions : Definitions Value) (field : String) (element : Value)
    (admitted : (lowerRule definitions (.threshold "" field [element])).isSome = true) :
    ∃ query, (definitions.lookup field).bind (compileQuery [element]) = some query := by
  cases lowered : lowerRule definitions (.threshold "" field [element]) with
  | none => simp [lowered] at admitted
  | some rule =>
    obtain ⟨result,dispatched⟩ := StatePreparedOutputs.threshold_available definitions "" field [element]
      rule lowered [] (.data .pending)
    have reflected := compile_query_refinement definitions field [element] [] (.data .pending)
    rw [dispatched] at reflected
    obtain ⟨query,compiled,_⟩ := Option.map_eq_some_iff.mp reflected
    exact ⟨query,compiled⟩

/-- The real authored leaf validator retains the exact source and fixed bound. -/
theorem checked_leaf_query (environment : Environment) (templates : List FreezeTemplate)
    (earlier : Definitions Value) (field : String) (element : Value)
    (checked : conditionSourceCheck environment templates earlier (.read field element) = true) :
    ∃ definition query, earlier.lookup field = some definition ∧ compileQuery [element] definition = some query := by
  simp only [conditionSourceCheck,Condition.fold_read,Bool.and_eq_true] at checked
  obtain ⟨query,compiled⟩ := admitted_query earlier field element checked.2
  cases found : earlier.lookup field with
  | none => simp [found] at compiled
  | some definition =>
    simp only [found,Option.bind_some] at compiled
    exact ⟨definition,query,rfl,compiled⟩

/-- No later supersede freeze can be hidden from a successfully checked leaf. -/
theorem checked_leaf_freezes (environment : Environment) (templates : List FreezeTemplate)
    (earlier : Definitions Value) (field : String) (element : Value)
    (checked : conditionSourceCheck environment templates earlier (.read field element) = true) :
    ∀ template ∈ templates, template.field = field → template.policy = true := by
  simp only [conditionSourceCheck,Condition.fold_read,Bool.and_eq_true] at checked
  intro template member same
  have accepted := List.all_eq_true.mp checked.1.2 template member
  simpa only [same,beq_self_eq_true,ite_true] using accepted

/-- A checked leaf and a completed actual source plan produce condition code;
no query predicate or source display is supplied by the caller. -/
theorem checked_leaf_compiles (environment : Environment) (templates : List FreezeTemplate)
    (earlier : Definitions Value) (plans : Plans Value) (maxNodes : Nat) (positive : 0 < maxNodes)
    (field : String) (element : Value) (source : Plan Value) (found : plans.lookup field = some source)
    (checked : conditionSourceCheck environment templates earlier (.read field element) = true) :
    ∃ code, StateConditionCompiler.compile maxNodes plans earlier (.read field element) = some code := by
  obtain ⟨definition,query,defined,queried⟩ := checked_leaf_query environment templates earlier field element checked
  have nonzero : maxNodes ≠ 0 := by omega
  exact ⟨.read field query source,by simp [StateConditionCompiler.compile,nonzero,found,defined,queried]⟩


/-- The actual source validator traverses every child of a conjunction. -/
theorem checked_children (environment : Environment) (templates : List FreezeTemplate)
    (earlier : Definitions Value) (children : List (Condition Value))
    (checked : conditionSourceCheck environment templates earlier (.all children) = true) :
    2 ≤ children.length ∧ ∀ child ∈ children,
      conditionSourceCheck environment templates earlier child = true := by
  simp only [conditionSourceCheck,Condition.fold_all] at checked
  change (decide (2 ≤ children.length) &&
    (children.map (conditionSourceCheck environment templates earlier)).all id) = true at checked
  simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
  refine ⟨checked.1,?_⟩
  intro child member
  exact List.all_eq_true.mp checked.2 _ (List.mem_map.mpr ⟨child,member,rfl⟩)

universe u v

/-- Ordered optional traversal succeeds whenever each actual input succeeds. -/
theorem mapM_available {A : Type u} {B : Type v} (inputs : List A) (function : A → Option B)
    (available : ∀ input ∈ inputs, ∃ output, function input = some output) :
    ∃ outputs, inputs.mapM function = some outputs := by
  induction inputs with
  | nil => exact ⟨[],rfl⟩
  | cons head tail ih =>
    obtain ⟨value,first⟩ := available head (by simp)
    obtain ⟨values,rest⟩ := ih (fun input member => available input (List.mem_cons_of_mem head member))
    exact ⟨value :: values,by simp [List.mapM_cons,first,rest]⟩

/-- Every admitted bounded tree compiles against a completed source dictionary.
The sole dictionary premise is plan availability for actual earlier sources;
query eligibility, conjunction arity and all descendant budgets are derived
from the original authored checks. -/
theorem checked_tree_compiles (environment : Environment) (templates : List FreezeTemplate)
    (earlier : Definitions Value) (plans : Plans Value)
    (sources : ∀ field definition, earlier.lookup field = some definition →
      ∃ source, plans.lookup field = some source)
    (condition : Condition Value) (maxNodes : Nat)
    (bounded : condition.size ≤ maxNodes)
    (checked : conditionSourceCheck environment templates earlier condition = true) :
    ∃ code, StateConditionCompiler.compile maxNodes plans earlier condition = some code := by
  let P := fun condition : Condition Value => ∀ maxNodes,
    condition.size ≤ maxNodes →
    conditionSourceCheck environment templates earlier condition = true →
    ∃ code, StateConditionCompiler.compile maxNodes plans earlier condition = some code
  apply Condition.rec (motive_1 := P) (motive_2 := fun children => ∀ child ∈ children, P child)
    ?_ ?_ ?_ ?_ condition maxNodes bounded checked
  · intro field element maxNodes bounded checked
    obtain ⟨definition,query,defined,_⟩ := checked_leaf_query environment templates earlier field element checked
    obtain ⟨source,found⟩ := sources field definition defined
    have positive : 0 < maxNodes := by change 1 ≤ maxNodes at bounded; omega
    exact checked_leaf_compiles environment templates earlier plans maxNodes positive field element source found checked
  · intro children ih maxNodes bounded checked
    obtain ⟨arity,childrenChecked⟩ := checked_children environment templates earlier children checked
    have available := mapM_available children (StateConditionCompiler.compile maxNodes plans earlier)
      (fun child member => ih child member maxNodes
        (Nat.le_trans (Condition.child_size_le children child member) bounded)
        (childrenChecked child member))
    obtain ⟨codes,compiled⟩ := available
    refine ⟨.all codes,?_⟩
    simp only [StateConditionCompiler.compile,Condition.fold_all]
    have valid : ¬ (maxNodes < (Condition.all children).size ∨ children.length < 2) := by omega
    simp only [valid,↓reduceIte]
    change ((children.map (StateConditionCompiler.compile maxNodes plans earlier)).mapM id).bind
      (fun values => some (StateConditionCompiler.Code.all values)) = some _
    have traversed : (children.map (StateConditionCompiler.compile maxNodes plans earlier)).mapM id = some codes := by
      simpa only [List.mapM_map,Function.comp_def, id_eq] using compiled
    rw [traversed]
    rfl
  · intro child impossible
    simp at impossible
  · intro head tail headProof tailProof child member
    rcases List.mem_cons.mp member with equal | inside
    · simpa only [equal] using headProof
    · exact tailProof child inside

end CBCL.StateAuthoredConditionPreparation
