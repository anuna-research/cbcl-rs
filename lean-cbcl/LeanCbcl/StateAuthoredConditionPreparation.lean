import LeanCbcl.StateAuthoredSourceProvenance
import LeanCbcl.StateConditionCompiler
import LeanCbcl.StateAuthoredConditionOutputs

/-! Bridge the actual authored condition installation gate to closed singleton
query compilation. The ordered base compiler supplies source availability;
successful preparation constructs the complete condition output inventory. -/
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


/-- Successful preparation retains the exact ordered condition validation. -/
theorem prepared_conditions (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) :
    conditionsCheck environment prepared.freezes entries prepared.declarations [] = true := by
  have lowered : lowerStatic environment entries = some prepared := by
    cases h : lowerStatic environment entries with
    | none => simp [prepareStatic,h] at accepted
    | some p =>
      by_cases checked : preparedCheck p = true
      · have same : p = prepared := by simpa [prepareStatic,h,Option.filter,checked] using accepted
        subst p
        rfl
      · simp [prepareStatic,h,Option.filter,checked] at accepted
  unfold lowerStatic at lowered
  split at lowered
  · contradiction
  · split at lowered
    · contradiction
    · split at lowered
      · contradiction
      · split at lowered
        · contradiction
        · split at lowered
          · contradiction
          · split at lowered
            · cases Option.some.inj lowered
              assumption
            · contradiction

/-- The ordered base compiler supplies every newly introduced source plan.
Condition compilation therefore needs no external source-availability premise. -/
theorem emit_complete (environment : Environment) (templates : List FreezeTemplate)
    (plans : Plans Value) (entries : List Entry) (declarations : List (Declaration Value))
    (earlier : Definitions Value) (base : List (Output Value))
    (sources : ∀ field definition, earlier.lookup field = some definition → ∃ source, plans.lookup field = some source)
    (checked : conditionsCheck environment templates entries declarations earlier = true)
    (built : compileDeclarations plans earlier declarations = some base) :
    ∃ outputs, emitAuthored environment.profile.definition.bounds.maxList plans entries declarations base earlier = some outputs := by
  induction entries generalizing declarations earlier base with
  | nil =>
    cases declarations <;> simp [conditionsCheck] at checked
    have empty : base = [] := (Option.some.inj built).symm
    subst base
    exact ⟨[],rfl⟩
  | cons entry rest ih =>
    cases entry with
    | condition name expression =>
      simp only [conditionsCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
      obtain ⟨code,compiled⟩ := checked_tree_compiles environment templates earlier plans sources expression
        environment.profile.definition.bounds.maxList checked.1.1 checked.1.2
      obtain ⟨outputs,emitted⟩ := ih declarations earlier base sources checked.2 built
      exact ⟨.condition name (.element (.scalar (.bool true))) code :: outputs,
        by simp [emitAuthored,compiled,emitted]⟩
    | field name rule | threshold name field elements =>
      cases declarations with
      | nil => simp [conditionsCheck] at checked
      | cons declaration later =>
        simp only [conditionsCheck,Bool.and_eq_true,beq_iff_eq] at checked
        obtain ⟨output,first,after⟩ := Option.bind_eq_some_iff.mp built
        obtain ⟨remaining,tail,final⟩ := Option.bind_eq_some_iff.mp after
        have same : output :: remaining = base := Option.some.inj final
        subst base
        have extended : ∀ field definition, (extend earlier declaration).lookup field = some definition →
            ∃ source, plans.lookup field = some source := by
          cases declaration with
          | threshold _ _ _ => exact sources
          | field fieldName definition =>
            cases found : plans.lookup fieldName with
            | none => simp [compileOne,found] at first
            | some plan =>
              intro field selected lookup
              by_cases equal : fieldName = field
              · subst field
                exact ⟨plan,found⟩
              · have different : (field == fieldName) = false := by simp [Ne.symm equal]
                exact sources field selected (by simpa [extend,List.lookup_cons,different] using lookup)
        obtain ⟨outputs,emitted⟩ := ih later (extend earlier declaration) remaining extended checked.2 tail
        exact ⟨output :: outputs,by simp [emitAuthored,checked.1,emitted]⟩
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih declarations earlier base sources (by simpa [conditionsCheck] using checked) built

/-- Every accepted authored clause constructs its complete condition inventory
at any ranked, content-consistent history. -/
theorem prepared_output_exists (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (installed : prepareStatic environment entries = some prepared) (whole : List Act)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ observation, StateAuthoredConditionOutputs.compileAuthored environment entries whole = some observation := by
  have ready : prepare environment entries whole = some (clauseAt prepared whole) := by
    simp [prepare,installed,clauseAt]
  obtain ⟨sources,fields,base,compiled,resolved,built,cache⟩ :=
    prepared_compiler_cache_refinement environment entries whole (clauseAt prepared whole) ready ranked consistent
  have sourceBuilt : StateInstalledLowering.compile (clauseAt prepared whole) = some sources := by
    simpa [StateAuthoredBindings.compile,ready] using compiled
  obtain ⟨outputs,emitted⟩ := emit_complete environment prepared.freezes sources entries prepared.declarations [] base
    (by intro field definition impossible; simp at impossible)
    (prepared_conditions environment entries prepared installed) built
  exact ⟨⟨whole,⟨(clauseAt prepared whole).freezes,outputs⟩⟩,
    by
      simp [StateAuthoredConditionOutputs.compileAuthored,ready,sourceBuilt,built]
      change (emitAuthored _ _ _ prepared.declarations base []).bind _ = _
      rw [emitted]
      rfl⟩

end CBCL.StateAuthoredConditionPreparation
