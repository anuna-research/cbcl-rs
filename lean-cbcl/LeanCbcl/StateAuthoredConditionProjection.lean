import LeanCbcl.StateAuthoredConditionReplay
import LeanCbcl.StateAuthoredQuasiDeterminism

/-! Full authored assembly preserves every base observation and adds only the
explicitly named Boolean condition instructions. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredConditionProjection
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateOutputWitnessReplay StateConditionCompiler

/-- Erasing auxiliary entries retains the authored output namespace. -/
def names (entries : List Entry) : List String := entries.filterMap fun entry => match entry with
  | .field name _ | .threshold name _ _ | .condition name _ => some name
  | _ => none

/-- Output names form a sublist of the shared validated namespace. -/
theorem names_sublist (entries : List Entry) : (names entries).Sublist (declaredNames entries) := by
  induction entries with
  | nil => exact .slnil
  | cons entry rest ih =>
    cases entry with
    | field name _ | threshold name _ _ | condition name _ =>
      simpa [names,declaredNames] using List.Sublist.cons₂ name ih
    | lattice declaration => simpa [names,declaredNames] using List.Sublist.cons declaration.name ih
    | domain _ | freeze _ _ _ => simpa [names,declaredNames] using ih

/-- Interleaving preserves base instructions and introduces only declared
condition names; output-name order is exactly original authored order. -/
theorem emit_trace (maxNodes : Nat) (plans : Plans Value) (entries : List Entry)
    (declarations : List (Declaration Value)) (base outputs : List (Output Value)) (earlier : Definitions Value)
    (baseNames : base.map outputName = declarations.map Declaration.name)
    (emitted : emitAuthored maxNodes plans entries declarations base earlier = some outputs) :
    base.Sublist outputs ∧ outputs.map outputName = names entries ∧
      ∀ output ∈ outputs, output ∈ base ∨ ∃ name truth code expression,
        output = .condition name truth code ∧ Entry.condition name expression ∈ entries := by
  induction entries generalizing declarations base outputs earlier with
  | nil =>
    cases declarations <;> cases base <;> simp [emitAuthored] at emitted
    subst outputs
    exact ⟨.slnil,rfl,by simp⟩
  | cons entry rest ih =>
    cases entry with
    | condition name expression =>
      obtain ⟨code,built,after⟩ := Option.bind_eq_some_iff.mp emitted
      obtain ⟨tail,tailBuilt,final⟩ := Option.bind_eq_some_iff.mp after
      have same : Output.condition name (.element (.scalar (.bool true))) code :: tail = outputs := Option.some.inj final
      subst outputs
      obtain ⟨sub,named,origin⟩ := ih declarations base tail earlier baseNames tailBuilt
      refine ⟨List.Sublist.cons _ sub,by simp [outputName,named,names],?_⟩
      intro output member
      rcases List.mem_cons.mp member with equal | inside
      · exact Or.inr ⟨name,_,code,expression,equal,by simp⟩
      · rcases origin output inside with old | ⟨n,t,c,e,same,declared⟩
        · exact Or.inl old
        · exact Or.inr ⟨n,t,c,e,same,List.mem_cons_of_mem _ declared⟩
    | field name _ | threshold name _ _ =>
      cases declarations with
      | nil => simp [emitAuthored] at emitted
      | cons declaration later =>
        cases base with
        | nil => simp [emitAuthored] at emitted
        | cons output remaining =>
          by_cases equal : name = declaration.name
          · cases tailBuilt : emitAuthored maxNodes plans rest later remaining (extend earlier declaration) with
            | none => simp [emitAuthored,equal,tailBuilt] at emitted
            | some tail =>
              have same : output :: tail = outputs := by simpa [emitAuthored,equal,tailBuilt] using emitted
              subst outputs
              have headName : outputName output = name := (List.cons.inj baseNames).1.trans equal.symm
              obtain ⟨sub,named,origin⟩ := ih later remaining tail (extend earlier declaration) (List.cons.inj baseNames).2 tailBuilt
              refine ⟨List.Sublist.cons₂ output sub,by simp [headName,named,names],?_⟩
              intro selected member
              rcases List.mem_cons.mp member with same | inside
              · exact Or.inl (List.mem_cons.mpr (Or.inl same))
              · rcases origin selected inside with old | ⟨n,t,c,e,same,declared⟩
                · exact Or.inl (List.mem_cons_of_mem _ old)
                · exact Or.inr ⟨n,t,c,e,same,List.mem_cons_of_mem _ declared⟩
          · simp [emitAuthored,equal] at emitted
    | domain _ | lattice _ | freeze _ _ _ =>
      obtain ⟨sub,named,origin⟩ := ih declarations base outputs earlier baseNames (by simpa [emitAuthored] using emitted)
      refine ⟨sub,by simpa [names] using named,?_⟩
      intro output member
      rcases origin output member with old | ⟨n,t,c,e,same,declared⟩
      · exact Or.inl old
      · exact Or.inr ⟨n,t,c,e,same,List.mem_cons_of_mem _ declared⟩

/-- A full observation retains its base compiled vector as an ordered sublist. -/
theorem base_projection (environment : Environment) (entries : List Entry) (whole : List Act)
    (full : CompiledObservation)
    (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries whole = some full) :
    ∃ base, compileAuthored environment entries whole = some base ∧ base.observe.Sublist full.observe ∧
      base.history = full.history ∧ base.program.freezes = full.program.freezes ∧
      (full.observe.map Prod.fst).Nodup ∧
      ∀ output ∈ full.program.outputs, output ∈ base.program.outputs ∨ ∃ name truth code expression,
        output = .condition name truth code ∧ Entry.condition name expression ∈ entries := by
  obtain ⟨prepared,sources,base,outputs,installed,plans,built,emitted,same⟩ :=
    StateAuthoredConditionOutputs.compiled_parts environment entries whole full compiled
  subst full
  have baseNames : base.map outputName = prepared.declarations.map Declaration.name := by
    exact StateCompiledFiniteInversion.compiled_names sources [] prepared.declarations base built
  obtain ⟨sub,named,origin⟩ := emit_trace _ sources entries prepared.declarations base outputs [] baseNames emitted
  have checked : metadataCheck environment entries = true := by
    by_cases result : metadataCheck environment entries = true
    · exact result
    · have absent : lowerStatic environment entries = none := by simp [lowerStatic,result]
      simp [prepareStatic,absent] at installed
  simp only [metadataCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  refine ⟨⟨whole,⟨materialize prepared.domains whole prepared.freezes,base⟩⟩,?_,?_,rfl,rfl,?_,origin⟩
  · have ready : prepare environment entries whole = some (clauseAt prepared whole) := by simp [prepare,installed,clauseAt]
    have builtAt : compileDeclarations sources [] (clauseAt prepared whole).declarations = some base := built
    simp [compileAuthored,ready,StateOutputCompiler.compileClause,plans,builtAt,show (clauseAt prepared whole).freezes = materialize prepared.domains whole prepared.freezes from rfl]
  · exact sub.map _
  · have observed : (outputs.map (Output.observe whole (materialize prepared.domains whole prepared.freezes))).map Prod.fst = outputs.map outputName := by
      rw [List.map_map]
      apply List.map_congr_left
      intro output _
      cases output <;> rfl
    change (List.map Prod.fst (List.map _ outputs)).Nodup
    rw [observed,named]
    exact (names_sublist entries).nodup checked.1.1.1.2


/-- Every declared base threshold retains a named observation. -/
theorem base_threshold_present (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (installed : prepareStatic environment entries = some prepared)
    (name source : String) (elements : List Value) (member : Entry.threshold name source elements ∈ entries)
    (whole : List Act) (base : CompiledObservation) (compiled : compileAuthored environment entries whole = some base) :
    ∃ result, (name,result) ∈ base.observe := by
  obtain ⟨other,plans,code,accepted,_,built,history,body⟩ :=
    StateAuthoredOutputReplay.compile_authored_parts environment entries whole base compiled
  have same : prepared = other := Option.some.inj (installed.symm.trans accepted)
  subst other
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := StateAuthoredSourceProvenance.static_trace environment entries prepared installed
  have declared := StateAuthoredSourceProvenance.declaration_threshold environment prepared.domains tables entries []
    prepared.declarations bindings lowered name source elements member
  have namesEq : base.observe.map Prod.fst = prepared.declarations.map Declaration.name := by
    rw [CompiledObservation.observe,history,body,Program.observe,
      StateCompiledFiniteInversion.observed_names,StateCompiledFiniteInversion.compiled_names plans [] prepared.declarations code built]
  have present : name ∈ base.observe.map Prod.fst := by
    rw [namesEq]
    exact List.mem_map.mpr ⟨_,declared,rfl⟩
  obtain ⟨⟨n,result⟩,inside,equal⟩ := List.mem_map.mp present
  change n = name at equal
  subst n
  exact ⟨result,inside⟩

/-- Unique full names identify base threshold results without conflating a
condition with an earlier named source or threshold. -/
theorem threshold_in_base (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (installed : prepareStatic environment entries = some prepared)
    (name source : String) (elements : List Value) (member : Entry.threshold name source elements ∈ entries)
    (whole : List Act) (full base : CompiledObservation)
    (baseCompiled : compileAuthored environment entries whole = some base)
    (fullCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries whole = some full)
    (result : StateReaderValues.Result Value) (observed : (name,result) ∈ full.observe) :
    (name,result) ∈ base.observe := by
  obtain ⟨actual,compiled,sub,_,_,unique,_⟩ := base_projection environment entries whole full fullCompiled
  have equal : actual = base := Option.some.inj (compiled.symm.trans baseCompiled)
  subst actual
  obtain ⟨value,present⟩ := base_threshold_present environment entries prepared installed name source elements member whole base baseCompiled
  have old := StateReaderReachability.lookup_original full.observe unique name value (sub.subset present)
  have current := StateReaderReachability.lookup_original full.observe unique name result observed
  have same : value = result := Option.some.inj (old.symm.trans current)
  simpa only [same] using present

/-- A condition never emits frozen metadata, so every full frozen success is
an unchanged base source observation. -/
theorem frozen_in_base (environment : Environment) (entries : List Entry) (whole : List Act)
    (full base : CompiledObservation) (baseCompiled : compileAuthored environment entries whole = some base)
    (fullCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries whole = some full)
    (name : String) (address : Nat) (value : Value) (excluded : FinSet Act)
    (observed : (name,.data (.frozen address value excluded)) ∈ full.observe) :
    (name,.data (.frozen address value excluded)) ∈ base.observe := by
  obtain ⟨actual,compiled,_,history,freezes,_,origin⟩ := base_projection environment entries whole full fullCompiled
  have equal : actual = base := Option.some.inj (compiled.symm.trans baseCompiled)
  subst actual
  obtain ⟨output,member,emitted⟩ := List.mem_map.mp observed
  rcases origin output member with old | ⟨n,truth,code,expression,same,_⟩
  · apply List.mem_map.mpr
    refine ⟨output,old,?_⟩
    simpa [history,freezes] using emitted
  · subst output
    have impossible := (Prod.mk.inj emitted).2
    change truthResult truth (code.observe full.history full.program.freezes) = .data (.frozen address value excluded) at impossible
    cases current : code.observe full.history full.program.freezes with
    | fault ids => simp [current,truthResult] at impossible
    | data datum => cases datum <;> simp [current,truthResult] at impossible


/-- Every authored condition retains its own fixed-true instruction. -/
theorem emit_condition_present (maxNodes : Nat) (plans : Plans Value) (entries : List Entry)
    (declarations : List (Declaration Value)) (base outputs : List (Output Value)) (earlier : Definitions Value)
    (emitted : emitAuthored maxNodes plans entries declarations base earlier = some outputs)
    (name : String) (expression : StateCondition.Condition Value) (present : Entry.condition name expression ∈ entries) :
    ∃ code, Output.condition name (.element (.scalar (.bool true))) code ∈ outputs := by
  induction entries generalizing declarations base outputs earlier with
  | nil => simp at present
  | cons entry rest ih =>
    cases entry with
    | condition current tree =>
      obtain ⟨code,built,after⟩ := Option.bind_eq_some_iff.mp emitted
      obtain ⟨tail,tailBuilt,final⟩ := Option.bind_eq_some_iff.mp after
      have same : Output.condition current (.element (.scalar (.bool true))) code :: tail = outputs := Option.some.inj final
      subst outputs
      rcases List.mem_cons.mp present with equal | inside
      · cases equal
        exact ⟨code,by simp⟩
      · obtain ⟨other,member⟩ := ih declarations base tail earlier tailBuilt inside
        exact ⟨other,List.mem_cons_of_mem _ member⟩
    | field current _ | threshold current _ _ =>
      have inside : Entry.condition name expression ∈ rest := by simpa using present
      cases declarations with
      | nil => simp [emitAuthored] at emitted
      | cons declaration later =>
        cases base with
        | nil => simp [emitAuthored] at emitted
        | cons output remaining =>
          by_cases equal : current = declaration.name
          · cases tailBuilt : emitAuthored maxNodes plans rest later remaining (extend earlier declaration) with
            | none => simp [emitAuthored,equal,tailBuilt] at emitted
            | some tail =>
              have same : output :: tail = outputs := by simpa [emitAuthored,equal,tailBuilt] using emitted
              subst outputs
              obtain ⟨code,member⟩ := ih later remaining tail (extend earlier declaration) tailBuilt inside
              exact ⟨code,List.mem_cons_of_mem _ member⟩
          · simp [emitAuthored,equal] at emitted
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih declarations base outputs earlier (by simpa [emitAuthored] using emitted) (by simpa using present)

/-- Successful original authored conditions always return exactly Boolean true.
The source/query compiler and unique installed names determine the result. -/
theorem condition_success (environment : Environment) (entries : List Entry) (whole : List Act)
    (full : CompiledObservation)
    (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries whole = some full)
    (name : String) (expression : StateCondition.Condition Value) (present : Entry.condition name expression ∈ entries)
    (result : Value) (reached : (name,.data (.reached result)) ∈ full.observe) :
    result = .element (.scalar (.bool true)) := by
  obtain ⟨_,_,_,_,_,unique,_⟩ := base_projection environment entries whole full compiled
  obtain ⟨prepared,sources,base,outputs,installed,plans,built,emitted,same⟩ :=
    StateAuthoredConditionOutputs.compiled_parts environment entries whole full compiled
  subst full
  obtain ⟨code,member⟩ := emit_condition_present _ sources entries prepared.declarations base outputs [] emitted name expression present
  have actual : (name,truthResult (.element (.scalar (.bool true)))
      (code.observe whole (materialize prepared.domains whole prepared.freezes))) ∈
      (⟨whole,⟨materialize prepared.domains whole prepared.freezes,outputs⟩⟩ : CompiledObservation).observe :=
    List.mem_map.mpr ⟨_,member,rfl⟩
  have first := StateReaderReachability.lookup_original _ unique name _ actual
  have second := StateReaderReachability.lookup_original _ unique name _ reached
  have resultEq := Option.some.inj (first.symm.trans second)
  cases observed : code.observe whole (materialize prepared.domains whole prepared.freezes) with
  | fault ids => simp [observed,truthResult] at resultEq
  | data datum =>
    cases datum <;> simp [observed,truthResult] at resultEq
    exact resultEq.symm

end CBCL.StateAuthoredConditionProjection
