import LeanCbcl.StateAuthoredSourceProvenance

/-! Ordered output compilation retains the actual priorDefinitions source environment.
Validated names identify each policy with its original source declaration; the
emitted output is located in the complete compiled code, not reconstructed. -/
namespace CBCL.StateAuthoredOutputProvenance
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler

/-- Every priorDefinitions source definition came from an original field declaration. -/
def Origins {V : Type} (full : List (Declaration V)) (definitions : Definitions V) : Prop :=
  ∀ name definition, (name,definition) ∈ definitions → Declaration.field name definition ∈ full

/-- Extending the real compiler environment preserves source provenance. -/
theorem extend_origins {V : Type} (full : List (Declaration V)) (definitions : Definitions V)
    (origins : Origins full definitions) (declaration : Declaration V) (member : declaration ∈ full) :
    Origins full (extend definitions declaration) := by
  intro name definition present
  cases declaration with
  | threshold _ _ _ => exact origins name definition present
  | field fieldName source =>
    rcases List.mem_cons.mp present with same | earlier
    · cases same; exact member
    · exact origins name definition earlier

/-- The validated shared namespace prevents distinct source definitions from
occupying the same name anywhere in the authored clause. -/
theorem unique_definition {V : Type} (full : List (Declaration V)) (unique : (full.map Declaration.name).Nodup)
    (name : String) (left right : Definition V)
    (first : Declaration.field name left ∈ full) (second : Declaration.field name right ∈ full) : left = right := by
  let indexed := full.map (fun declaration => (declaration.name,declaration))
  have names : (indexed.map Prod.fst).Nodup := by simpa only [indexed,List.map_map,Function.comp_def] using unique
  have a := StateReaderReachability.lookup_original indexed names name (.field name left)
    (List.mem_map.mpr ⟨.field name left,first,rfl⟩)
  have b := StateReaderReachability.lookup_original indexed names name (.field name right)
    (List.mem_map.mpr ⟨.field name right,second,rfl⟩)
  exact (Declaration.field.inj (Option.some.inj (a.symm.trans b))).2

/-- A successful output walk exposes its actual priorDefinitions and emitted code for
every original declaration, including thresholds after arbitrary other entries. -/
theorem emitted_origin {V : Type} (plans : Plans V) (full declarations : List (Declaration V))
    (definitions : Definitions V) (code : List (Output V))
    (origins : Origins full definitions) (included : ∀ declaration ∈ declarations, declaration ∈ full)
    (compiled : compileDeclarations plans definitions declarations = some code) :
    ∀ declaration ∈ declarations, ∃ priorDefinitions output,
      Origins full priorDefinitions ∧ output ∈ code ∧ compileOne plans priorDefinitions declaration = some output := by
  induction declarations generalizing definitions code with
  | nil => simp
  | cons declaration rest ih =>
    cases head : compileOne plans definitions declaration with
    | none => simp [compileDeclarations,head] at compiled
    | some output =>
      cases tail : compileDeclarations plans (extend definitions declaration) rest with
      | none => simp [compileDeclarations,head,tail] at compiled
      | some more =>
        have same : output :: more = code := by simpa [compileDeclarations,head,tail] using compiled
        subst code
        intro target member
        rcases List.mem_cons.mp member with rfl | inside
        · exact ⟨definitions,output,origins,by simp,head⟩
        · obtain ⟨priorDefinitions,selected,sourceOrigins,present,built⟩ := ih (extend definitions declaration) more
            (extend_origins full definitions origins declaration (included _ (by simp)))
            (fun selected member => included selected (List.mem_cons_of_mem _ member)) tail target inside
          exact ⟨priorDefinitions,selected,sourceOrigins,List.mem_cons_of_mem _ present,built⟩

/-- Encoding finite elements and decoding them in their source-owned policy
preserves the actual authored alternative list. -/
theorem decode_queries (queries : List Val) :
    (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q))).mapM StateFiniteRead.decode = some queries := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    simp only [List.map_cons,List.mapM_cons,StateFiniteRead.decode,ih]
    rfl

/-- Successful one-declaration compilation of a finite threshold recovers the
actual source policy and admitted alternative check from its priorDefinitions environment. -/
theorem finite_emitted (plans : Plans StateInstalledLegacy.Value)
    (full : List (Declaration StateInstalledLegacy.Value)) (unique : (full.map Declaration.name).Nodup)
    (field : StateInstalledFinite.Field) (name outputName : String) (queries : List Val)
    (declared : Declaration.field name (StateFiniteRead.definition field) ∈ full)
    (priorDefinitions : Definitions StateInstalledLegacy.Value) (origins : Origins full priorDefinitions)
    (plan : Plan StateInstalledLegacy.Value) (lookup : plans.lookup name = some plan)
    (output : Output StateInstalledLegacy.Value)
    (compiled : compileOne plans priorDefinitions (.threshold outputName name (queries.map (fun q => .element (.scalar q)))) = some output) :
    StateFiniteRead.check field queries = true ∧
      output = .threshold outputName name
        (.raw (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.policy field).test
          (StateInstalledFinite.term field).state) plan := by
  cases found : priorDefinitions.lookup name with
  | none => simp [compileOne,lookup,found] at compiled
  | some definition =>
    obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
    have present : (name,definition) ∈ priorDefinitions := by simp [equal]
    have same := unique_definition full unique name definition (StateFiniteRead.definition field)
      (origins name definition present) declared
    subst definition
    have policy : (StateFiniteRead.policy field).check (queries.map (fun q => .element (.scalar q))) =
        StateFiniteRead.check field queries := by simp only [StateFiniteRead.policy,decode_queries]
    cases checked : StateFiniteRead.check field queries with
    | false => simp [compileOne,lookup,found,compileQuery,StateFiniteRead.definition,policy,checked] at compiled
    | true =>
      refine ⟨rfl,?_⟩
      have compiledQuery := StateFiniteFreezePolicy.compiled_alternatives field queries checked
      have same : Output.threshold outputName name
          (.raw (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.policy field).test
            (StateInstalledFinite.term field).state) plan = output := by
        simpa [compileOne,lookup,found,compiledQuery] using compiled
      exact same.symm

end CBCL.StateAuthoredOutputProvenance
