import LeanCbcl.StateInstalledLowering

/-! Reference recognition of source-relative query policies and backward
references, with exact compiler acceptance rather than one-way completeness. -/
set_option autoImplicit false
namespace CBCL.StateInstalledRecognition
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler StateInstalledLowering

/-- Successful installed rule compilation implies every dependency is present. -/
theorem compile_rule_sound {V : Type} (earlier : Plans V) (rule : StateInstalledCompiler.Rule V)
    (plan : Plan V) (compiled : compileRule earlier rule = some plan) :
    ∀ name ∈ StateInstalledCompiler.references rule, name ∈ earlier.map Prod.fst := by
  cases rule with
  | source _ => simp [StateInstalledCompiler.references]
  | earlier name =>
    change earlier.lookup name = some plan at compiled
    have present := (lookup_present earlier name).mp (by simp [compiled])
    simpa [StateInstalledCompiler.references] using present
  | derived post name | threshold alternatives test name | thresholdRaw alternatives test state name
  | thresholdLift spec embed name | freeze spec name =>
    cases found : earlier.lookup name with
    | none => simp [compileRule,found] at compiled
    | some source =>
      have present := (lookup_present earlier name).mp (by simp [found])
      simpa [StateInstalledCompiler.references] using present
  | pair combine left right =>
    cases leftFound : earlier.lookup left with
    | none => simp [compileRule,leftFound] at compiled
    | some l =>
      cases rightFound : earlier.lookup right with
      | none => simp [compileRule,leftFound,rightFound] at compiled
      | some r =>
        have lPresent := (lookup_present earlier left).mp (by simp [leftFound])
        have rPresent := (lookup_present earlier right).mp (by simp [rightFound])
        intro name member
        simp only [StateInstalledCompiler.references,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact lPresent
        · exact rPresent

/-- Successful attached-field compilation implies the original rules are well scoped. -/
theorem attached_fields_sound {V : Type} (earlier : Plans V)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (plans : Plans V) (compiled : StateInstalledClause.compileFields earlier (StateInstalledClause.attach freezes fields) = some plans) :
    WellScoped (earlier.map Prod.fst) fields := by
  induction fields generalizing earlier plans with
  | nil => trivial
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    change (do
      let plan ← StateInstalledClause.compileField earlier ⟨rule,freezes.lookup name⟩
      let tail ← StateInstalledClause.compileFields ((name,plan)::earlier) (StateInstalledClause.attach freezes rest)
      pure ((name,plan)::tail)) = some plans at compiled
    cases head : StateInstalledClause.compileField earlier ⟨rule,freezes.lookup name⟩ with
    | none => simp [head] at compiled
    | some plan =>
      have sourceCompiled : ∃ source, compileRule earlier rule = some source := by
        cases source : compileRule earlier rule with
        | none => simp [StateInstalledClause.compileField,source] at head
        | some value => exact ⟨value,rfl⟩
      obtain ⟨source,sourceCompiled⟩ := sourceCompiled
      cases tailCompiled : StateInstalledClause.compileFields ((name,plan)::earlier) (StateInstalledClause.attach freezes rest) with
      | none => simp [head,tailCompiled] at compiled
      | some tail => exact ⟨compile_rule_sound earlier rule source sourceCompiled,ih _ _ tailCompiled⟩

/-- Source recognition is exactly successful policy-sensitive rule lowering. -/
theorem recognized_iff {V : Type} (definitions : Definitions V) (declaration : Declaration V) :
    Recognized definitions declaration ↔ (lowerRule definitions declaration).isSome = true := by
  constructor
  · intro recognized
    obtain ⟨rule,lowered⟩ := recognized_complete recognized
    simp [lowered]
  · intro lowered
    cases declaration with
    | field name definition => exact .field name definition
    | threshold name source elements =>
      cases found : definitions.lookup source with
      | none => simp [lowerRule,found] at lowered
      | some definition =>
        cases definition with
        | derived _ _ | pair _ _ _ => simp [lowerRule,found] at lowered
        | native data read =>
          cases read with
          | none => simp [lowerRule,found] at lowered
          | some policy =>
            cases checked : policy.check elements with
            | false => simp [lowerRule,found,checked] at lowered
            | true => exact .native name source elements data policy found checked
        | factored term read =>
          cases read with
          | none => simp [lowerRule,found] at lowered
          | some policy =>
            cases checked : policy.check elements with
            | false => simp [lowerRule,found,checked] at lowered
            | true => exact .factored name source elements term policy found checked
        | lattice field =>
          cases checked : StateInstalledLattice.prepareQuery field elements with
          | none => simp [lowerRule,found,checked] at lowered
          | some query => exact .lattice name source elements field query found checked

/-- Policy and backward-reference validation performed before plan construction. -/
noncomputable def check {V : Type} (definitions : Definitions V) (names : List String) : List (Declaration V) → Bool
  | [] => true
  | declaration :: rest => (lowerRule definitions declaration).isSome &&
      (StateInstalledLowering.references declaration).all names.contains &&
      check (extend definitions declaration) (declaration.name::names) rest

/-- The reference gate constructs every recognition and reference obligation. -/
theorem check_iff {V : Type} (definitions : Definitions V) (names : List String) (declarations : List (Declaration V)) :
    check definitions names declarations = true ↔ WellFormed definitions names declarations := by
  induction declarations generalizing definitions names with
  | nil => constructor <;> intro _; exact .nil _ _; rfl
  | cons declaration rest ih =>
    simp only [check,Bool.and_eq_true,← recognized_iff,List.all_eq_true,List.contains_iff_mem,ih]
    constructor
    · rintro ⟨⟨recognized,backward⟩,tail⟩; exact .cons _ _ _ _ recognized backward tail
    · intro formed
      cases formed with
      | cons _ _ _ _ recognized backward tail => exact ⟨⟨recognized,backward⟩,tail⟩

/-- Successful resolution plus scoping constructs authored well-formedness. -/
theorem resolve_sound {V : Type} (definitions : Definitions V) (names : List String)
    (declarations : List (Declaration V)) (fields : List (String × StateInstalledCompiler.Rule V))
    (resolved : resolve definitions declarations = some fields) (wellScoped : WellScoped names fields) :
    WellFormed definitions names declarations := by
  induction declarations generalizing definitions names fields with
  | nil => exact .nil _ _
  | cons declaration rest ih =>
    cases lowered : lowerRule definitions declaration with
    | none => simp [resolve,lowered] at resolved
    | some rule =>
      cases tail : resolve (extend definitions declaration) rest with
      | none => simp [resolve,lowered,tail] at resolved
      | some more =>
        simp [resolve,lowered,tail] at resolved
        subst fields
        refine .cons _ _ _ _ ((recognized_iff _ _).mpr (by simp [lowered])) ?_ (ih _ _ _ tail wellScoped.2)
        rw [← lowered_references lowered]
        exact wellScoped.1

/-- Successful compilation entails exactly the metadata and declaration conditions. -/
theorem compile_sound {V : Type} (clause : Clause V) (plans : Plans V)
    (compiled : StateInstalledLowering.compile clause = some plans) :
    ValidMetadata clause ∧ WellFormed [] [] clause.declarations := by
  unfold StateInstalledLowering.compile at compiled
  split at compiled
  · rename_i metadata
    cases resolved : resolve [] clause.declarations with
    | none => simp [resolved] at compiled
    | some fields =>
      have fieldsCompiled : StateInstalledClause.compileFields [] (StateInstalledClause.attach clause.freezes fields) = some plans := by
        simpa [resolved] using compiled
      exact ⟨metadata,resolve_sound [] [] clause.declarations fields resolved
        (attached_fields_sound [] fields clause.freezes plans fieldsCompiled)⟩
  · contradiction

/-- Exact semantic installation acceptance, with no assumed successful compilation. -/
theorem compile_iff {V : Type} (clause : Clause V) :
    (StateInstalledLowering.compile clause).isSome = true ↔
      ValidMetadata clause ∧ check [] [] clause.declarations = true := by
  rw [check_iff]
  constructor
  · intro accepted
    cases compiled : StateInstalledLowering.compile clause with
    | none => simp [compiled] at accepted
    | some plans => exact compile_sound clause plans compiled
  · rintro ⟨metadata,wellFormed⟩
    obtain ⟨plans,compiled⟩ := native_installed_compiler_complete clause metadata wellFormed
    simp [compiled]

end CBCL.StateInstalledRecognition
