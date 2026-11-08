import LeanCbcl.StateInstalledCompiler
import LeanCbcl.StateResourceVerifier

/-! Freeze declarations attach to fields before dependency compilation. This
prevents a later freeze declaration from leaving an earlier derived field
connected to the unfrozen source. -/
namespace CBCL.StateInstalledClause
open State StateLift StateLVar StateObservation StateObservationPlan StateRuleRefinement
open StateInstalledCompiler

structure Field (V : Type) where
  rule : StateInstalledCompiler.Rule V
  freeze : Option FreezeSpec := none

def compileField {V : Type} (earlier : Plans V) (field : Field V) : Option (Plan V) := do
  let source ← compileRule earlier field.rule
  return match field.freeze with | none => source | some spec => .freeze spec source

noncomputable def interpretField {V : Type} (world : Act → Prop) (earlier : Readers V)
    (field : Field V) : Option (Reader V) := do
  let source ← interpretRule world earlier field.rule
  return match field.freeze with | none => source | some spec => nativeFreeze world spec source

theorem compile_field_refinement {V : Type} (world : Act → Prop) {plans : Plans V} {readers : Readers V}
    (related : Related world plans readers) (field : Field V) :
    Corresponds world (compileField plans field) (interpretField world readers field) := by
  have head := compile_rule_refinement world related field.rule
  cases hp : compileRule plans field.rule <;> cases hr : interpretRule world readers field.rule <;>
    simp [hp,hr,Corresponds] at head <;> simp [compileField,interpretField,hp,hr,Corresponds]
  next p r =>
    cases field.freeze with
    | none => exact head
    | some spec =>
      intro A closed
      rw [freeze_source_refinement world spec p closed]
      exact nativeFreeze_congr world spec _ _ head closed

def compileFields {V : Type} (earlier : Plans V) : List (String × Field V) → Option (Plans V)
  | [] => some []
  | (name,field)::rest => do
      let plan ← compileField earlier field
      let tail ← compileFields ((name,plan)::earlier) rest
      return (name,plan)::tail

noncomputable def interpretFields {V : Type} (world : Act → Prop) (earlier : Readers V) :
    List (String × Field V) → Option (Readers V)
  | [] => some []
  | (name,field)::rest => do
      let reader ← interpretField world earlier field
      let tail ← interpretFields world ((name,reader)::earlier) rest
      return (name,reader)::tail

theorem compile_fields_refinement {V : Type} (world : Act → Prop) {plans : Plans V} {readers : Readers V}
    (related : Related world plans readers) (fields : List (String × Field V)) :
    FieldsCorrespond world (compileFields plans fields) (interpretFields world readers fields) := by
  induction fields generalizing plans readers with
  | nil => exact List.Forall₂.nil
  | cons binding rest ih =>
    obtain ⟨name,field⟩ := binding
    have head := compile_field_refinement world related field
    cases hp : compileField plans field <;> cases hr : interpretField world readers field <;>
      simp [hp,hr,Corresponds] at head <;> simp [compileFields,interpretFields,hp,hr,FieldsCorrespond]
    next p r =>
      have tail := ih (related_cons related name p r head)
      cases tp : compileFields ((name,p)::plans) rest <;>
        cases tr : interpretFields world ((name,r)::readers) rest <;>
        simp [tp,tr,FieldsCorrespond] at tail <;> simp [tp,tr,FieldsCorrespond]
      exact .cons ⟨rfl,head⟩ tail

/-- Freeze metadata is looked up over the complete clause before any field is
compiled. No new public field or alias is introduced. -/
def attach {V : Type} (freezes : List (String × FreezeSpec)) (fields : List (String × StateInstalledCompiler.Rule V)) :
    List (String × Field V) := fields.map (fun (name,rule) => (name,⟨rule,freezes.lookup name⟩))

structure Clause (V : Type) where
  fields : List (String × StateInstalledCompiler.Rule V)
  freezes : List (String × FreezeSpec)

/-- Each target occurs exactly once, and names an existing source. Semantic
policy validation belongs to recognition of each installed FreezeSpec. -/
def ValidMetadata {V : Type} (clause : Clause V) : Prop :=
  (clause.fields.map Prod.fst).Nodup ∧ (clause.freezes.map Prod.fst).Nodup ∧
    ∀ name ∈ clause.freezes.map Prod.fst, name ∈ clause.fields.map Prod.fst

instance {V : Type} (clause : Clause V) : Decidable (ValidMetadata clause) := by
  unfold ValidMetadata
  infer_instance

def compile {V : Type} (clause : Clause V) : Option (Plans V) :=
  if ValidMetadata clause then compileFields [] (attach clause.freezes clause.fields) else none

noncomputable def interpret {V : Type} (world : Act → Prop) (clause : Clause V) : Option (Readers V) :=
  if ValidMetadata clause then interpretFields world [] (attach clause.freezes clause.fields) else none

theorem installed_clause_refinement {V : Type} (world : Act → Prop) (clause : Clause V) :
    FieldsCorrespond world (compile clause) (interpret world clause) := by
  unfold compile interpret
  split
  · exact compile_fields_refinement world (plans := []) (readers := []) (fun _ => True.intro) _
  · trivial

/-- A source decorated by any freeze declaration is already frozen when its
plan enters the earlier-field environment. -/
theorem attached_freeze_compilation {V : Type} (plans : Plans V) (rule : StateInstalledCompiler.Rule V)
    (spec : FreezeSpec) (source : Plan V) (compiled : compileRule plans rule = some source) :
    compileField plans ⟨rule,some spec⟩ = some (.freeze spec source) := by
  simp [compileField,compiled]

/-- Connect the resource leaf to the proved executable native verifier. The
only premises identify its installed config and accepted typed projection. -/
theorem native_resource_source_refinement {V : Type} (input : StateResourceVerifier.Input)
    (decode : Act → CheckpointEvidence.ResourceData) (source : Source V) (A : List Act)
    (projection : input.facts = CheckpointEvidence.project decode A) :
    sourceRead (.resource input.config decode source) A =
      nativeGuard (StateResourceVerifier.nativeFaultRead input) (sourceRead source A) := by
  rw [sourceRead,StateResourceVerifier.native_certificate_read_refinement input decode A projection]

/-- Global freeze attachment does not change reference admissibility. -/
theorem attached_fields_complete {V : Type} (earlier : Plans V)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (wellScoped : StateInstalledCompiler.WellScoped (earlier.map Prod.fst) fields) :
    ∃ plans, compileFields earlier (attach freezes fields) = some plans := by
  induction fields generalizing earlier with
  | nil => exact ⟨[],rfl⟩
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    obtain ⟨head,tail⟩ := wellScoped
    obtain ⟨source,compiled⟩ := StateInstalledCompiler.compile_rule_complete earlier rule head
    let plan := match freezes.lookup name with | none => source | some spec => Plan.freeze spec source
    have installed : compileField earlier ⟨rule,freezes.lookup name⟩ = some plan := by
      simp [compileField,compiled,plan]
    obtain ⟨plans,more⟩ := ih ((name,plan)::earlier) tail
    refine ⟨(name,plan)::plans,?_⟩
    change (compileField earlier ⟨rule,freezes.lookup name⟩).bind (fun source =>
      (compileFields ((name,source)::earlier) (attach freezes rest)).bind
        (fun tail => some ((name,source)::tail))) = _
    rw [installed]
    simp only [Option.bind_some,more]

end CBCL.StateInstalledClause
