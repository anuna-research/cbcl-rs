import LeanCbcl.StateFreezeGrowth

/-! Error-path refinement through ordered compilation when whole-observation
freeze contributor predicates increase. The literal source/query rules remain
fixed; dependency lookup carries the regenerated decorations forward. -/
set_option autoImplicit false
namespace CBCL.StateCompiledFreezeGrowth
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler StateFreezeGrowth

/-- The fault-path environment extracted from actual compiled plans. -/
def paths {V : Type} (plans : Plans V) : List (String × Path) :=
  plans.map (fun (name,plan) => (name,path plan))

/-- Named plan lookup and fault-path projection commute. -/
theorem lookup_paths {V : Type} (plans : Plans V) (name : String) :
    (paths plans).lookup name = (plans.lookup name).map path := by
  induction plans with
  | nil => rfl
  | cons binding rest ih =>
    obtain ⟨key,plan⟩ := binding
    by_cases same : key = name
    · subst key; simp [paths,List.lookup]
    · simp only [paths,List.map_cons,List.lookup,beq_eq_false_iff_ne.mpr (Ne.symm same)]
      exact ih

/-- Direct error-path elaboration of the same installed rule forms. -/
def rulePath {V : Type} (earlier : List (String × Path)) : Rule V → Option Path
  | .source source => some (path (sourcePlan source))
  | .earlier name | .derived _ name | .threshold _ _ name | .thresholdRaw _ _ _ name => earlier.lookup name
  | .pair _ left right => do return .join (← earlier.lookup left) (← earlier.lookup right)
  | .thresholdLift spec _ name => (earlier.lookup name).map (fun source => .join (.threshold spec) source)
  | .freeze spec name => (earlier.lookup name).map (fun source => .freeze spec.verb spec.contributes spec.policy source)

/-- Fault paths are those of the actual compiled rule, not an unrelated model. -/
theorem compile_rule_path {V : Type} (earlier : Plans V) (rule : Rule V) :
    (compileRule earlier rule).map path = rulePath (paths earlier) rule := by
  cases rule with
  | source source => rfl
  | earlier name => exact (lookup_paths earlier name).symm
  | derived post name | threshold alternatives test name | thresholdRaw alternatives test state name =>
    simp only [compileRule,rulePath,lookup_paths]
    cases earlier.lookup name <;> rfl
  | pair combine left right =>
    simp only [compileRule,rulePath,lookup_paths]
    cases earlier.lookup left <;> cases earlier.lookup right <;> rfl
  | thresholdLift spec embed name =>
    simp only [compileRule,rulePath,lookup_paths]
    cases earlier.lookup name <;> rfl
  | freeze spec name =>
    simp only [compileRule,rulePath,lookup_paths]
    cases earlier.lookup name <;> rfl

/-- Optional path lookup preserves rejection as well as related successful paths. -/
inductive Match : Option Path → Option Path → Prop where
  | none : Match none none
  | some {left right : Path} : Related left right → Match (some left) (some right)

/-- Mapping corresponding path constructors preserves optional lookup status. -/
theorem match_map {left right : Option Path} (related : Match left right) (f g : Path → Path)
    (preserves : ∀ a b, Related a b → Related (f a) (g b)) : Match (left.map f) (right.map g) := by
  cases related with
  | none => exact .none
  | some paths => exact .some (preserves _ _ paths)

/-- Both dependencies of a pair contribute their related error paths. -/
theorem match_join {a b c d : Option Path} (ac : Match a c) (bd : Match b d) :
    Match (a.bind (fun left => b.bind (fun right => some (Path.join left right))))
      (c.bind (fun left => d.bind (fun right => some (Path.join left right)))) := by
  cases ac with
  | none => exact .none
  | some left =>
    cases bd with
    | none => exact .none
    | some right => exact .some (.join left right)

/-- Every earlier source name has matching lookup status and related fault paths. -/
def Environments (left right : List (String × Path)) : Prop :=
  ∀ name, Match (left.lookup name) (right.lookup name)

/-- The same source-linked rule carries a path relation through every backward dependency. -/
theorem rule_path_related {V : Type} (left right : List (String × Path))
    (related : Environments left right) (rule : Rule V) : Match (rulePath left rule) (rulePath right rule) := by
  cases rule with
  | source source => exact .some (.same _)
  | earlier name | derived post name | threshold alternatives test name | thresholdRaw alternatives test state name =>
    exact related name
  | pair combine first second =>
    simpa [rulePath] using match_join (related first) (related second)
  | thresholdLift spec embed name =>
    exact match_map (related name) _ _ (fun _ _ relation => .join (.same _) relation)
  | freeze spec name =>
    exact match_map (related name) _ _ (fun _ _ relation =>
      .freeze spec.verb spec.contributes spec.contributes spec.policy (fun _ proof => proof) relation)

/-- Corresponding global freeze metadata preserves verb/policy and grows the
retained full-observation contributor predicate. -/
inductive FreezeMatch : Option FreezeSpec → Option FreezeSpec → Prop where
  | none : FreezeMatch none none
  | some (verb : String) (left right : Act → Prop) (policy : Bool) :
      (∀ act, left act → right act) → FreezeMatch (some ⟨verb,left,policy⟩) (some ⟨verb,right,policy⟩)

/-- Every target has corresponding global metadata in the regenerated clause. -/
def Decorations (left right : List (String × FreezeSpec)) : Prop :=
  ∀ name, FreezeMatch (left.lookup name) (right.lookup name)

/-- Attach the field's global freeze to its error path before dependencies resolve. -/
def decorate (freeze : Option FreezeSpec) (source : Path) : Path :=
  match freeze with
  | none => source
  | some spec => .freeze spec.verb spec.contributes spec.policy source

/-- Rebuilding a freeze decoration preserves the source's path relation. -/
theorem decorate_related {left right : Option FreezeSpec} (metadata : FreezeMatch left right)
    {a b : Path} (related : Related a b) : Related (decorate left a) (decorate right b) := by
  cases metadata with
  | none => exact related
  | some verb first second policy contributors => exact .freeze verb first second policy contributors related

/-- Extend backward dependency environments with the two decorated field paths. -/
theorem extend_related (left right : List (String × Path)) (related : Environments left right)
    (name : String) (a b : Path) (head : Related a b) : Environments ((name,a)::left) ((name,b)::right) := by
  intro key
  by_cases same : key = name
  · subst key
    simpa [List.lookup] using Match.some head
  · simpa [List.lookup,beq_eq_false_iff_ne.mpr same] using related key

/-- Literal ordered fault-path compiler corresponding to attached source fields. -/
def fields {V : Type} (earlier : List (String × Path)) (freezes : List (String × FreezeSpec)) :
    List (String × Rule V) → Option (List (String × Path))
  | [] => some []
  | (name,rule)::rest => do
      let source ← rulePath earlier rule
      let current := decorate (freezes.lookup name) source
      let tail ← fields ((name,current)::earlier) freezes rest
      some ((name,current)::tail)

/-- The same source order and regenerated decorations give related outputs. -/
def Outputs : Option (List (String × Path)) → Option (List (String × Path)) → Prop
  | none,none => True
  | some left,some right => List.Forall₂ (fun a b => a.1 = b.1 ∧ Related a.2 b.2) left right
  | _,_ => False

/-- Every ordered dependency path preserves relation and rejection status as
native full-history freeze contributor sets grow. -/
theorem fields_related {V : Type} (left right : List (String × Path))
    (earlier : Environments left right) (first second : List (String × FreezeSpec))
    (metadata : Decorations first second) (rules : List (String × Rule V)) :
    Outputs (fields left first rules) (fields right second rules) := by
  induction rules generalizing left right with
  | nil => exact .nil
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    have head := rule_path_related left right earlier rule
    generalize leftFound : rulePath left rule = leftPath at head
    generalize rightFound : rulePath right rule = rightPath at head
    cases head with
    | none => simp [fields,leftFound,rightFound,Outputs]
    | @some a b relation =>
      have decorated := decorate_related (metadata name) relation
      have tail := ih ((name,decorate (first.lookup name) a)::left) ((name,decorate (second.lookup name) b)::right)
        (extend_related left right earlier name _ _ decorated)
      cases leftTail : fields ((name,decorate (first.lookup name) a)::left) first rest with
      | none =>
        cases rightTail : fields ((name,decorate (second.lookup name) b)::right) second rest <;>
          simp [leftTail,rightTail,Outputs] at tail
        simp [fields,leftFound,rightFound,leftTail,rightTail,Outputs]
      | some leftMore =>
        cases rightTail : fields ((name,decorate (second.lookup name) b)::right) second rest with
        | none => simp [leftTail,rightTail,Outputs] at tail
        | some rightMore =>
          simp only [leftTail,rightTail,Outputs] at tail
          simp only [fields,leftFound,rightFound,Bind.bind,Option.bind,leftTail,rightTail,Outputs]
          exact List.Forall₂.cons ⟨rfl,decorated⟩ tail

/-- A global decoration's path is exactly that of the actual compiled field. -/
theorem compile_field_path {V : Type} (earlier : Plans V) (freezes : List (String × FreezeSpec))
    (name : String) (rule : Rule V) :
    (StateInstalledClause.compileField earlier ⟨rule,freezes.lookup name⟩).map path =
      (rulePath (paths earlier) rule).map (decorate (freezes.lookup name)) := by
  rw [← compile_rule_path]
  cases found : compileRule earlier rule <;> cases freezes.lookup name <;>
    simp [StateInstalledClause.compileField,found,decorate,path]

/-- Ordered error-path elaboration is the exact path projection of compiled
plans, including rejection and every globally attached freeze decoration. -/
theorem compile_fields_path {V : Type} (earlier : Plans V) (freezes : List (String × FreezeSpec))
    (rules : List (String × Rule V)) :
    (StateInstalledClause.compileFields earlier (StateInstalledClause.attach freezes rules)).map paths =
      fields (paths earlier) freezes rules := by
  induction rules generalizing earlier with
  | nil => rfl
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    have head := compile_field_path earlier freezes name rule
    have rewritten : fields (paths earlier) freezes ((name,rule)::rest) =
        ((rulePath (paths earlier) rule).map (decorate (freezes.lookup name))).bind
          (fun current => (fields ((name,current)::paths earlier) freezes rest).map (fun tail => (name,current)::tail)) := by
      cases found : rulePath (paths earlier) rule with
      | none => simp [fields,found]
      | some current =>
        cases more : fields ((name,decorate (freezes.lookup name) current)::paths earlier) freezes rest <;>
          simp [fields,found,more]
    rw [rewritten,← head]
    change ((StateInstalledClause.compileField earlier ⟨rule,freezes.lookup name⟩).bind (fun current =>
      (StateInstalledClause.compileFields ((name,current)::earlier) (StateInstalledClause.attach freezes rest)).bind
        (fun tail => some ((name,current)::tail)))).map paths = _
    cases compiled : StateInstalledClause.compileField earlier ⟨rule,freezes.lookup name⟩ with
    | none => rfl
    | some current =>
      simp only [Option.map_some,Bind.bind,Option.bind]
      have tail := ih ((name,current)::earlier)
      change _ = (fields (paths ((name,current)::earlier)) freezes rest).map (fun more => (name,path current)::more)
      rw [← tail]
      cases StateInstalledClause.compileFields ((name,current)::earlier) (StateInstalledClause.attach freezes rest) <;> rfl

/-- The actual compiled field paths preserve every previous fault witness as
both accepted history and full-observation freeze contributor sets grow. -/
theorem compiled_error_growth {V : Type} (world : Act → Prop) (rules : List (String × Rule V))
    (first second : List (String × FreezeSpec)) (metadata : Decorations first second)
    {A B : List Act} (closed : CausallyClosed world A) (growth : ∀ act ∈ A, act ∈ B)
    (left right : Plans V)
    (leftCompiled : StateInstalledClause.compileFields [] (StateInstalledClause.attach first rules) = some left)
    (rightCompiled : StateInstalledClause.compileFields [] (StateInstalledClause.attach second rules) = some right) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ Grows (errors world a.2 A) (errors world b.2 B)) (paths left) (paths right) := by
  have related := fields_related ([] : List (String × Path)) [] (by intro name; exact .none) first second metadata rules
  change Outputs (fields (paths ([] : Plans V)) first rules) (fields (paths ([] : Plans V)) second rules) at related
  rw [← compile_fields_path ([] : Plans V) first rules,← compile_fields_path ([] : Plans V) second rules,
    leftCompiled,rightCompiled] at related
  simp only [Option.map_some,Outputs] at related
  generalize paths left = leftPaths at related ⊢
  generalize paths right = rightPaths at related ⊢
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons ⟨head.1,related_errors_grow world head.2 closed growth⟩ ih

/-- Actual authored freeze templates discharge the decoration relation from
proved retained-contributor growth; no abstract selector-growth oracle is needed. -/
theorem authored_decorations (domains : List StateInstalledDomains.Domain)
    (templates : List StateAuthoredBindings.FreezeTemplate) {A B : List Act}
    (growth : ∀ act ∈ A, act ∈ B) :
    Decorations (StateAuthoredBindings.materialize domains A templates) (StateAuthoredBindings.materialize domains B templates) := by
  induction templates with
  | nil => intro name; exact .none
  | cons template rest ih =>
    intro name
    by_cases same : name = template.field
    · subst name
      simpa [StateAuthoredBindings.materialize,List.lookup] using
        FreezeMatch.some template.verb (StateAuthoredBindings.contributes domains A template.footprint)
          (StateAuthoredBindings.contributes domains B template.footprint) template.policy
          (StateAuthoredBindings.contributes_grows domains growth template.footprint)
    · simpa [StateAuthoredBindings.materialize,List.lookup,beq_eq_false_iff_ne.mpr same] using ih name

/-- Whole concrete authored compilation preserves fault witnesses across
accepted-set growth, even though each fold regenerates its freeze selectors. -/
theorem authored_compiled_error_growth (world : Act → Prop) (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) {A B : List Act}
    (closed : CausallyClosed world A) (growth : ∀ act ∈ A, act ∈ B) (left right : Plans StateInstalledLegacy.Value)
    (leftCompiled : StateAuthoredBindings.compile environment entries A = some left)
    (rightCompiled : StateAuthoredBindings.compile environment entries B = some right) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ Grows (errors world a.2 A) (errors world b.2 B)) (paths left) (paths right) := by
  cases prepared : StateAuthoredBindings.prepareStatic environment entries with
  | none => simp [StateAuthoredBindings.compile,StateAuthoredBindings.prepare,prepared] at leftCompiled
  | some metadata =>
    have leftClause : StateInstalledLowering.compile
        ⟨metadata.declarations,StateAuthoredBindings.materialize metadata.domains A metadata.freezes⟩ = some left := by
      simpa [StateAuthoredBindings.compile,StateAuthoredBindings.prepare,prepared] using leftCompiled
    have rightClause : StateInstalledLowering.compile
        ⟨metadata.declarations,StateAuthoredBindings.materialize metadata.domains B metadata.freezes⟩ = some right := by
      simpa [StateAuthoredBindings.compile,StateAuthoredBindings.prepare,prepared] using rightCompiled
    cases resolved : StateInstalledLowering.resolve [] metadata.declarations with
    | none => simp [StateInstalledLowering.compile,resolved] at leftClause
    | some rules =>
      have first : StateInstalledClause.compileFields []
          (StateInstalledClause.attach (StateAuthoredBindings.materialize metadata.domains A metadata.freezes) rules) = some left := by
        unfold StateInstalledLowering.compile at leftClause
        split at leftClause
        · simpa [resolved] using leftClause
        · contradiction
      have second : StateInstalledClause.compileFields []
          (StateInstalledClause.attach (StateAuthoredBindings.materialize metadata.domains B metadata.freezes) rules) = some right := by
        unfold StateInstalledLowering.compile at rightClause
        split at rightClause
        · simpa [resolved] using rightClause
        · contradiction
      exact compiled_error_growth world rules _ _ (authored_decorations metadata.domains metadata.freezes growth)
        closed growth left right first second

/-- Freeze policies and target lookup do not depend on the accepted observation. -/
theorem materialized_stable_source (domains : List StateInstalledDomains.Domain)
    (templates : List StateAuthoredBindings.FreezeTemplate) (A B : List Act) (name : String) :
    StateInstalledLowering.stableSource (StateAuthoredBindings.materialize domains A templates) name =
      StateInstalledLowering.stableSource (StateAuthoredBindings.materialize domains B templates) name := by
  induction templates with
  | nil => rfl
  | cons template rest ih =>
    by_cases same : name = template.field
    · subst name; simp [StateInstalledLowering.stableSource,StateAuthoredBindings.materialize,List.lookup]
    · simpa [StateInstalledLowering.stableSource,StateAuthoredBindings.materialize,List.lookup,
        beq_eq_false_iff_ne.mpr same] using ih

/-- All installed-clause metadata checks are invariant under rebuilding the
same global freezes with different retained contributor predicates. -/
theorem materialized_metadata (prepared : StateAuthoredBindings.Prepared) (A B : List Act) :
    StateInstalledLowering.ValidMetadata
      ⟨prepared.declarations,StateAuthoredBindings.materialize prepared.domains A prepared.freezes⟩ ↔
    StateInstalledLowering.ValidMetadata
      ⟨prepared.declarations,StateAuthoredBindings.materialize prepared.domains B prepared.freezes⟩ := by
  have names : (StateAuthoredBindings.materialize prepared.domains A prepared.freezes).map Prod.fst =
      (StateAuthoredBindings.materialize prepared.domains B prepared.freezes).map Prod.fst := by
    simp [StateAuthoredBindings.materialize,List.map_map,Function.comp_def]
  have stable : StateInstalledLowering.stableDeclarations
      (StateAuthoredBindings.materialize prepared.domains A prepared.freezes) prepared.declarations =
      StateInstalledLowering.stableDeclarations
      (StateAuthoredBindings.materialize prepared.domains B prepared.freezes) prepared.declarations := by
    unfold StateInstalledLowering.stableDeclarations
    apply congrArg (fun predicate => prepared.declarations.all predicate)
    funext declaration
    cases declaration with
    | field _ _ => rfl
    | threshold _ source _ => exact materialized_stable_source prepared.domains prepared.freezes A B source
  simp only [StateInstalledLowering.ValidMetadata]
  rw [names,stable]

/-- Growing accepted history cannot turn a successfully compiled concrete
clause into rejection when its global freeze contributors are regenerated. -/
theorem authored_compiles_after_growth (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B)
    (left : Plans StateInstalledLegacy.Value) (compiled : StateAuthoredBindings.compile environment entries A = some left) :
    ∃ right, StateAuthoredBindings.compile environment entries B = some right := by
  cases prepared : StateAuthoredBindings.prepareStatic environment entries with
  | none => simp [StateAuthoredBindings.compile,StateAuthoredBindings.prepare,prepared] at compiled
  | some metadata =>
    have first : StateInstalledLowering.compile
        ⟨metadata.declarations,StateAuthoredBindings.materialize metadata.domains A metadata.freezes⟩ = some left := by
      simpa [StateAuthoredBindings.compile,StateAuthoredBindings.prepare,prepared] using compiled
    have validA : StateInstalledLowering.ValidMetadata
        ⟨metadata.declarations,StateAuthoredBindings.materialize metadata.domains A metadata.freezes⟩ := by
      unfold StateInstalledLowering.compile at first
      split at first
      · assumption
      · contradiction
    have validB := (materialized_metadata metadata A B).mp validA
    cases resolved : StateInstalledLowering.resolve [] metadata.declarations with
    | none => simp [StateInstalledLowering.compile,resolved] at first
    | some rules =>
      have firstFields : StateInstalledClause.compileFields []
          (StateInstalledClause.attach (StateAuthoredBindings.materialize metadata.domains A metadata.freezes) rules) = some left := by
        simpa [StateInstalledLowering.compile,validA,resolved] using first
      have related := fields_related ([] : List (String × Path)) [] (by intro name; exact .none)
        _ _ (authored_decorations metadata.domains metadata.freezes growth) rules
      change Outputs (fields (paths ([] : Plans StateInstalledLegacy.Value)) _ rules)
        (fields (paths ([] : Plans StateInstalledLegacy.Value)) _ rules) at related
      rw [← compile_fields_path ([] : Plans StateInstalledLegacy.Value) _ rules,
        ← compile_fields_path ([] : Plans StateInstalledLegacy.Value) _ rules,firstFields] at related
      cases second : StateInstalledClause.compileFields []
          (StateInstalledClause.attach (StateAuthoredBindings.materialize metadata.domains B metadata.freezes) rules) with
      | none => simp [second,Outputs] at related
      | some right =>
        exact ⟨right,by simp [StateAuthoredBindings.compile,StateAuthoredBindings.prepare,prepared,
          StateInstalledLowering.compile,validB,resolved,second]⟩

/-- Aligned compiled paths transfer a named field's concrete fault witness. -/
theorem named_fault_transfer (world : Act → Prop) {A B : List Act}
    {left right : List (String × Path)}
    (related : List.Forall₂ (fun a b => a.1 = b.1 ∧ Grows (errors world a.2 A) (errors world b.2 B)) left right)
    (name : String) (source : Path) (member : (name,source) ∈ left) (evidence : Evidence)
    (fault : errors world source A = some evidence) :
    ∃ target enlarged, (name,target) ∈ right ∧ errors world target B = some enlarged ∧ ∀ address ∈ evidence, address ∈ enlarged := by
  induction related with
  | nil => simp at member
  | @cons a b left right head tail ih =>
    rcases List.mem_cons.mp member with same | more
    · have nameEqual : name = b.1 := (congrArg Prod.fst same).trans head.1
      have pathEqual : source = a.2 := congrArg Prod.snd same
      obtain ⟨enlarged,result,includes⟩ := head.2 evidence (by simpa [pathEqual] using fault)
      exact ⟨b.2,enlarged,List.mem_cons.mpr (Or.inl (by cases b; simp_all)),result,includes⟩
    · obtain ⟨target,enlarged,inside,result,includes⟩ := ih more
      exact ⟨target,enlarged,List.mem_cons_of_mem _ inside,result,includes⟩

/-- Concrete whole-clause fault persistence with automatically regenerated
plans: successful compilation cannot disappear, and every previous address
remains in the same named observation's terminal fault evidence. -/
theorem authored_fault_grows (world : Act → Prop) (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) {A B : List Act}
    (closed : CausallyClosed world A) (growth : ∀ act ∈ A, act ∈ B)
    (left : Plans StateInstalledLegacy.Value) (compiled : StateAuthoredBindings.compile environment entries A = some left)
    (name : String) (source : Plan StateInstalledLegacy.Value) (member : (name,source) ∈ left) (evidence : Evidence)
    (fault : observe world source A = .fault evidence) :
    ∃ right target enlarged, StateAuthoredBindings.compile environment entries B = some right ∧
      (name,target) ∈ right ∧ observe world target B = .fault enlarged ∧ ∀ address ∈ evidence, address ∈ enlarged := by
  obtain ⟨right,rightCompiled⟩ := authored_compiles_after_growth environment entries growth left compiled
  have relation := authored_compiled_error_growth world environment entries closed growth left right compiled rightCompiled
  have error : errors world (path source) A = some evidence := by
    cases read : errors world (path source) A with
    | none => simp [observe,read] at fault
    | some actual =>
      have equal : actual = evidence := by simpa [observe,read] using fault
      simpa [equal] using read
  have present : (name,path source) ∈ paths left := List.mem_map.mpr ⟨(name,source),member,rfl⟩
  obtain ⟨targetPath,enlarged,targetMember,result,includes⟩ := named_fault_transfer world relation name (path source) present evidence error
  obtain ⟨binding,inside,equal⟩ := List.mem_map.mp targetMember
  have nameEqual : binding.1 = name := congrArg Prod.fst equal
  have pathEqual : path binding.2 = targetPath := congrArg Prod.snd equal
  exact ⟨right,binding.2,enlarged,rightCompiled,by simpa [← nameEqual] using inside,
    by simp [observe,pathEqual,result],includes⟩

/-- Reliable accepted-witness dissemination yields eventual fault evidence at
another replica even when every observation recompiles its own freeze plans. -/
theorem eventual_authored_fault {adm : AdmissionStratification.Admission} {auth : Act → Prop}
    {H : StateKernelDelivery.ValidHistory adm}
    (left right : StateKernelDelivery.Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (atTime : Nat) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateAuthoredBindings.compile environment entries (left.run atTime).accepted = some plans)
    (name : String) (source : Plan StateInstalledLegacy.Value) (member : (name,source) ∈ plans) (evidence : Evidence)
    (fault : observe H.contains source (left.run atTime).accepted = .fault evidence) :
    ∃ time, ∀ n, time ≤ n → ∃ current target enlarged,
      StateAuthoredBindings.compile environment entries (right.run n).accepted = some current ∧
      (name,target) ∈ current ∧ observe H.contains target (right.run n).accepted = .fault enlarged ∧
      ∀ address ∈ evidence, address ∈ enlarged := by
  obtain ⟨time,delivered⟩ := witness_dissemination left right (left.run atTime).accepted atTime (by simp)
  exact ⟨time,fun n later => authored_fault_grows H.contains environment entries
    (replica_causal_closed left admission atTime) (delivered n later) plans compiled name source member evidence fault⟩

end CBCL.StateCompiledFreezeGrowth
