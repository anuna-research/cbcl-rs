import LeanCbcl.StateInstalledLattice
import LeanCbcl.StateInstalledTerm

/-! Installed source-relative lowering. Threshold declarations contain only a
source name and elements: they cannot supply a detached contribution or test.
The source definition selects its raw-lattice or native-display read strategy.
Native closure implementations and typed metadata extraction remain explicit
leaf parameters; this is not a proof about the Rust parser or serialized AST. -/
namespace CBCL.StateInstalledLowering
open State StateLift StateLVar StateObservation StateObservationPlan StateRuleRefinement
open StateInstalledCompiler

/-- Native closure-specific admissibility check retained from installation.
The compiler invokes it on the declared alternatives before emitting a read. -/
abbrev NativeRead (V : Type) := StateInstalledTerm.Policy V V

/-- The source metadata and admissible threshold policy retained during lowering. -/
inductive Definition (V : Type) where
  | native (source : Source V) (read : Option (NativeRead V))
  | factored (term : StateInstalledTerm.Term V) (read : Option (StateInstalledTerm.Policy V term.Carrier))
  | lattice (field : StateInstalledLattice.Field V)
  | derived (post : V → V) (name : String)
  | pair (combine : V → V → V) (left right : String)

/-- A named source, derived value, or threshold declaration. -/
inductive Declaration (V : Type) where
  | field (name : String) (definition : Definition V)
  | threshold (name source : String) (elements : List V)

/-- The installed state field name. -/
def Declaration.name {V : Type} : Declaration V → String
  | .field name _ | .threshold name _ _ => name

/-- The previously lowered source metadata indexed by field name. -/
abbrev Definitions (V : Type) := List (String × Definition V)

/-- Extend metadata with one successfully lowered declaration. -/
def extend {V : Type} (definitions : Definitions V) : Declaration V → Definitions V
  | .field name definition => (name,definition)::definitions
  | .threshold .. => definitions

/-- Construct retained source metadata for one authored declaration. -/
noncomputable def lowerDefinition {V : Type} : Definition V → StateInstalledCompiler.Rule V
  | .native source _ => .source source
  | .factored term _ => .source (StateInstalledTerm.source term)
  | .lattice field => .source (StateInstalledLattice.source field)
  | .derived post name => .derived post name
  | .pair combine left right => .pair combine left right

/-- Lower an authored rule using previously installed source metadata. -/
noncomputable def lowerRule {V : Type} (definitions : Definitions V) : Declaration V → Option (StateInstalledCompiler.Rule V)
  | .field _ definition => some (lowerDefinition definition)
  | .threshold _ source elements =>
      match definitions.lookup source with
      | none => none
      | some definition => match definition with
        | .native _ (some policy) => if policy.check elements then some (.threshold elements policy.test source) else none
        | .factored term (some policy) => if policy.check elements then
            some (.thresholdRaw elements policy.test term.state source) else none
        | .lattice field => match StateInstalledLattice.prepareQuery field elements with
          | none => none
          | some query => some (StateInstalledLattice.queryRule query source)
        | _ => none

/-- Resolve an authored declaration to its installed rule. -/
noncomputable def resolve {V : Type} (earlier : Definitions V) :
    List (Declaration V) → Option (List (String × StateInstalledCompiler.Rule V))
  | [] => some []
  | declaration::rest => do
      let rule ← lowerRule earlier declaration
      let tail ← resolve (extend earlier declaration) rest
      return (declaration.name,rule)::tail

/-- Independent native execution of one recognized source definition. -/
noncomputable def nativeDefinition {V : Type} (readers : Readers V) : Definition V → Option (Reader V)
  | .native source _ => some (sourceRead source)
  | .factored term _ => some (sourceRead (StateInstalledTerm.source term))
  | .lattice field => some (sourceRead (StateInstalledLattice.source field))
  | .derived post name => do
      let source ← readers.lookup name
      return fun A => nativeDerived post (source A)
  | .pair combine left right => do
      let l ← readers.lookup left
      let r ← readers.lookup right
      return fun A => nativePair combine (l A) (r A)

/-- Native query dispatch consults the source definition and the completed
source reader. It never interprets a compiled plan. -/
noncomputable def nativeRule {V : Type} (definitions : Definitions V) (readers : Readers V) :
    Declaration V → Option (Reader V)
  | .field _ definition => nativeDefinition readers definition
  | .threshold _ source elements =>
      match definitions.lookup source with
      | none => none
      | some definition => match definition with
        | .native _ (some policy) => if policy.check elements then do
            let reader ← readers.lookup source
            return fun A => nativeClosureThreshold elements policy.test (reader A)
          else none
        | .factored term (some policy) => if policy.check elements then do
            let reader ← readers.lookup source
            return fun A => nativeRawThreshold elements policy.test (term.state (rawHistory A)) (reader A)
          else none
        | .lattice field => do
            let query ← StateInstalledLattice.prepareQuery field elements
            let reader ← readers.lookup source
            return fun A => nativeLiftThreshold query.spec field.renderElement (reader A) A
        | _ => none

theorem lower_definition_refinement {V : Type} (world : Act → Prop) (readers : Readers V) (definition : Definition V) :
    interpretRule world readers (lowerDefinition definition) = nativeDefinition readers definition := by
  cases definition <;> rfl

/-- All query policy is obtained from the named installed source. -/
theorem lower_rule_refinement {V : Type} (world : Act → Prop) (definitions : Definitions V)
    (readers : Readers V) (declaration : Declaration V) :
    (lowerRule definitions declaration).bind (interpretRule world readers) = nativeRule definitions readers declaration := by
  cases declaration with
  | field name definition => exact lower_definition_refinement world readers definition
  | threshold name source elements =>
    cases found : definitions.lookup source with
    | none => simp [lowerRule,nativeRule,found]
    | some definition =>
      cases definition with
      | native sourceData read => cases read with
        | none => simp [lowerRule,nativeRule,found]
        | some policy => cases checked : policy.check elements <;> simp [lowerRule,nativeRule,found,checked,interpretRule]
      | derived _ _ | pair _ _ _ => simp [lowerRule,nativeRule,found]
      | factored term read => cases read with
        | none => simp [lowerRule,nativeRule,found]
        | some policy => cases checked : policy.check elements <;> simp [lowerRule,nativeRule,found,checked,interpretRule]
      | lattice field =>
        cases query : StateInstalledLattice.prepareQuery field elements <;>
          simp [lowerRule,nativeRule,found,query,StateInstalledLattice.queryRule,interpretRule]

/-- Attach all matching freeze declarations to an installed source. -/
noncomputable def decorate {V : Type} (world : Act → Prop) (freezes : List (String × FreezeSpec))
    (name : String) (reader : Reader V) : Reader V :=
  match freezes.lookup name with
  | none => reader
  | some spec => nativeFreeze world spec reader

/-- Read the ordered fields using the independent native interpreter. -/
noncomputable def nativeFields {V : Type} (world : Act → Prop) (freezes : List (String × FreezeSpec))
    (definitions : Definitions V) (earlier : Readers V) : List (Declaration V) → Option (Readers V)
  | [] => some []
  | declaration::rest => do
      let source ← nativeRule definitions earlier declaration
      let reader := decorate world freezes declaration.name source
      let tail ← nativeFields world freezes (extend definitions declaration) ((declaration.name,reader)::earlier) rest
      return (declaration.name,reader)::tail

theorem interpret_attached_head {V : Type} (world : Act → Prop) (freezes : List (String × FreezeSpec))
    (earlier : Readers V) (name : String) (rule : StateInstalledCompiler.Rule V) :
    StateInstalledClause.interpretField world earlier ⟨rule,freezes.lookup name⟩ =
      (interpretRule world earlier rule).map (decorate world freezes name) := by
  cases h : interpretRule world earlier rule <;>
    cases f : freezes.lookup name <;> simp [StateInstalledClause.interpretField,h,f,decorate]

/-- Whole source-relative lowering preserves the independent native reader
loop, including freezes attached before the next dependency resolves. -/
theorem resolve_native_refinement {V : Type} (world : Act → Prop) (freezes : List (String × FreezeSpec))
    (definitions : Definitions V) (earlier : Readers V) (declarations : List (Declaration V)) :
    (resolve definitions declarations).bind (fun fields => StateInstalledClause.interpretFields world earlier
      (StateInstalledClause.attach freezes fields)) = nativeFields world freezes definitions earlier declarations := by
  induction declarations generalizing definitions earlier with
  | nil => rfl
  | cons declaration rest ih =>
    have head := lower_rule_refinement world definitions earlier declaration
    cases lower : lowerRule definitions declaration with
    | none => simp [resolve,lower,nativeFields,← head,lower]
    | some rule =>
      simp only [lower,Option.bind_some] at head
      cases resolved : resolve (extend definitions declaration) rest with
      | none =>
        simp [resolve,lower,resolved,StateInstalledClause.attach,StateInstalledClause.interpretFields,
          interpret_attached_head,nativeFields,← head,← ih,resolved]
      | some fields =>
        simp [resolve,lower,resolved,StateInstalledClause.attach,StateInstalledClause.interpretFields,
          interpret_attached_head,nativeFields,← head,← ih,resolved]
        cases interpretRule world earlier rule <;> rfl

/-- An installed state clause with its ordered fields and freezes. -/
structure Clause (V : Type) where
  /-- The ordered source declarations. -/
  declarations : List (Declaration V)
  /-- The clause-wide freeze declarations. -/
  freezes : List (String × FreezeSpec)

/-- Supersede freezes can revise a source; thresholds may only observe an
unfrozen source or one using the terminal-fault policy. -/
def stableSource (freezes : List (String × FreezeSpec)) (source : String) : Bool :=
  match freezes.lookup source with | none => true | some spec => spec.policy

/-- Attach source freeze metadata before compiling dependent declarations. -/
def stableDeclarations {V : Type} (freezes : List (String × FreezeSpec)) (declarations : List (Declaration V)) : Bool :=
  declarations.all (fun declaration => match declaration with
    | .field .. => true
    | .threshold _ source _ => stableSource freezes source)

/-- Each declaration has the source metadata required by its read policy. -/
def ValidMetadata {V : Type} (clause : Clause V) : Prop :=
  (clause.declarations.map Declaration.name).Nodup ∧ (clause.freezes.map Prod.fst).Nodup ∧
    (∀ name ∈ clause.freezes.map Prod.fst, name ∈ clause.declarations.map Declaration.name) ∧
    stableDeclarations clause.freezes clause.declarations = true

instance {V : Type} (clause : Clause V) : Decidable (ValidMetadata clause) := by
  unfold ValidMetadata
  infer_instance

/-- Lower source metadata and compile the complete authored clause. -/
noncomputable def compile {V : Type} (clause : Clause V) : Option (Plans V) := do
  if ValidMetadata clause then
    let fields ← resolve [] clause.declarations
    StateInstalledClause.compileFields [] (StateInstalledClause.attach clause.freezes fields)
  else none

/-- Read the authored clause through the independent native field interpreter. -/
noncomputable def interpret {V : Type} (world : Act → Prop) (clause : Clause V) : Option (Readers V) :=
  if ValidMetadata clause then nativeFields world clause.freezes [] [] clause.declarations else none

/-- Top-level installed semantic compiler: raw-lattice/display query dispatch,
backward name resolution, global freeze attachment, and every dependency path
are connected to the typed plan. Wire extraction/native leaf implementations
are explicit boundaries, never correctness or fault-persistence assumptions. -/
theorem native_installed_compiler_refinement {V : Type} (world : Act → Prop) (clause : Clause V) :
    FieldsCorrespond world (compile clause) (interpret world clause) := by
  unfold compile interpret
  split
  · rw [← resolve_native_refinement world clause.freezes [] [] clause.declarations]
    cases resolved : resolve [] clause.declarations with
    | none => trivial
    | some fields =>
      exact StateInstalledClause.compile_fields_refinement world (plans := []) (readers := [])
        (fun _ => True.intro) (StateInstalledClause.attach clause.freezes fields)
  · trivial

/-- The names referenced by this installed declaration. -/
def references {V : Type} : Declaration V → List String
  | .field _ (.native ..) | .field _ (.factored ..) | .field _ (.lattice _) => []
  | .field _ (.derived _ name) => [name]
  | .field _ (.pair _ left right) => [left,right]
  | .threshold _ source _ => [source]

/-- Recognition uses source types and their actual element/pair checks. -/
inductive Recognized {V : Type} (definitions : Definitions V) : Declaration V → Prop where
  | field (name) (definition : Definition V) : Recognized definitions (.field name definition)
  | native (name source elements) (data : Source V) (policy : NativeRead V)
      (found : definitions.lookup source = some (.native data (some policy)))
      (checked : policy.check elements = true) : Recognized definitions (.threshold name source elements)
  | factored (name source elements) (term : StateInstalledTerm.Term V) (policy : StateInstalledTerm.Policy V term.Carrier)
      (found : definitions.lookup source = some (.factored term (some policy)))
      (checked : policy.check elements = true) : Recognized definitions (.threshold name source elements)
  | lattice (name source elements) (field : StateInstalledLattice.Field V) (query : StateInstalledLattice.Query field)
      (found : definitions.lookup source = some (.lattice field))
      (checked : StateInstalledLattice.prepareQuery field elements = some query) :
      Recognized definitions (.threshold name source elements)

/-- All references resolve and every declaration has valid source metadata. -/
inductive WellFormed {V : Type} : Definitions V → List String → List (Declaration V) → Prop where
  | nil (definitions names) : WellFormed definitions names []
  | cons (definitions names declaration rest)
      (recognized : Recognized definitions declaration)
      (backward : ∀ reference ∈ references declaration, reference ∈ names)
      (tail : WellFormed (extend definitions declaration) (declaration.name::names) rest) :
      WellFormed definitions names (declaration::rest)

theorem recognized_complete {V : Type} {definitions : Definitions V} {declaration : Declaration V}
    (recognized : Recognized definitions declaration) : ∃ rule, lowerRule definitions declaration = some rule := by
  cases recognized with
  | field name definition => exact ⟨lowerDefinition definition,rfl⟩
  | native name source elements data policy found checked =>
    exact ⟨.threshold elements policy.test source,by simp [lowerRule,found,checked]⟩
  | factored name source elements term policy found checked =>
    exact ⟨.thresholdRaw elements policy.test term.state source,by simp [lowerRule,found,checked]⟩
  | lattice name source elements field query found checked =>
    exact ⟨StateInstalledLattice.queryRule query source,by simp [lowerRule,found,checked]⟩

theorem lowered_references {V : Type} {definitions : Definitions V} {declaration : Declaration V}
    {rule : StateInstalledCompiler.Rule V} (lowered : lowerRule definitions declaration = some rule) :
    StateInstalledCompiler.references rule = references declaration := by
  cases declaration with
  | field name definition =>
    simp only [lowerRule,Option.some.injEq] at lowered
    subst rule
    cases definition <;> rfl
  | threshold name source elements =>
    cases found : definitions.lookup source with
    | none => simp [lowerRule,found] at lowered
    | some definition =>
      cases definition with
      | derived _ _ | pair _ _ _ => simp [lowerRule,found] at lowered
      | native data policy =>
        cases policy with
        | none => simp [lowerRule,found] at lowered
        | some policy =>
          cases checked : policy.check elements <;> simp [lowerRule,found,checked] at lowered
          subst rule
          rfl
      | factored term policy =>
        cases policy with
        | none => simp [lowerRule,found] at lowered
        | some policy =>
          cases checked : policy.check elements <;> simp [lowerRule,found,checked] at lowered
          subst rule
          rfl
      | lattice field =>
        cases checked : StateInstalledLattice.prepareQuery field elements with
        | none => simp [lowerRule,found,checked] at lowered
        | some query =>
          simp [lowerRule,found,checked] at lowered
          subst rule
          rfl

theorem resolve_complete {V : Type} {definitions : Definitions V} {names : List String}
    {declarations : List (Declaration V)} (wellFormed : WellFormed definitions names declarations) :
    ∃ fields, resolve definitions declarations = some fields ∧ StateInstalledCompiler.WellScoped names fields := by
  induction wellFormed with
  | nil => exact ⟨[],rfl,True.intro⟩
  | cons definitions names declaration rest recognized backward tail ih =>
    obtain ⟨rule,lowered⟩ := recognized_complete recognized
    obtain ⟨fields,resolved,wellScoped⟩ := ih
    refine ⟨(declaration.name,rule)::fields,?_,?_,wellScoped⟩
    · simp [resolve,lowered,resolved]
    · rw [lowered_references lowered]
      exact backward

/-- Non-vacuity for the complete source-relative compiler. -/
theorem native_installed_compiler_complete {V : Type} (clause : Clause V)
    (metadata : ValidMetadata clause) (wellFormed : WellFormed [] [] clause.declarations) :
    ∃ plans, compile clause = some plans := by
  obtain ⟨fields,resolved,wellScoped⟩ := resolve_complete wellFormed
  obtain ⟨plans,compiled⟩ := StateInstalledClause.attached_fields_complete [] fields clause.freezes wellScoped
  exact ⟨plans,by simp [compile,metadata,resolved,compiled]⟩

theorem native_installed_observations_refinement {V : Type} (world : Act → Prop)
    (clause : Clause V) (plans : Plans V) (compiled : compile clause = some plans) :
    ∃ readers, interpret world clause = some readers ∧ ∀ A, CausallyClosed world A →
      plans.map (fun (name,p) => (name,observe world p A)) = readers.map (fun (name,r) => (name,r A)) := by
  have related := native_installed_compiler_refinement world clause
  rw [compiled] at related
  cases interpreted : interpret world clause with
  | none => simp [interpreted,FieldsCorrespond] at related
  | some readers =>
    refine ⟨readers,rfl,?_⟩
    simp only [interpreted,FieldsCorrespond,Aligned] at related
    intro A closed
    clear compiled interpreted
    induction related with
    | nil => rfl
    | @cons p r ps rs head tail ih => simp only [List.map_cons,head.1,head.2 A closed,ih]

theorem native_installed_observations_setEq {V : Type} (world : Act → Prop)
    (clause : Clause V) (plans : Plans V) (compiled : compile clause = some plans)
    {A B : List Act} (ua : NodupAddr A) (ub : NodupAddr B) (same : SetEq A B)
    (ca : CausallyClosed world A) (cb : CausallyClosed world B) :
    ∃ readers, interpret world clause = some readers ∧
      readers.map (fun (name,r) => (name,r A)) = readers.map (fun (name,r) => (name,r B)) := by
  obtain ⟨readers,interpreted,equal⟩ := native_installed_observations_refinement world clause plans compiled
  refine ⟨readers,interpreted,?_⟩
  rw [← equal A ca,← equal B cb]
  apply List.map_congr_left
  intro binding _
  obtain ⟨name,p⟩ := binding
  simp only [observe_setEq world p ua ub same]

open StateKernelDelivery AdmissionStratification StateRefinement

/-- Finite complete delivery yields equality of the entire independently
interpreted installed clause, including its fault evidence and frozen data. -/
theorem native_installed_strong_eventual_consistency {V : Type} {adm : Admission}
    {auth : Act → Prop} {H : ValidHistory adm} (left right : Replica adm auth H)
    (admission : PredecessorAdmission adm H.contains) (clause : Clause V) (plans : Plans V)
    (compiled : compile clause = some plans) (history : List Act)
    (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ readers, interpret H.contains clause = some readers ∧ ∃ t, ∀ n m, t ≤ n → t ≤ m →
      readers.map (fun (name,r) => (name,r (left.run n).accepted)) =
      readers.map (fun (name,r) => (name,r (right.run m).accepted)) := by
  obtain ⟨readers,interpreted,equal⟩ := native_installed_observations_refinement H.contains clause plans compiled
  obtain ⟨tl,hl⟩ := finite_history_stabilizes left history complete
  obtain ⟨tr,hr⟩ := finite_history_stabilizes right history complete
  refine ⟨readers,interpreted,max tl tr,?_⟩
  intro n m hn hm
  rw [← equal _ (replica_causal_closed left admission n),← equal _ (replica_causal_closed right admission m)]
  apply List.map_congr_left
  intro binding _
  obtain ⟨name,p⟩ := binding
  simp only
  congr 1
  exact observe_setEq H.contains p
    (reachable_wellFormed (behavior_reachable left.behavior n)).accepted_unique
    (reachable_wellFormed (behavior_reachable right.behavior m)).accepted_unique
    (fun a => (hl n (by omega) a).trans (hr m (by omega) a).symm)

theorem aligned_reader {V : Type} {world : Act → Prop} {plans : Plans V} {readers : Readers V}
    (aligned : Aligned world plans readers) (reader : String × Reader V) (member : reader ∈ readers) :
    ∃ plan ∈ plans, plan.1 = reader.1 ∧ Agrees world plan.2 reader.2 := by
  induction aligned with
  | nil => simp at member
  | @cons p r ps rs head tail ih =>
    rcases List.mem_cons.mp member with equal | inside
    · subst reader
      exact ⟨p,by simp,head⟩
    · obtain ⟨plan,member,agrees⟩ := ih inside
      exact ⟨plan,List.mem_cons_of_mem _ member,agrees⟩

/-- Attributable faults of native installed readers disseminate with their
witnesses. This conclusion uses the plan compiler refinement and accepted
causal admission; native fault persistence is not a supplied hypothesis. -/
theorem native_installed_eventual_fault {V : Type} {adm : Admission} {auth : Act → Prop}
    {H : ValidHistory adm} (left right : Replica adm auth H)
    (admission : PredecessorAdmission adm H.contains) (clause : Clause V) (plans : Plans V)
    (compiled : compile clause = some plans) (readers : Readers V)
    (interpreted : interpret H.contains clause = some readers) (reader : String × Reader V)
    (member : reader ∈ readers) (atTime : Nat) (evidence : Evidence)
    (fault : reader.2 (left.run atTime).accepted = .fault evidence) :
    ∃ t, ∀ n, t ≤ n → ∃ enlarged, reader.2 (right.run n).accepted = .fault enlarged ∧
      ∀ address ∈ evidence, address ∈ enlarged := by
  have aligned := native_installed_compiler_refinement H.contains clause
  rw [compiled,interpreted] at aligned
  obtain ⟨plan,_,_,agrees⟩ := aligned_reader aligned reader member
  have planFault : observe H.contains plan.2 (left.run atTime).accepted = .fault evidence := by
    rw [agrees _ (replica_causal_closed left admission atTime),fault]
  obtain ⟨t,eventually⟩ := eventual_composed_fault left right admission plan.2 atTime planFault
  refine ⟨t,?_⟩
  intro n hn
  obtain ⟨enlarged,observed,includes⟩ := eventually n hn
  exact ⟨enlarged,(agrees _ (replica_causal_closed right admission n)).symm.trans observed,includes⟩

end CBCL.StateInstalledLowering
