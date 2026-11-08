import LeanCbcl.StateRuleRefinement

/-! Ordered installed-IR compiler. Native closures and immutable decoders are
explicit leaf parameters; parsing and validating surface declarations is a
separate boundary. References resolve only against earlier installed fields.
The independent interpreter retains history-indexed readers so freezes read
their dependencies at the causal cut. -/
namespace CBCL.StateInstalledCompiler
open State StateLift StateLVar StateObservation StateObservationPlan StateRuleRefinement

inductive Source (V : Type) where
  | snapshot (display : FinSet Act → V)
  | context (decode : Act → Option Val) (embed : Val → V)
  | domain (verb key opener field : String) (display : FinSet Act → V)
  | resource (config : CheckpointEvidence.ResourceConfig)
      (decode : Act → CheckpointEvidence.ResourceData) (source : Source V)
  | guardDomain (opener field : String) (source : Source V)
  | guardThreshold (spec : ThresholdSpec) (source : Source V)

def sourcePlan {V : Type} : Source V → Plan V
  | .snapshot display => .snapshot display
  | .context decode embed => .contextAs decode embed
  | .domain v k o f display => .domain v k o f display
  | .resource c decode source => .resource c decode (sourcePlan source)
  | .guardDomain opener field source => .guardDomain opener field (sourcePlan source)
  | .guardThreshold spec source => .guardThreshold spec (sourcePlan source)

def nativeGuard {V : Type} (guard : Error) (source : StateObservationPlan.Observation V) : StateObservationPlan.Observation V :=
  match unionError guard (sourceError source) with
  | some evidence => .fault evidence
  | none => source

noncomputable def sourceRead {V : Type} : Source V → List Act → StateObservationPlan.Observation V
  | .snapshot display, A => .data (.snapshot (display (rawHistory A)))
  | .context decode embed, A => match StateContext.read decode A with
      | .pending => .data .pending
      | .fault e => .fault e
      | .value v => .data (.context (embed v))
  | .domain v k o f display, A => match domainRead v k o f A with
      | .fault e => .fault e
      | .value selected => .data (.snapshot (display selected))
  | .resource c decode source, A => nativeGuard (StateResource.faultRead c decode A) (sourceRead source A)
  | .guardDomain opener field source, A => nativeGuard (domainError opener field A) (sourceRead source A)
  | .guardThreshold spec source, A => nativeGuard (thresholdError spec A) (sourceRead source A)

theorem source_refinement {V : Type} (world : Act → Prop) (source : Source V) (A : List Act) :
    observe world (sourcePlan source) A = sourceRead source A := by
  induction source with
  | snapshot display => rfl
  | context decode embed =>
    cases h : StateContext.read decode A <;> simp [sourcePlan,sourceRead,observe,path,errors,contextError,data,h]
  | domain v k o f display => exact domain_source_refinement world v k o f display A
  | resource c decode source ih =>
    simp only [sourcePlan,sourceRead,← ih]
    cases a : StateResource.faultRead c decode A <;> cases b : errors world (path (sourcePlan source)) A <;>
      simp [observe,path,errors,nativeGuard,sourceError,unionError,data,a,b]
  | guardDomain opener field source ih =>
    simp only [sourcePlan,sourceRead,← ih]
    cases a : domainError opener field A <;> cases b : errors world (path (sourcePlan source)) A <;>
      simp [observe,path,errors,nativeGuard,sourceError,unionError,data,a,b]
  | guardThreshold spec source ih =>
    simp only [sourcePlan,sourceRead,← ih]
    cases a : thresholdError spec A <;> cases b : errors world (path (sourcePlan source)) A <;>
      simp [observe,path,errors,nativeGuard,sourceError,unionError,data,a,b]


inductive Rule (V : Type) where
  | source (source : Source V)
  | earlier (name : String)
  | derived (post : V → V) (name : String)
  | pair (combine : V → V → V) (left right : String)
  | threshold (alternatives : List V) (test : V → V → Bool) (name : String)
  | thresholdLift (spec : ThresholdSpec) (embed : spec.Carrier → V) (name : String)
  | freeze (spec : FreezeSpec) (name : String)

abbrev Plans (V : Type) := List (String × Plan V)
abbrev Reader (V : Type) := List Act → StateObservationPlan.Observation V
abbrev Readers (V : Type) := List (String × Reader V)

def compileRule {V : Type} (earlier : Plans V) : Rule V → Option (Plan V)
  | .source source => some (sourcePlan source)
  | .earlier name => earlier.lookup name
  | .derived post name => do return .map post (← earlier.lookup name)
  | .pair combine left right => do
      let l ← earlier.lookup left
      let r ← earlier.lookup right
      return .map (fun (a,b) => combine a b) (.pair l r)
  | .threshold alternatives test name => do return .thresholdOn alternatives test (← earlier.lookup name)
  | .thresholdLift spec embed name => do return .embed embed (.threshold spec (← earlier.lookup name))
  | .freeze spec name => do return .freeze spec (← earlier.lookup name)

def nativePair {V : Type} (combine : V → V → V)
    (left right : StateObservationPlan.Observation V) : StateObservationPlan.Observation V :=
  match left, right with
  | .fault a, .fault b => .fault (a ∪ b)
  | .fault a, _ => .fault a
  | _, .fault b => .fault b
  | .data a, .data b => .data (mapData (fun (l,r) => combine l r) (pairData a b))

/-- The raw carrier read used by factored native rules. This differs from a
closure threshold: the source fault wins, but the raw carrier is folded over
current accepted history even when the displayed source has been frozen. -/
noncomputable def nativeLiftThreshold {V : Type} (spec : ThresholdSpec)
    (embed : spec.Carrier → V) (source : StateObservationPlan.Observation V) (A : List Act) :
    StateObservationPlan.Observation V := by
  letI := spec.algebra
  exact match unionError (thresholdError spec A) (sourceError source) with
  | some evidence => .fault evidence
  | none => match thresholdRead spec.alternatives (lift spec.contribution A)
      (sourceError source).isSome (rawHistory A) with
      | .pending | .fault _ => .data .pending
      | .reached value => .data (.reached (embed value))

noncomputable def interpretRule {V : Type} (world : Act → Prop) (earlier : Readers V) :
    Rule V → Option (Reader V)
  | .source source => some (sourceRead source)
  | .earlier name => earlier.lookup name
  | .derived post name => do
      let source ← earlier.lookup name
      return fun A => nativeDerived post (source A)
  | .pair combine left right => do
      let l ← earlier.lookup left
      let r ← earlier.lookup right
      return fun A => nativePair combine (l A) (r A)
  | .threshold alternatives test name => do
      let source ← earlier.lookup name
      return fun A => nativeClosureThreshold alternatives test (source A)
  | .thresholdLift spec embed name => do
      let source ← earlier.lookup name
      return fun A => nativeLiftThreshold spec embed (source A) A
  | .freeze spec name => do
      let source ← earlier.lookup name
      return nativeFreeze world spec source

def Agrees {V : Type} (world : Act → Prop) (p : Plan V) (r : Reader V) : Prop :=
  ∀ A, CausallyClosed world A → observe world p A = r A

def Corresponds {V : Type} (world : Act → Prop) : Option (Plan V) → Option (Reader V) → Prop
  | none, none => True
  | some p, some r => Agrees world p r
  | _, _ => False

def Related {V : Type} (world : Act → Prop) (plans : Plans V) (readers : Readers V) : Prop :=
  ∀ name, Corresponds world (plans.lookup name) (readers.lookup name)

theorem pair_refinement {V : Type} (world : Act → Prop) (combine : V → V → V)
    (left right : Plan V) (A : List Act) :
    observe world (.map (fun (l,r) => combine l r) (.pair left right)) A =
      nativePair combine (observe world left A) (observe world right A) := by
  cases l : errors world (path left) A <;> cases r : errors world (path right) A <;>
    simp [observe,path,errors,unionError,data,nativePair,l,r]

/-- Reader equality is needed only for admitted histories, including the cut. -/
theorem nativeFreeze_congr {V : Type} (world : Act → Prop) (spec : FreezeSpec)
    (left right : Reader V) (same : ∀ A, CausallyClosed world A → left A = right A)
    {A : List Act} (closed : CausallyClosed world A) :
    nativeFreeze world spec left A = nativeFreeze world spec right A := by
  classical
  unfold nativeFreeze freezeRead
  rw [same A closed]
  split
  · rfl
  · cases first : A.find? (fun f => decide (Earliest world spec.verb A f)) with
    | none => simp [same A closed]
    | some f => simp [same _ (cut_closed closed f)]


theorem lift_threshold_refinement {V : Type} (world : Act → Prop) (spec : ThresholdSpec)
    (embed : spec.Carrier → V) (source : Plan V) (A : List Act) :
    observe world (.embed embed (.threshold spec source)) A =
      nativeLiftThreshold spec embed (observe world source A) A := by
  letI := spec.algebra
  unfold nativeLiftThreshold
  rw [source_error_refinement]
  cases e : unionError (thresholdError spec A) (errors world (path source) A) with
  | some evidence => simp [observe,path,errors,data,e]
  | none =>
    simp only [observe,path,errors,e,data]
    cases thresholdRead spec.alternatives (lift spec.contribution A)
      (errors world (path source) A).isSome (rawHistory A) <;> rfl

/-- Exact per-rule refinement, including rejection of unresolved references. -/
theorem compile_rule_refinement {V : Type} (world : Act → Prop) {plans : Plans V} {readers : Readers V}
    (related : Related world plans readers) (rule : Rule V) :
    Corresponds world (compileRule plans rule) (interpretRule world readers rule) := by
  cases rule with
  | source source => exact fun A _ => source_refinement world source A
  | earlier name => exact related name
  | derived post name =>
    have same := related name
    cases hp : plans.lookup name <;> cases hr : readers.lookup name <;>
      simp [hp,hr,Corresponds] at same <;> simp [compileRule,interpretRule,hp,hr,Corresponds]
    intro A closed
    rw [derived_source_refinement,same A closed]
  | threshold alternatives test name =>
    have same := related name
    cases hp : plans.lookup name <;> cases hr : readers.lookup name <;>
      simp [hp,hr,Corresponds] at same <;> simp [compileRule,interpretRule,hp,hr,Corresponds]
    intro A closed
    rw [← compileClosureThreshold,closure_threshold_refinement,same A closed]
  | thresholdLift spec embed name =>
    have same := related name
    cases hp : plans.lookup name <;> cases hr : readers.lookup name <;>
      simp [hp,hr,Corresponds] at same <;> simp [compileRule,interpretRule,hp,hr,Corresponds]
    intro A closed
    rw [lift_threshold_refinement,same A closed]
  | freeze spec name =>
    have same := related name
    cases hp : plans.lookup name <;> cases hr : readers.lookup name <;>
      simp [hp,hr,Corresponds] at same <;> simp [compileRule,interpretRule,hp,hr,Corresponds]
    intro A closed
    rw [freeze_source_refinement world spec _ closed]
    exact nativeFreeze_congr world spec _ _ same closed
  | pair combine left right =>
    have sl := related left
    have sr := related right
    cases pl : plans.lookup left <;> cases rl : readers.lookup left <;>
      cases pr : plans.lookup right <;> cases rr : readers.lookup right <;>
      simp [pl,rl,pr,rr,Corresponds] at sl sr <;>
      simp [compileRule,interpretRule,pl,rl,pr,rr,Corresponds]
    intro A closed
    rw [pair_refinement,sl A closed,sr A closed]

/-- The next binding is installed before processing the tail. This is the
same left-to-right scope rule as the runtime's `done` map. -/
def compileFields {V : Type} (earlier : Plans V) : List (String × Rule V) → Option (Plans V)
  | [] => some []
  | (name,rule) :: rest => do
      let plan ← compileRule earlier rule
      let tail ← compileFields ((name,plan) :: earlier) rest
      return (name,plan) :: tail

noncomputable def interpretFields {V : Type} (world : Act → Prop) (earlier : Readers V) :
    List (String × Rule V) → Option (Readers V)
  | [] => some []
  | (name,rule) :: rest => do
      let reader ← interpretRule world earlier rule
      let tail ← interpretFields world ((name,reader) :: earlier) rest
      return (name,reader) :: tail

def Aligned {V : Type} (world : Act → Prop) (plans : Plans V) (readers : Readers V) : Prop :=
  List.Forall₂ (fun p r => p.1 = r.1 ∧ Agrees world p.2 r.2) plans readers

def FieldsCorrespond {V : Type} (world : Act → Prop) : Option (Plans V) → Option (Readers V) → Prop
  | none,none => True
  | some plans,some readers => Aligned world plans readers
  | _,_ => False

theorem related_cons {V : Type} {world : Act → Prop} {plans : Plans V} {readers : Readers V}
    (related : Related world plans readers) (name : String) (p : Plan V) (r : Reader V)
    (same : Agrees world p r) : Related world ((name,p)::plans) ((name,r)::readers) := by
  intro query
  by_cases equal : query = name
  · simpa [List.lookup_cons,equal,Corresponds] using same
  · simpa [List.lookup_cons,beq_eq_false_iff_ne.mpr equal] using related query

/-- Arbitrary ordered clauses: no detached source-replay semantics is used. -/
theorem compile_fields_refinement {V : Type} (world : Act → Prop) {plans : Plans V} {readers : Readers V}
    (related : Related world plans readers) (fields : List (String × Rule V)) :
    FieldsCorrespond world (compileFields plans fields) (interpretFields world readers fields) := by
  induction fields generalizing plans readers with
  | nil => exact List.Forall₂.nil
  | cons field rest ih =>
    obtain ⟨name,rule⟩ := field
    have head := compile_rule_refinement world related rule
    cases hp : compileRule plans rule <;> cases hr : interpretRule world readers rule <;>
      simp [hp,hr,Corresponds] at head <;>
      simp [compileFields,interpretFields,hp,hr,FieldsCorrespond]
    next p r =>
      have tail := ih (related_cons related name p r head)
      cases tp : compileFields ((name,p)::plans) rest <;>
        cases tr : interpretFields world ((name,r)::readers) rest <;>
        simp [tp,tr,FieldsCorrespond] at tail <;> simp [tp,tr,FieldsCorrespond]
      exact .cons ⟨rfl,head⟩ tail

/-- Installation rejects duplicate state names in addition to unresolved
references. Decoders/closures are already recognized immutable metadata. -/
def compileClause {V : Type} (fields : List (String × Rule V)) : Option (Plans V) :=
  if (fields.map Prod.fst).Nodup then compileFields [] fields else none

noncomputable def interpretClause {V : Type} (world : Act → Prop)
    (fields : List (String × Rule V)) : Option (Readers V) :=
  if (fields.map Prod.fst).Nodup then interpretFields world [] fields else none

theorem installed_clause_refinement {V : Type} (world : Act → Prop) (fields : List (String × Rule V)) :
    FieldsCorrespond world (compileClause fields) (interpretClause world fields) := by
  unfold compileClause interpretClause
  split
  · exact compile_fields_refinement world (plans := []) (readers := []) (fun _ => True.intro) fields
  · trivial

/-- Successful compilation preserves every named observed value and its fault
evidence, in clause order. The interpreter is independent of compiled plans. -/
theorem installed_rule_plan_refinement {V : Type} (world : Act → Prop)
    (fields : List (String × Rule V)) (plans : Plans V) (compiled : compileClause fields = some plans) :
    ∃ readers, interpretClause world fields = some readers ∧
      ∀ A, CausallyClosed world A →
        plans.map (fun (name,p) => (name,observe world p A)) =
        readers.map (fun (name,r) => (name,r A)) := by
  have related := installed_clause_refinement world fields
  rw [compiled] at related
  cases interpreted : interpretClause world fields with
  | none => simp [interpreted,FieldsCorrespond] at related
  | some readers =>
    refine ⟨readers,rfl,?_⟩
    simp only [interpreted,FieldsCorrespond,Aligned] at related
    intro A closed
    clear compiled interpreted
    induction related with
    | nil => rfl
    | @cons p r ps rs head tail ih =>
      simp only [List.map_cons,head.1,head.2 A closed,ih]

/-- Independent name-dependency inventory of the installed IR. -/
def references {V : Type} : Rule V → List String
  | .source _ => []
  | .earlier name | .derived _ name | .threshold _ _ name | .thresholdLift _ _ name | .freeze _ name => [name]
  | .pair _ left right => [left,right]

def WellScoped {V : Type} : List String → List (String × Rule V) → Prop
  | _,[] => True
  | names,(name,rule)::rest => (∀ reference ∈ references rule, reference ∈ names) ∧ WellScoped (name::names) rest

theorem lookup_present {V : Type} (plans : Plans V) (name : String) :
    (plans.lookup name).isSome = true ↔ name ∈ plans.map Prod.fst := by
  induction plans with
  | nil => simp
  | cons binding rest ih =>
    obtain ⟨key,plan⟩ := binding
    by_cases equal : name = key
    · simp [equal,List.lookup_cons]
    · simp [List.lookup_cons,beq_eq_false_iff_ne.mpr equal,equal,ih]

theorem compile_rule_complete {V : Type} (plans : Plans V) (rule : Rule V)
    (wellScoped : ∀ name ∈ references rule, name ∈ plans.map Prod.fst) :
    ∃ plan, compileRule plans rule = some plan := by
  have lookup : ∀ name ∈ references rule, ∃ plan, plans.lookup name = some plan := by
    intro name member
    have present := (lookup_present plans name).mpr (wellScoped name member)
    cases h : plans.lookup name with
    | none => simp [h] at present
    | some p => exact ⟨p,rfl⟩
  cases rule with
  | source source => exact ⟨_,rfl⟩
  | earlier name => exact lookup name (by simp [references])
  | derived post name =>
    obtain ⟨p,h⟩ := lookup name (by simp [references])
    exact ⟨.map post p,by simp [compileRule,h]⟩
  | threshold alternatives test name =>
    obtain ⟨p,h⟩ := lookup name (by simp [references])
    exact ⟨.thresholdOn alternatives test p,by simp [compileRule,h]⟩
  | thresholdLift spec embed name =>
    obtain ⟨p,h⟩ := lookup name (by simp [references])
    exact ⟨.embed embed (.threshold spec p),by simp [compileRule,h]⟩
  | freeze spec name =>
    obtain ⟨p,h⟩ := lookup name (by simp [references])
    exact ⟨.freeze spec p,by simp [compileRule,h]⟩
  | pair combine left right =>
    obtain ⟨p,hp⟩ := lookup left (by simp [references])
    obtain ⟨r,hr⟩ := lookup right (by simp [references])
    exact ⟨.map (fun (a,b) => combine a b) (.pair p r),by simp [compileRule,hp,hr]⟩

theorem compile_fields_complete {V : Type} (plans : Plans V) (fields : List (String × Rule V))
    (wellScoped : WellScoped (plans.map Prod.fst) fields) :
    ∃ compiled, compileFields plans fields = some compiled := by
  induction fields generalizing plans with
  | nil => exact ⟨[],rfl⟩
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    obtain ⟨head,tail⟩ := wellScoped
    obtain ⟨p,hp⟩ := compile_rule_complete plans rule head
    obtain ⟨compiled,hc⟩ := ih ((name,p)::plans) tail
    exact ⟨(name,p)::compiled,by simp [compileFields,hp,hc]⟩

/-- No independently well-wellScoped, uniquely named installed clause is rejected. -/
theorem installed_clause_complete {V : Type} (fields : List (String × Rule V))
    (unique : (fields.map Prod.fst).Nodup) (wellScoped : WellScoped [] fields) :
    ∃ plans, compileClause fields = some plans := by
  obtain ⟨plans,h⟩ := compile_fields_complete [] fields wellScoped
  exact ⟨plans,by simp [compileClause,unique,h]⟩

/-- Compiler correctness plus the plan theorem yields convergence of the
independent installed-rule interpreter, for arbitrary ordered declarations. -/
theorem installed_observations_setEq {V : Type} (world : Act → Prop)
    (fields : List (String × Rule V)) (plans : Plans V) (compiled : compileClause fields = some plans)
    {A B : List Act} (ua : NodupAddr A) (ub : NodupAddr B) (same : SetEq A B)
    (ca : CausallyClosed world A) (cb : CausallyClosed world B) :
    ∃ readers, interpretClause world fields = some readers ∧
      readers.map (fun (name,r) => (name,r A)) = readers.map (fun (name,r) => (name,r B)) := by
  obtain ⟨readers,interpreted,equal⟩ := installed_rule_plan_refinement world fields plans compiled
  refine ⟨readers,interpreted,?_⟩
  rw [← equal A ca,← equal B cb]
  apply List.map_congr_left
  intro binding _
  obtain ⟨name,p⟩ := binding
  simp only [observe_setEq world p ua ub same]

end CBCL.StateInstalledCompiler
