import LeanCbcl.StateFreezeWitnessReplay
import LeanCbcl.StateCompiledFreezeGrowth

/-! Cross-history replay for actual compiled dependency paths with regenerated
freeze contributor predicates. -/
set_option autoImplicit false
namespace CBCL.StateReplayPaths
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateWitnessReplay StateResourceReplay StateFreezeWitnessReplay StateAuthoredBindings

/-- Optional error union preserves both cross-history replay certificates. -/
theorem union_cross_replays (leftA rightA leftB rightB : Error) (A B : List Act)
    (hl : CrossReplays A B leftA leftB) (hr : CrossReplays A B rightA rightB) :
    CrossReplays A B (unionError leftA rightA) (unionError leftB rightB) := by
  intro e fault accepted
  cases la : leftA with
  | none =>
    cases ra : rightA with
    | none => simp [la,ra,unionError] at fault
    | some old =>
      have same : old = e := by simpa [la,ra,unionError] using fault
      subst e
      obtain ⟨later,current,contains⟩ := hr old ra accepted
      cases lb : leftB with
      | none => exact ⟨later,by simp [current,unionError],contains⟩
      | some other => exact ⟨other ∪ later,by simp [current,unionError],fun id member => Or.inr (contains id member)⟩
  | some first =>
    cases ra : rightA with
    | none =>
      have same : first = e := by simpa [la,ra,unionError] using fault
      subst e
      obtain ⟨later,current,contains⟩ := hl first la accepted
      cases rb : rightB with
      | none => exact ⟨later,by simp [current,unionError],contains⟩
      | some other => exact ⟨later ∪ other,by simp [current,unionError],fun id member => Or.inl (contains id member)⟩
    | some second =>
      have same : first ∪ second = e := by simpa [la,ra,unionError] using fault
      subst e
      obtain ⟨laterLeft,currentLeft,containsLeft⟩ := hl first la (accepts_union_left accepted)
      obtain ⟨laterRight,currentRight,containsRight⟩ := hr second ra (accepts_union_right accepted)
      exact ⟨laterLeft ∪ laterRight,by simp [currentLeft,currentRight,unionError],
        fun id member => member.elim (fun h => Or.inl (containsLeft id h)) (fun h => Or.inr (containsRight id h))⟩

/-- Raw-error replay and concrete conflict-pair transfer suffice for a full
freeze wrapper. The transfer law is discharged by static or materialized data. -/
theorem freeze_cross_replays (world : Act → Prop) (verb : String) (policy : Bool)
    (leftContribution rightContribution : Act → Prop) (A B : List Act) (rawLeft rawRight : Error)
    (transfer : ∀ {a b}, Accepts A (freezeEvidence world verb leftContribution policy A) B →
      FreezeConflict world verb leftContribution policy A a b →
      FreezeConflict world verb rightContribution policy B a b)
    (rawReplay : CrossReplays A B rawLeft rawRight) :
    CrossReplays A B (freezeFault world verb leftContribution policy rawLeft A)
      (freezeFault world verb rightContribution policy rawRight B) := by
  classical
  intro e fault accepted
  unfold freezeFault at fault ⊢
  split at fault
  · rename_i reason
    have same := Option.some.inj fault
    subst e
    have rawAccepted := accepts_union_left accepted
    have freezeAccepted := accepts_union_right accepted
    have freezeGrows : ∀ id ∈ freezeEvidence world verb leftContribution policy A,
        id ∈ freezeEvidence world verb rightContribution policy B := by
      rintro id ⟨a,b,conflict,which⟩
      exact ⟨a,b,transfer freezeAccepted conflict,which⟩
    have rawGrows : ∀ old, rawLeft = some old → ∃ later, rawRight = some later ∧ ∀ id ∈ old, id ∈ later := by
      intro old observed
      apply rawReplay old observed
      simpa [observed] using rawAccepted
    have currentReason : rawRight.isSome ∨ ∃ a b,
        FreezeConflict world verb rightContribution policy B a b := by
      rcases reason with rawFault | ⟨a,b,conflict⟩
      · cases observed : rawLeft with
        | none => simp [observed] at rawFault
        | some old =>
          obtain ⟨later,current,_⟩ := rawGrows old observed
          exact Or.inl (by simp [current])
      · exact Or.inr ⟨a,b,transfer freezeAccepted conflict⟩
    refine ⟨rawRight.getD ∅ ∪ freezeEvidence world verb rightContribution policy B,
      if_pos currentReason,?_⟩
    intro id member
    rcases member with rawMember | freezeMember
    · cases observed : rawLeft with
      | none =>
        have impossible : id ∈ (∅ : Evidence) := by simpa [observed] using rawMember
        exact False.elim impossible
      | some old =>
        obtain ⟨later,current,contains⟩ := rawGrows old observed
        exact Or.inl (by simpa [current] using contains id (by simpa [observed] using rawMember))
    · exact Or.inr (freezeGrows id freezeMember)
  · contradiction

/-- Structurally corresponding paths with static primitive sources and either
fixed or freshly materialized freeze predicates. -/
inductive Related (domains : List StateInstalledDomains.Domain) (A B : List Act) : Path → Path → Prop where
  | same (source : Path) (checked : CertifiedReplay A B source) : Related domains A B source source
  | join {leftA leftB rightA rightB} : Related domains A B leftA leftB → Related domains A B rightA rightB →
      Related domains A B (.join leftA rightA) (.join leftB rightB)
  | freeze (verb : String) (contribution : Act → Prop) (policy : Bool) {left right} :
      Related domains A B left right →
      Related domains A B (.freeze verb contribution policy left) (.freeze verb contribution policy right)
  | materialized (verb : String) (footprint : Footprint) (policy : Bool) {left right} :
      Related domains A B left right →
      Related domains A B (.freeze verb (contributes domains A footprint) policy left)
        (.freeze verb (contributes domains B footprint) policy right)

/-- Related compiled paths replay all faults and containing evidence after
accepting only the named acts, under the actual causal-closure premises. -/
theorem related_replays (world : Act → Prop) (domains : List StateInstalledDomains.Domain)
    (A B : List Act) (unique : NodupAddr A) (sourceClosed : CausallyClosed world A)
    (receiverClosed : CausallyClosed world B) {left right : Path}
    (related : Related domains A B left right) :
    CrossReplays A B (errors world left A) (errors world right B) := by
  induction related with
  | same source checked => exact paths_replay world source sourceClosed checked
  | join left right ihLeft ihRight => exact union_cross_replays _ _ _ _ A B ihLeft ihRight
  | freeze verb contribution policy relation ih =>
    apply freeze_cross_replays world verb policy contribution contribution A B _ _ _ ih
    intro a b accepted conflict
    have original := freeze_witness_accepted conflict
    exact freeze_witness_transfer sourceClosed conflict
      (accepted a original.1 ⟨a,b,conflict,Or.inl rfl⟩)
      (accepted b original.2 ⟨a,b,conflict,Or.inr rfl⟩)
  | materialized verb footprint policy relation ih =>
    exact freeze_fault_replays world domains footprint verb policy _ _ unique sourceClosed receiverClosed ih

/-- Optional lookups preserve both rejection and related compiled paths. -/
inductive Match (domains : List StateInstalledDomains.Domain) (A B : List Act) : Option Path → Option Path → Prop where
  | none : Match domains A B none none
  | some {left right} : Related domains A B left right → Match domains A B (some left) (some right)

/-- Mapping corresponding constructors preserves path lookup status. -/
theorem match_map {domains : List StateInstalledDomains.Domain} {A B : List Act} {left right : Option Path}
    (related : Match domains A B left right) (f g : Path → Path)
    (preserves : ∀ a b, Related domains A B a b → Related domains A B (f a) (g b)) :
    Match domains A B (left.map f) (right.map g) := by
  cases related with
  | none => exact .none
  | some paths => exact .some (preserves _ _ paths)

/-- Both product dependencies retain their path relation. -/
theorem match_join {domains : List StateInstalledDomains.Domain} {A B : List Act} {a b c d : Option Path}
    (ac : Match domains A B a c) (bd : Match domains A B b d) :
    Match domains A B (a.bind (fun left => b.bind (fun right => some (Path.join left right))))
      (c.bind (fun left => d.bind (fun right => some (Path.join left right)))) := by
  cases ac with
  | none => exact .none
  | some left =>
    cases bd with
    | none => exact .none
    | some right => exact .some (.join left right)

/-- Corresponding earlier names carry related dependency paths. -/
def Environments (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : List (String × Path)) : Prop :=
  ∀ name, Match domains A B (left.lookup name) (right.lookup name)

/-- Actual installed-rule path elaboration preserves the cross-history
relation, using concrete certification only at primitive source leaves. -/
theorem rule_path_related {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : List (String × Path)) (related : Environments domains A B left right)
    (rule : Rule V) (source : StateInstalledReplay.RuleCertified A B rule) :
    Match domains A B (StateCompiledFreezeGrowth.rulePath left rule) (StateCompiledFreezeGrowth.rulePath right rule) := by
  cases rule with
  | source leaf => exact .some (.same _ source)
  | earlier name | derived post name | threshold alternatives test name | thresholdRaw alternatives test state name =>
    exact related name
  | pair combine first second =>
    simpa [StateCompiledFreezeGrowth.rulePath] using match_join (related first) (related second)
  | thresholdLift spec embed name =>
    exact match_map (related name) _ _ (fun _ _ relation => .join (.same _ trivial) relation)
  | freeze spec name =>
    exact match_map (related name) _ _ (fun _ _ relation => .freeze spec.verb spec.contributes spec.policy relation)

/-- Regenerated global freeze metadata keeps verb, policy and footprint. -/
inductive FreezeMatch (domains : List StateInstalledDomains.Domain) (A B : List Act) :
    Option FreezeSpec → Option FreezeSpec → Prop where
  | none : FreezeMatch domains A B none none
  | materialized (verb : String) (footprint : Footprint) (policy : Bool) :
      FreezeMatch domains A B (some ⟨verb,contributes domains A footprint,policy⟩)
        (some ⟨verb,contributes domains B footprint,policy⟩)

/-- Every global target has corresponding materialized freeze metadata. -/
def Decorations (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : List (String × FreezeSpec)) : Prop :=
  ∀ name, FreezeMatch domains A B (left.lookup name) (right.lookup name)

/-- Global freeze attachment preserves the cross-history relation. -/
theorem decorate_related {domains : List StateInstalledDomains.Domain} {A B : List Act}
    {left right : Option FreezeSpec} (metadata : FreezeMatch domains A B left right)
    {a b : Path} (related : Related domains A B a b) :
    Related domains A B (StateCompiledFreezeGrowth.decorate left a) (StateCompiledFreezeGrowth.decorate right b) := by
  cases metadata with
  | none => exact related
  | materialized verb footprint policy => exact .materialized verb footprint policy related

/-- Extending both compiled prefixes preserves exact named lookup relations. -/
theorem extend_related (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : List (String × Path)) (related : Environments domains A B left right)
    (name : String) (a b : Path) (head : Related domains A B a b) :
    Environments domains A B ((name,a)::left) ((name,b)::right) := by
  intro key
  by_cases same : key = name
  · subst key
    simpa [List.lookup] using Match.some head
  · simpa [List.lookup,beq_eq_false_iff_ne.mpr same] using related key

/-- Both compilations reject together or emit ordered, name-aligned paths. -/
def Outputs (domains : List StateInstalledDomains.Domain) (A B : List Act) :
    Option (List (String × Path)) → Option (List (String × Path)) → Prop
  | none,none => True
  | some left,some right => List.Forall₂ (fun a b => a.1 = b.1 ∧ Related domains A B a.2 b.2) left right
  | _,_ => False

/-- The exact ordered path compiler preserves replay relations through all
backward dependencies and newly materialized global freezes. -/
theorem fields_related {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (rules : List (String × Rule V)) (sources : ∀ binding ∈ rules, StateInstalledReplay.RuleCertified A B binding.2)
    (left right : List (String × Path)) (earlier : Environments domains A B left right)
    (first second : List (String × FreezeSpec)) (metadata : Decorations domains A B first second) :
    Outputs domains A B (StateCompiledFreezeGrowth.fields left first rules)
      (StateCompiledFreezeGrowth.fields right second rules) := by
  induction rules generalizing left right with
  | nil => exact .nil
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    have head := rule_path_related domains A B left right earlier rule (sources (name,rule) (by simp))
    generalize leftFound : StateCompiledFreezeGrowth.rulePath left rule = leftPath at head
    generalize rightFound : StateCompiledFreezeGrowth.rulePath right rule = rightPath at head
    cases head with
    | none => simp [StateCompiledFreezeGrowth.fields,leftFound,rightFound,Outputs]
    | @some a b relation =>
      have decorated := decorate_related (metadata name) relation
      have tail := ih (fun binding member => sources binding (List.mem_cons_of_mem (name,rule) member)) ((name,StateCompiledFreezeGrowth.decorate (first.lookup name) a)::left) ((name,StateCompiledFreezeGrowth.decorate (second.lookup name) b)::right)
        (extend_related domains A B left right earlier name _ _ decorated)
      cases leftTail : StateCompiledFreezeGrowth.fields ((name,StateCompiledFreezeGrowth.decorate (first.lookup name) a)::left) first rest with
      | none =>
        cases rightTail : StateCompiledFreezeGrowth.fields ((name,StateCompiledFreezeGrowth.decorate (second.lookup name) b)::right) second rest <;>
          simp [leftTail,rightTail,Outputs] at tail
        simp [StateCompiledFreezeGrowth.fields,leftFound,rightFound,leftTail,rightTail,Outputs]
      | some leftMore =>
        cases rightTail : StateCompiledFreezeGrowth.fields ((name,StateCompiledFreezeGrowth.decorate (second.lookup name) b)::right) second rest with
        | none => simp [leftTail,rightTail,Outputs] at tail
        | some rightMore =>
          simp only [leftTail,rightTail,Outputs] at tail
          simp only [StateCompiledFreezeGrowth.fields,leftFound,rightFound,Bind.bind,Option.bind,leftTail,rightTail,Outputs]
          exact List.Forall₂.cons ⟨rfl,decorated⟩ tail


/-- Actual materialization preserves its template identity at every target. -/
theorem authored_decorations (domains : List StateInstalledDomains.Domain)
    (templates : List FreezeTemplate) (A B : List Act) :
    Decorations domains A B (materialize domains A templates) (materialize domains B templates) := by
  induction templates with
  | nil => intro name; exact .none
  | cons template rest ih =>
    intro name
    by_cases same : name = template.field
    · subst name
      simpa [materialize,List.lookup] using
        FreezeMatch.materialized template.verb template.footprint template.policy
    · simpa [materialize,List.lookup,beq_eq_false_iff_ne.mpr same] using ih name

/-- Related path compilation is the exact projection of both actual plan lists. -/
theorem compiled_paths_related {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (rules : List (String × Rule V)) (sources : ∀ binding ∈ rules, StateInstalledReplay.RuleCertified A B binding.2)
    (templates : List FreezeTemplate) (left right : Plans V)
    (first : StateInstalledClause.compileFields [] (StateInstalledClause.attach (materialize domains A templates) rules) = some left)
    (second : StateInstalledClause.compileFields [] (StateInstalledClause.attach (materialize domains B templates) rules) = some right) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ Related domains A B a.2 b.2)
      (StateCompiledFreezeGrowth.paths left) (StateCompiledFreezeGrowth.paths right) := by
  have relation := fields_related domains A B rules sources [] [] (by intro name; exact .none)
    _ _ (authored_decorations domains templates A B)
  change Outputs domains A B
    (StateCompiledFreezeGrowth.fields (StateCompiledFreezeGrowth.paths ([] : Plans V)) _ rules)
    (StateCompiledFreezeGrowth.fields (StateCompiledFreezeGrowth.paths ([] : Plans V)) _ rules) at relation
  rw [← StateCompiledFreezeGrowth.compile_fields_path ([] : Plans V) _ rules,
    ← StateCompiledFreezeGrowth.compile_fields_path ([] : Plans V) _ rules,first,second] at relation
  exact relation

/-- Both successful authored compilations have corresponding actual error
paths, with concrete source certificates derived from their static preparation. -/
theorem authored_paths_related (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (prepared : Prepared) (installed : prepareStatic environment entries = some prepared)
    (A B : List Act) (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (left right : Plans StateInstalledLegacy.Value)
    (leftCompiled : StateAuthoredBindings.compile environment entries A = some left)
    (rightCompiled : StateAuthoredBindings.compile environment entries B = some right) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ Related prepared.domains A B a.2 b.2)
      (StateCompiledFreezeGrowth.paths left) (StateCompiledFreezeGrowth.paths right) := by
  have leftClause : StateInstalledLowering.compile (clauseAt prepared A) = some left := by
    simpa [StateAuthoredBindings.compile,prepare,installed,clauseAt] using leftCompiled
  have rightClause : StateInstalledLowering.compile (clauseAt prepared B) = some right := by
    simpa [StateAuthoredBindings.compile,prepare,installed,clauseAt] using rightCompiled
  cases resolved : StateInstalledLowering.resolve [] prepared.declarations with
  | none => simp [StateInstalledLowering.compile,clauseAt,resolved] at leftClause
  | some rules =>
    have sources := StateAuthoredReplay.resolve_certified prepared.declarations A B
      (StateAuthoredReplay.prepared_declarations_certified world environment entries prepared valid closed rooted installed)
      [] rules resolved
    have first : StateInstalledClause.compileFields []
        (StateInstalledClause.attach (materialize prepared.domains A prepared.freezes) rules) = some left := by
      unfold StateInstalledLowering.compile at leftClause
      split at leftClause
      · simpa [clauseAt,resolved] using leftClause
      · contradiction
    have second : StateInstalledClause.compileFields []
        (StateInstalledClause.attach (materialize prepared.domains B prepared.freezes) rules) = some right := by
      unfold StateInstalledLowering.compile at rightClause
      split at rightClause
      · simpa [clauseAt,resolved] using rightClause
      · contradiction
    exact compiled_paths_related prepared.domains A B rules sources prepared.freezes left right first second

/-- Aligned named paths transfer a fault from its reported acts rather than
assuming that the receiver contains the whole previous accepted history. -/
theorem named_fault_transfer (world : Act → Prop) {A B : List Act} {left right : List (String × Path)}
    (related : List.Forall₂ (fun a b => a.1 = b.1 ∧ CrossReplays A B (errors world a.2 A) (errors world b.2 B)) left right)
    (name : String) (source : Path) (member : (name,source) ∈ left) (evidence : Evidence)
    (fault : errors world source A = some evidence) (accepted : Accepts A evidence B) :
    ∃ target enlarged, (name,target) ∈ right ∧ errors world target B = some enlarged ∧
      ∀ id ∈ evidence, id ∈ enlarged := by
  induction related with
  | nil => simp at member
  | @cons a b left right head tail ih =>
    rcases List.mem_cons.mp member with same | more
    · have nameEqual : name = b.1 := (congrArg Prod.fst same).trans head.1
      have pathEqual : source = a.2 := congrArg Prod.snd same
      obtain ⟨enlarged,result,includes⟩ := head.2 evidence (by simpa [pathEqual] using fault) accepted
      exact ⟨b.2,enlarged,List.mem_cons.mpr (Or.inl (by cases b; simp_all)),result,includes⟩
    · obtain ⟨target,enlarged,inside,result,includes⟩ := ih more
      exact ⟨target,enlarged,List.mem_cons_of_mem _ inside,result,includes⟩

/-- Reported witnesses reproduce the same named fault in a separately compiled
receiver plan, including freshly materialized contributor predicates. -/
theorem authored_fault_replays (world : Act → Prop) (environment : Environment) (entries : List Entry)
    {A B : List Act} (unique : NodupAddr A) (valid : ∀ act ∈ A, world act)
    (sourceClosed : CausallyClosed world A) (receiverClosed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (left right : Plans StateInstalledLegacy.Value)
    (leftCompiled : StateAuthoredBindings.compile environment entries A = some left)
    (rightCompiled : StateAuthoredBindings.compile environment entries B = some right)
    (name : String) (source : Plan StateInstalledLegacy.Value) (member : (name,source) ∈ left) (e : Evidence)
    (fault : observe world source A = .fault e) (accepted : Accepts A e B) :
    ∃ target enlarged, (name,target) ∈ right ∧ observe world target B = .fault enlarged ∧
      ∀ id ∈ e, id ∈ enlarged := by
  cases installed : prepareStatic environment entries with
  | none => simp [StateAuthoredBindings.compile,prepare,installed] at leftCompiled
  | some prepared =>
    have relation := authored_paths_related world environment entries prepared installed A B valid receiverClosed rooted
      left right leftCompiled rightCompiled
    have cross : List.Forall₂ (fun a b => a.1 = b.1 ∧ CrossReplays A B (errors world a.2 A) (errors world b.2 B))
        (StateCompiledFreezeGrowth.paths left) (StateCompiledFreezeGrowth.paths right) := by
      generalize StateCompiledFreezeGrowth.paths left = leftPaths at relation ⊢
      generalize StateCompiledFreezeGrowth.paths right = rightPaths at relation ⊢
      induction relation with
      | nil => exact .nil
      | cons head tail ih =>
        exact .cons ⟨head.1,related_replays world prepared.domains A B unique sourceClosed receiverClosed head.2⟩ ih
    have original : errors world (path source) A = some e := by
      cases observed : errors world (path source) A with
      | none => simp [observe,observed] at fault
      | some actual =>
        have same : actual = e := by simpa [observe,observed] using fault
        simpa [same] using observed
    have present : (name,path source) ∈ StateCompiledFreezeGrowth.paths left := List.mem_map.mpr ⟨(name,source),member,rfl⟩
    obtain ⟨targetPath,enlarged,targetMember,current,contains⟩ :=
      named_fault_transfer world cross name (path source) present e original accepted
    obtain ⟨binding,inside,equal⟩ := List.mem_map.mp targetMember
    have nameEqual : binding.1 = name := congrArg Prod.fst equal
    have pathEqual : path binding.2 = targetPath := congrArg Prod.snd equal
    exact ⟨binding.2,enlarged,by simpa [← nameEqual] using inside,
      by simp [observe,pathEqual,current],contains⟩

/-- Static successful authored preparation compiles at any receiving history;
this needs neither source-history growth nor receipt of unrelated acts. -/
theorem authored_recompiles (environment : Environment) (entries : List Entry) (A B : List Act)
    (left : Plans StateInstalledLegacy.Value)
    (compiled : StateAuthoredBindings.compile environment entries A = some left) :
    ∃ right, StateAuthoredBindings.compile environment entries B = some right := by
  cases installed : prepareStatic environment entries with
  | none => simp [StateAuthoredBindings.compile,prepare,installed] at compiled
  | some prepared =>
    apply prepared_compiler_complete environment entries B (clauseAt prepared B)
    simp [prepare,installed,clauseAt]

/-- A receiver holding the reported witness can recompile the clause and
reproduce its named fault with containing evidence. -/
theorem authored_fault_recompiles (world : Act → Prop) (environment : Environment) (entries : List Entry)
    {A B : List Act} (unique : NodupAddr A) (valid : ∀ act ∈ A, world act)
    (sourceClosed : CausallyClosed world A) (receiverClosed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (left : Plans StateInstalledLegacy.Value) (compiled : StateAuthoredBindings.compile environment entries A = some left)
    (name : String) (source : Plan StateInstalledLegacy.Value) (member : (name,source) ∈ left) (e : Evidence)
    (fault : observe world source A = .fault e) (accepted : Accepts A e B) :
    ∃ right target enlarged, StateAuthoredBindings.compile environment entries B = some right ∧
      (name,target) ∈ right ∧ observe world target B = .fault enlarged ∧ ∀ id ∈ e, id ∈ enlarged := by
  obtain ⟨right,rightCompiled⟩ := authored_recompiles environment entries A B left compiled
  obtain ⟨target,enlarged,present,current,contains⟩ := authored_fault_replays world environment entries unique valid
    sourceClosed receiverClosed rooted left right compiled rightCompiled name source member e fault accepted
  exact ⟨right,target,enlarged,rightCompiled,present,current,contains⟩

open StateKernelDelivery AdmissionStratification StateRefinement

/-- Reliable delivery transfers exactly the reported actual witness acts.
Every later receiver compilation faults in the same named observation, with
all previous evidence retained. Structural causal coverage is explicit. -/
theorem eventual_authored_witness_fault {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (environment : Environment) (entries : List Entry)
    (atTime : Nat) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateAuthoredBindings.compile environment entries (left.run atTime).accepted = some plans)
    (name : String) (source : Plan StateInstalledLegacy.Value) (member : (name,source) ∈ plans) (e : Evidence)
    (fault : observe H.contains source (left.run atTime).accepted = .fault e) :
    ∃ witness : List Act,
      (∀ act, act ∈ witness ↔ act ∈ (left.run atTime).accepted ∧ act.addr ∈ e) ∧
      ∃ time, ∀ n, time ≤ n → ∃ current target enlarged,
        StateAuthoredBindings.compile environment entries (right.run n).accepted = some current ∧
        (name,target) ∈ current ∧ observe H.contains target (right.run n).accepted = .fault enlarged ∧
        ∀ id ∈ e, id ∈ enlarged := by
  classical
  let witness := (left.run atTime).accepted.filter (fun act => decide (act.addr ∈ e))
  have exactWitness : ∀ act, act ∈ witness ↔ act ∈ (left.run atTime).accepted ∧ act.addr ∈ e := by
    intro act
    simp [witness]
  obtain ⟨time,delivered⟩ := witness_dissemination left right witness atTime
    (fun act inside => ((exactWitness act).mp inside).1)
  have unique := (reachable_wellFormed (behavior_reachable left.behavior atTime)).accepted_unique
  have rooted := StateContextReplay.rooted_openers_of_dependencies H causal (StateInstalledContext.evidenceInput environment.profile)
  refine ⟨witness,exactWitness,time,fun n later => ?_⟩
  apply authored_fault_recompiles H.contains environment entries unique (accepted_valid left atTime)
    (replica_causal_closed left admission atTime) (replica_causal_closed right admission n) rooted
    plans compiled name source member e fault
  intro act inside named
  exact delivered n later act ((exactWitness act).mpr ⟨inside,named⟩)

end CBCL.StateReplayPaths
