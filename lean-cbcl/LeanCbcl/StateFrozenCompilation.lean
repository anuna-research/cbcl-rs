import LeanCbcl.StateFrozenPayload

/-! Actual ordered source compilation preserves payload structure across freshly
materialized freeze metadata. -/
set_option autoImplicit false
namespace CBCL.StateFrozenCompilation
open State StateObservation StateObservationPlan StateInstalledCompiler StateAuthoredBindings
open StateFrozenPayload

/-- Optional plan compilation preserves both failure and related successful plans. -/
inductive Match {V : Type} : Option (Plan V) → Option (Plan V) → Prop where
  | none : Match none none
  | some {left right : Plan V} : Related left right → Match (some left) (some right)

/-- A plan constructor preserves matched optional compilation. -/
theorem match_map {V W : Type} {left right : Option (Plan V)} (matched : Match left right)
    (f g : Plan V → Plan W) (preserves : ∀ a b, Related a b → Related (f a) (g b)) :
    Match (left.map f) (right.map g) := by
  cases matched with
  | none => exact .none
  | some relation => exact .some (preserves _ _ relation)

/-- Both product dependencies retain their compiled relation. -/
theorem match_pair {V : Type} {a b c d : Option (Plan V)} (left : Match a c) (right : Match b d)
    (combine : V → V → V) :
    Match (a.bind (fun x => b.bind (fun y => some (.map (fun (u,v) => combine u v) (.pair x y)))))
      (c.bind (fun x => d.bind (fun y => some (.map (fun (u,v) => combine u v) (.pair x y))))) := by
  cases left with
  | none => exact .none
  | some l =>
    cases right with
    | none => exact .none
    | some r => exact .some (.map _ (.pair l r))

/-- Each earlier source name retains a matched compiled plan. -/
def Environments {V : Type} (left right : Plans V) : Prop :=
  ∀ name, Match (left.lookup name) (right.lookup name)

/-- Every actual installed rule preserves the payload relation through lookup. -/
theorem rule_related {V : Type} (left right : Plans V) (related : Environments left right) (rule : Rule V) :
    Match (compileRule left rule) (compileRule right rule) := by
  cases rule with
  | source source => exact .some (.source source)
  | earlier name => exact related name
  | derived post name =>
    have head := match_map (related name) _ _ (fun _ _ relation => .map post relation)
    cases l : left.lookup name <;> cases r : right.lookup name <;> simpa [compileRule,l,r] using head
  | threshold alternatives test name =>
    have head := match_map (related name) _ _ (fun _ _ relation => .thresholdOn alternatives test relation)
    cases l : left.lookup name <;> cases r : right.lookup name <;> simpa [compileRule,l,r] using head
  | thresholdRaw alternatives test state name =>
    have head := match_map (related name) _ _ (fun _ _ relation => .thresholdRaw alternatives test state relation)
    cases l : left.lookup name <;> cases r : right.lookup name <;> simpa [compileRule,l,r] using head
  | thresholdLift spec embed name =>
    have head := match_map (related name) _ _ (fun _ _ relation => .embed embed (.threshold spec relation))
    cases l : left.lookup name <;> cases r : right.lookup name <;> simpa [compileRule,l,r] using head
  | freeze spec name =>
    have head := match_map (related name) _ _ (fun _ _ relation =>
      .freeze spec.verb spec.policy spec.contributes spec.contributes relation)
    cases l : left.lookup name <;> cases r : right.lookup name <;> simpa [compileRule,l,r] using head
  | pair combine first second =>
    simpa only [compileRule,Bind.bind,Option.bind] using match_pair (related first) (related second) combine

/-- Attaching regenerated freeze metadata retains the same source computation. -/
theorem field_related {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : Plans V) (related : Environments left right) (rule : Rule V)
    (first second : Option FreezeSpec) (metadata : StateReplayPaths.FreezeMatch domains A B first second) :
    Match (StateInstalledClause.compileField left ⟨rule,first⟩)
      (StateInstalledClause.compileField right ⟨rule,second⟩) := by
  have head := rule_related left right related rule
  generalize l : compileRule left rule = leftPlan at head
  generalize r : compileRule right rule = rightPlan at head
  cases head with
  | none => simp [StateInstalledClause.compileField,l,r]; exact .none
  | some relation =>
    cases metadata with
    | none => simpa [StateInstalledClause.compileField,l,r] using Match.some relation
    | materialized verb footprint policy =>
      simpa [StateInstalledClause.compileField,l,r] using Match.some
        (Related.freeze verb policy (contributes domains A footprint) (contributes domains B footprint) relation)

/-- Extending the compiler dictionary retains the relation at every name. -/
theorem extend_related {V : Type} (left right : Plans V) (related : Environments left right)
    (name : String) (a b : Plan V) (head : Related a b) :
    Environments ((name,a)::left) ((name,b)::right) := by
  intro key
  by_cases same : key = name
  · subst key
    simpa [List.lookup] using Match.some head
  · simpa [List.lookup,beq_eq_false_iff_ne.mpr same] using related key

/-- Entire ordered compilation retains corresponding names and payload structures. -/
def Outputs {V : Type} : Option (Plans V) → Option (Plans V) → Prop
  | none,none => True
  | some left,some right => List.Forall₂ (fun a b => a.1 = b.1 ∧ Related a.2 b.2) left right
  | _,_ => False

/-- The actual attached-field compiler preserves payload structure through all
backward dependencies and freshly regenerated source freezer predicates. -/
theorem fields_related {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (rules : List (String × Rule V)) (left right : Plans V) (earlier : Environments left right)
    (first second : List (String × FreezeSpec))
    (metadata : StateReplayPaths.Decorations domains A B first second) :
    Outputs (StateInstalledClause.compileFields left (StateInstalledClause.attach first rules))
      (StateInstalledClause.compileFields right (StateInstalledClause.attach second rules)) := by
  induction rules generalizing left right with
  | nil => exact .nil
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    change Outputs
      ((StateInstalledClause.compileField left ⟨rule,first.lookup name⟩).bind (fun a =>
        (StateInstalledClause.compileFields ((name,a)::left) (StateInstalledClause.attach first rest)).bind
          (fun tail => some ((name,a)::tail))))
      ((StateInstalledClause.compileField right ⟨rule,second.lookup name⟩).bind (fun b =>
        (StateInstalledClause.compileFields ((name,b)::right) (StateInstalledClause.attach second rest)).bind
          (fun tail => some ((name,b)::tail))))
    have head := field_related domains A B left right earlier rule _ _ (metadata name)
    generalize l : StateInstalledClause.compileField left ⟨rule,first.lookup name⟩ = leftHead at head
    generalize r : StateInstalledClause.compileField right ⟨rule,second.lookup name⟩ = rightHead at head
    cases head with
    | none => simp [Outputs]
    | @some a b relation =>
      have tail := ih ((name,a)::left) ((name,b)::right) (extend_related left right earlier name a b relation)
      cases lt : StateInstalledClause.compileFields ((name,a)::left) (StateInstalledClause.attach first rest) with
      | none =>
        cases rt : StateInstalledClause.compileFields ((name,b)::right) (StateInstalledClause.attach second rest) <;>
          simp [lt,rt,Outputs] at tail
        simp [lt,rt,Outputs]
      | some more =>
        cases rt : StateInstalledClause.compileFields ((name,b)::right) (StateInstalledClause.attach second rest) with
        | none => simp [lt,rt,Outputs] at tail
        | some other =>
          simp only [lt,rt,Outputs] at tail
          simp only [Option.bind_some,lt,rt,Outputs]
          exact List.Forall₂.cons ⟨rfl,relation⟩ tail

/-- Two successful compilations of the same installed rules retain paired
actual source plans under independently materialized freeze metadata. -/
theorem compiled_plans_related {V : Type} (domains : List StateInstalledDomains.Domain)
    (A B : List Act) (rules : List (String × Rule V)) (templates : List FreezeTemplate)
    (left right : Plans V)
    (first : StateInstalledClause.compileFields [] (StateInstalledClause.attach (materialize domains A templates) rules) = some left)
    (second : StateInstalledClause.compileFields [] (StateInstalledClause.attach (materialize domains B templates) rules) = some right) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ Related a.2 b.2) left right := by
  have relation := fields_related domains A B rules [] [] (by intro name; exact .none)
    _ _ (StateReplayPaths.authored_decorations domains templates A B)
  rw [first,second] at relation
  exact relation

/-- Actual authored compilation supplies the related source-plan structures;
no caller provides a dependency, computation or frozen-source correspondence. -/
theorem authored_plans_related (environment : Environment) (entries : List Entry)
    (prepared : Prepared) (installed : prepareStatic environment entries = some prepared)
    (A B : List Act) (left right : Plans StateInstalledLegacy.Value)
    (leftCompiled : StateAuthoredBindings.compile environment entries A = some left)
    (rightCompiled : StateAuthoredBindings.compile environment entries B = some right) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ Related a.2 b.2) left right := by
  have leftClause : StateInstalledLowering.compile (clauseAt prepared A) = some left := by
    simpa [StateAuthoredBindings.compile,prepare,installed,clauseAt] using leftCompiled
  have rightClause : StateInstalledLowering.compile (clauseAt prepared B) = some right := by
    simpa [StateAuthoredBindings.compile,prepare,installed,clauseAt] using rightCompiled
  cases resolved : StateInstalledLowering.resolve [] prepared.declarations with
  | none => simp [StateInstalledLowering.compile,clauseAt,resolved] at leftClause
  | some rules =>
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
    exact compiled_plans_related prepared.domains A B rules prepared.freezes left right first second

end CBCL.StateFrozenCompilation
