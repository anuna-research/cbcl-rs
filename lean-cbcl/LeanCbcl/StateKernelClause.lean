import LeanCbcl.StateKernel

/-!
SPEC-036: fixed surface vocabulary, independently specified rule meaning,
reference elaboration, and arbitrary-clause correctness/completeness.
-/
namespace CBCL.StateKernelClause
open CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries
open CBCL.StateKernelAggregates CBCL.StateKernelExtensions CBCL.StateKernel

/-- Typed surface inventory matching runtime Rule::head. Aliases normalize before this AST. -/
inductive Rule where
  | last (verb field : String)
  | latestPerSigner (verb field : String)
  | latestPerKey (verb key field : String)
  | existsRule (verb : String)
  | count (verb : String)
  | progress (verb : String)
  | events (verb field : String)
  | setUnion (verb field : String)
  | values (verb field : String)
  | valuesPerKey (verb key field : String) (delete : Option String)
  | registerPerKey (verb key field : String) (delete : Option String)
  | observedSet (add remove field : String)
  | counter (increment decrement field : String)
  | histogram (earlier : String)
  | sum (earlier : String)
  | lwwRegister (verb field clock : String)
  | lwwPerSigner (verb field clock : String)
  | lwwMap (verb key field clock : String) (delete : Option String)
  | boundedCounter (configuration : String)
  deriving DecidableEq

/-- Exact public wire head inventory; checked against the Rust enum by a script. -/
def Rule.head : Rule → String
  | .last .. => "last"
  | .latestPerSigner .. => "latest-per-signer"
  | .latestPerKey .. => "latest-per-key"
  | .existsRule .. => "exists"
  | .count .. => "count"
  | .progress .. => "progress"
  | .events .. => "events"
  | .setUnion .. => "set-union"
  | .values .. => "values"
  | .valuesPerKey .. => "values-per-key"
  | .registerPerKey .. => "register-per-key"
  | .observedSet .. => "observed-set"
  | .counter .. => "counter"
  | .histogram .. => "histogram"
  | .sum .. => "sum"
  | .lwwRegister .. => "lww-register"
  | .lwwPerSigner .. => "lww-per-signer"
  | .lwwMap .. => "lww-map"
  | .boundedCounter .. => "bounded-counter"

/-- Canonical aliases preserve the existing rule semantics and body identity. -/
def normalizeHead : String → String
  | "multi-value-register" => "values"
  | "multi-value-map" => "values-per-key"
  | other => other

/-- Independently enumerated scalar/event map sources accepted by derived fields. -/
inductive MapSource : Rule → Prop where
  | signer (v f) : MapSource (.latestPerSigner v f)
  | keyed (v k f) : MapSource (.latestPerKey v k f)
  | register (v k f d) : MapSource (.registerPerKey v k f d)
  | events (v f) : MapSource (.events v f)
  | hlcSigner (v f c) : MapSource (.lwwPerSigner v f c)
  | hlcKeyed (v k f c d) : MapSource (.lwwMap v k f c d)

/-- Histograms accept scalar maps; event histograms remain installation-incompatible. -/
inductive HistogramSource : Rule → Prop where
  | signer (v f) : HistogramSource (.latestPerSigner v f)
  | keyed (v k f) : HistogramSource (.latestPerKey v k f)
  | register (v k f d) : HistogramSource (.registerPerKey v k f d)
  | hlcSigner (v f c) : HistogramSource (.lwwPerSigner v f c)
  | hlcKeyed (v k f c d) : HistogramSource (.lwwMap v k f c d)

/-- Independent map denotation, not a call to elaboration. -/
def SurfaceMapMeaning (input : Input) (domains : List Domain) : Rule → FiniteMap → Prop
  | .latestPerSigner v f, m => MapMeaning input.clock input.signerRank (Admitted domains input.acts)
      ⟨.own v, .signer, .address, f, false⟩ m
  | .latestPerKey v k f, m => MapMeaning input.clock input.signerRank (Admitted domains input.acts)
      ⟨.verb v, .key k, .address, f, false⟩ m
  | .registerPerKey v k f d, m => MapMeaning input.clock input.signerRank (Admitted domains input.acts)
      ⟨.current v (some k) d, .key k, .address, f, false⟩ m
  | .events v f, m => MapMeaning input.clock input.signerRank (Admitted domains input.acts)
      ⟨.withField (.verb v) f, .address, .address, f, true⟩ m
  | .lwwPerSigner v f c, m => MapMeaning input.clock input.signerRank (Admitted domains input.acts)
      ⟨.own v, .signer, .hlc c, f, false⟩ m
  | .lwwMap v k f c d, m => MapMeaning input.clock input.signerRank (Admitted domains input.acts)
      ⟨.current v (some k) d, .key k, .hlc c, f, false⟩ m
  | _, _ => False

/-- Independent surface semantics; named references use earlier surface declarations. -/
def SurfaceMeaning (input : Input) (domains : List Domain) (earlier : List (String × Rule))
    (rule : Rule) (output : Observation) : Prop :=
  match rule with
  | .last v f => Meaning input domains (.scalar (.verb v) .address f) output
  | .latestPerSigner .. | .latestPerKey .. | .registerPerKey .. | .events ..
  | .lwwPerSigner .. | .lwwMap .. => match output with
      | .map m => SurfaceMapMeaning input domains rule m
      | _ => False
  | .existsRule v => Meaning input domains (.existsRule (.verb v)) output
  | .count v => Meaning input domains (.count (.verb v)) output
  | .progress v => Meaning input domains (.progress v) output
  | .setUnion v f => Meaning input domains (.distinct (.verb v) f) output
  | .values v f => Meaning input domains (.distinct (.current v none none) f) output
  | .valuesPerKey v k f d => Meaning input domains (.valuesBy (.current v (some k) d) k f) output
  | .observedSet add remove f => Meaning input domains (.distinct (.current add (some f) (some remove)) f) output
  | .counter inc dec f => Meaning input domains (.counter (.verb inc) (.verb dec) f) output
  | .lwwRegister v f c => Meaning input domains (.scalar (.verb v) (.hlc c) f) output
  | .boundedCounter name => Meaning input domains (.bounded name) output
  | .histogram reference => match output with
      | .histogram keys counts => ∃ source, earlier.lookup reference = some source ∧ HistogramSource source ∧
          ∃ m, SurfaceMapMeaning input domains source m ∧ HistogramMeaning m counts keys
      | _ => False
  | .sum reference => match output with
      | .integer value => ∃ source, earlier.lookup reference = some source ∧ MapSource source ∧
          ∃ m, SurfaceMapMeaning input domains source m ∧ SumMeaning m value
      | _ => False

/-- Executable lowering of primitive map declarations. -/
def mapPlanOf : Rule → Option MapPlan
  | .latestPerSigner v f => some ⟨.own v, .signer, .address, f, false⟩
  | .latestPerKey v k f => some ⟨.verb v, .key k, .address, f, false⟩
  | .registerPerKey v k f d => some ⟨.current v (some k) d, .key k, .address, f, false⟩
  | .events v f => some ⟨.withField (.verb v) f, .address, .address, f, true⟩
  | .lwwPerSigner v f c => some ⟨.own v, .signer, .hlc c, f, false⟩
  | .lwwMap v k f c d => some ⟨.current v (some k) d, .key k, .hlc c, f, false⟩
  | _ => none

/-- Executable compatibility check, separate from the inductive specification. -/
def histogramAllowed : Rule → Bool
  | .latestPerSigner .. | .latestPerKey .. | .registerPerKey .. | .lwwPerSigner .. | .lwwMap .. => true
  | _ => false

/-- Every independently specified map source lowers; no reject-all loophole. -/
theorem map_plan_complete {rule : Rule} (source : MapSource rule) :
    ∃ plan, mapPlanOf rule = some plan := by cases source <;> exact ⟨_, rfl⟩

theorem histogram_source_map {rule : Rule} (source : HistogramSource rule) : MapSource rule := by
  cases source <;> constructor

theorem histogram_allowed_correct (rule : Rule) : histogramAllowed rule = true ↔ HistogramSource rule := by
  constructor
  · intro h
    cases rule <;> simp only [histogramAllowed, Bool.false_eq_true] at h
    all_goals first | contradiction | constructor
  · intro h; cases h <;> rfl

@[simp] theorem mapPlan_histogram (reference : String) : mapPlanOf (.histogram reference) = none := rfl
@[simp] theorem mapPlan_sum (reference : String) : mapPlanOf (.sum reference) = none := rfl

/-- Map translation preserves the independently specified source and payload graph. -/
theorem map_plan_correct {rule : Rule} {plan : MapPlan} (compiled : mapPlanOf rule = some plan)
    (input : Input) (domains : List Domain) (m : FiniteMap) :
    MapMeaning input.clock input.signerRank (Admitted domains input.acts) plan m ↔
      SurfaceMapMeaning input domains rule m := by
  cases rule <;> simp only [mapPlanOf, Option.some.injEq, reduceCtorEq] at compiled
  all_goals subst plan; rfl

theorem map_plan_source {rule : Rule} {plan : MapPlan} (compiled : mapPlanOf rule = some plan) : MapSource rule := by
  cases rule <;> simp only [mapPlanOf, Option.some.injEq, reduceCtorEq] at compiled
  all_goals constructor

/-- Independently defined backward-reference well-formedness. -/
def WellFormedRule (earlier : List (String × Rule)) : Rule → Prop
  | .histogram reference => ∃ source, earlier.lookup reference = some source ∧ HistogramSource source
  | .sum reference => ∃ source, earlier.lookup reference = some source ∧ MapSource source
  | _ => True

/-- Executable rule elaboration resolves references before interpretation. -/
def compileRule (earlier : List (String × Rule)) (rule : Rule) : Option Expr :=
  match mapPlanOf rule with
  | some plan => some (.mapped plan)
  | none => match rule with
      | .last v f => some (.scalar (.verb v) .address f)
      | .existsRule v => some (.existsRule (.verb v))
      | .count v => some (.count (.verb v))
      | .progress v => some (.progress v)
      | .setUnion v f => some (.distinct (.verb v) f)
      | .values v f => some (.distinct (.current v none none) f)
      | .valuesPerKey v k f d => some (.valuesBy (.current v (some k) d) k f)
      | .observedSet add remove f => some (.distinct (.current add (some f) (some remove)) f)
      | .counter inc dec f => some (.counter (.verb inc) (.verb dec) f)
      | .lwwRegister v f c => some (.scalar (.verb v) (.hlc c) f)
      | .boundedCounter name => some (.bounded name)
      | .histogram reference => do
          let source ← earlier.lookup reference
          if histogramAllowed source then
            let plan ← mapPlanOf source
            some (.histogram plan)
          else none
      | .sum reference => do
          let source ← earlier.lookup reference
          let plan ← mapPlanOf source
          some (.sum plan)
      | _ => none

/-- Every supported well-formed rule is accepted, independently of its output. -/
theorem compile_rule_complete (earlier : List (String × Rule)) (rule : Rule)
    (wf : WellFormedRule earlier rule) : ∃ expression, compileRule earlier rule = some expression := by
  cases rule with
  | histogram reference =>
      obtain ⟨source, lookup, allowed⟩ := wf
      obtain ⟨plan, compiled⟩ := map_plan_complete (histogram_source_map allowed)
      exact ⟨.histogram plan, by simp [compileRule, mapPlan_histogram, lookup, (histogram_allowed_correct source).mpr allowed, compiled]⟩
  | sum reference =>
      obtain ⟨source, lookup, sourceMap⟩ := wf
      obtain ⟨plan, compiled⟩ := map_plan_complete sourceMap
      exact ⟨.sum plan, by simp [compileRule, mapPlan_sum, lookup, compiled]⟩
  | _ => exact ⟨_, rfl⟩

/-- Successful elaboration preserves independent surface meaning. -/
theorem compile_rule_correct {earlier : List (String × Rule)} {rule : Rule} {expression : Expr}
    (compiled : compileRule earlier rule = some expression) (input : Input) (domains : List Domain)
    (output : Observation) (good : Meaning input domains expression output) :
    SurfaceMeaning input domains earlier rule output := by
  cases rule with
  | histogram reference =>
      cases lookup : earlier.lookup reference with
      | none => simp [compileRule, mapPlan_histogram, lookup] at compiled
      | some source =>
          by_cases allowed : histogramAllowed source = true
          · cases planEq : mapPlanOf source with
            | none => simp [compileRule, mapPlan_histogram, lookup, allowed, planEq] at compiled
            | some plan =>
                have eq : expression = .histogram plan := by simpa [compileRule, mapPlan_histogram, lookup, allowed, planEq] using compiled.symm
                subst expression
                cases output <;> simp only [Meaning] at good
                all_goals try contradiction
                next keys counts =>
                  obtain ⟨m, map, histogram⟩ := good
                  exact ⟨source, lookup, (histogram_allowed_correct source).mp allowed,
                    m, (map_plan_correct planEq _ _ _).mp map, histogram⟩
          · simp [compileRule, mapPlan_histogram, lookup, allowed] at compiled
  | sum reference =>
      cases lookup : earlier.lookup reference with
      | none => simp [compileRule, mapPlan_sum, lookup] at compiled
      | some source =>
          cases planEq : mapPlanOf source with
          | none => simp [compileRule, mapPlan_sum, lookup, planEq] at compiled
          | some plan =>
              have eq : expression = .sum plan := by simpa [compileRule, mapPlan_sum, lookup, planEq] using compiled.symm
              subst expression
              cases output <;> simp only [Meaning] at good
              all_goals try contradiction
              next value =>
                obtain ⟨m, map, total⟩ := good
                exact ⟨source, lookup, map_plan_source planEq, m,
                  (map_plan_correct planEq _ _ _).mp map, total⟩
  | _ =>
      simp only [compileRule, mapPlanOf, Option.some.injEq] at compiled
      subst expression
      cases output <;> simp only [SurfaceMeaning, SurfaceMapMeaning, Meaning] at good ⊢ <;> exact good

/-- A domain names an opener-only list initializer. -/
structure DomainDecl where
  /-- Filtered verb. -/
  verb : String
  /-- Filtered data key. -/
  key : String
  /-- State field containing the opener's list. -/
  source : String

/-- A complete clause preserves field order and independent domain declarations. -/
structure Clause where
  /-- Named state fields, with unique names. -/
  fields : List (String × Rule)
  /-- Domain declarations, possibly combined by intersection. -/
  domains : List DomainDecl

/-- Independent domain-source resolution; not a call to the elaborator. -/
def DomainMeaning (input : Input) (fields : List (String × Rule)) (decl : DomainDecl)
    (resolved : Domain) : Prop :=
  ∃ field, fields.lookup decl.source = some (.last input.opener field) ∧
    resolved = ⟨decl.verb, decl.key, input.opener, field⟩

/-- Independent admissibility of domain references. -/
def WellFormedDomain (input : Input) (fields : List (String × Rule)) (decl : DomainDecl) : Prop :=
  ∃ field, fields.lookup decl.source = some (.last input.opener field)

/-- Independent rule-list admissibility; references can only use preceding declarations. -/
inductive WellFormedFields : List (String × Rule) → List (String × Rule) → Prop where
  | nil (earlier) : WellFormedFields earlier []
  | cons (earlier) (name rule) (rest)
      (head : WellFormedRule earlier rule)
      (tail : WellFormedFields (earlier ++ [(name, rule)]) rest) :
      WellFormedFields earlier ((name, rule) :: rest)

/-- Unique names match the standing R7 contract; no shadowing semantics is invented. -/
def WellFormedClause (input : Input) (clause : Clause) : Prop :=
  (clause.fields.map Prod.fst).Nodup ∧ WellFormedFields [] clause.fields ∧
    ∀ decl ∈ clause.domains, WellFormedDomain input clause.fields decl

/-- Concrete domain elaboration consults the entire raw declaration list. -/
def compileDomain (input : Input) (fields : List (String × Rule)) (decl : DomainDecl) : Option Domain :=
  match fields.lookup decl.source with
  | some (.last opener field) => if opener == input.opener then
      some ⟨decl.verb, decl.key, opener, field⟩ else none
  | _ => none

/-- Concrete domain-list elaboration. -/
def compileDomains (input : Input) (fields : List (String × Rule)) : List DomainDecl → Option (List Domain)
  | [] => some []
  | d :: rest => do
      let resolved ← compileDomain input fields d
      let tail ← compileDomains input fields rest
      some (resolved :: tail)

/-- Concrete ordered field elaboration. -/
def compileFields (earlier : List (String × Rule)) : List (String × Rule) → Option (List (String × Expr))
  | [] => some []
  | (name, rule) :: rest => do
      let expression ← compileRule earlier rule
      let tail ← compileFields (earlier ++ [(name, rule)]) rest
      some ((name, expression) :: tail)

/-- Successfully elaborated domains and expressions, without runtime effects. -/
structure Compiled where
  /-- Resolved opener-source domains. -/
  domains : List Domain
  /-- Named expressions in clause order. -/
  fields : List (String × Expr)

/-- Elaboration fails closed on duplicates or unsupported references. -/
def compileClause (input : Input) (clause : Clause) : Option Compiled := do
  if (clause.fields.map Prod.fst).Nodup then
    let domains ← compileDomains input clause.fields clause.domains
    let fields ← compileFields [] clause.fields
    some ⟨domains, fields⟩
  else none

/-- Whole-clause evaluation after references have been resolved. -/
def evaluateFields (input : Input) (domains : List Domain) (fields : List (String × Expr)) : List (String × Observation) :=
  fields.map (fun (name, expression) => (name, evaluate input domains expression))

/-- Independent ordered field semantics, with earlier *surface* declarations. -/
inductive FieldsMeaning (input : Input) (domains : List Domain) :
    List (String × Rule) → List (String × Rule) → List (String × Observation) → Prop where
  | nil (earlier) : FieldsMeaning input domains earlier [] []
  | cons (earlier) (name rule) (rest) (output) (outputs)
      (head : SurfaceMeaning input domains earlier rule output)
      (tail : FieldsMeaning input domains (earlier ++ [(name, rule)]) rest outputs) :
      FieldsMeaning input domains earlier ((name, rule) :: rest) ((name, output) :: outputs)

/-- Independent whole-clause denotation, including exact domain-source resolution. -/
def ClauseMeaning (input : Input) (clause : Clause) (outputs : List (String × Observation)) : Prop :=
  ∃ domains, List.Forall₂ (DomainMeaning input clause.fields) clause.domains domains ∧
    FieldsMeaning input domains [] clause.fields outputs

/-- Every independently admissible domain source elaborates. -/
theorem compile_domain_complete (input : Input) (fields : List (String × Rule))
    (decl : DomainDecl) (wf : WellFormedDomain input fields decl) :
    ∃ resolved, compileDomain input fields decl = some resolved := by
  obtain ⟨field, lookup⟩ := wf
  exact ⟨⟨decl.verb, decl.key, input.opener, field⟩, by simp [compileDomain, lookup]⟩

/-- Domain elaboration preserves its independently specified source. -/
theorem compile_domain_correct {input : Input} {fields : List (String × Rule)}
    {decl : DomainDecl} {resolved : Domain}
    (compiled : compileDomain input fields decl = some resolved) :
    DomainMeaning input fields decl resolved := by
  unfold compileDomain at compiled
  split at compiled <;> try contradiction
  next opener field lookup =>
    split at compiled <;> try contradiction
    next equal =>
      have eq : opener = input.opener := by simpa using equal
      subst opener
      exact ⟨field, lookup, by simpa using compiled.symm⟩

/-- Every independently admissible domain list elaborates. -/
theorem compile_domains_complete (input : Input) (fields : List (String × Rule))
    (decls : List DomainDecl) (wf : ∀ d ∈ decls, WellFormedDomain input fields d) :
    ∃ domains, compileDomains input fields decls = some domains := by
  induction decls with
  | nil => exact ⟨[], rfl⟩
  | cons d rest ih =>
      obtain ⟨domain, head⟩ := compile_domain_complete input fields d (wf d (by simp))
      obtain ⟨domains, tail⟩ := ih (fun x hx => wf x (by simp [hx]))
      exact ⟨domain :: domains, by simp [compileDomains, head, tail]⟩

/-- Domain lists retain order and exact source relations. -/
theorem compile_domains_correct {input : Input} {fields : List (String × Rule)}
    {decls : List DomainDecl} {domains : List Domain}
    (compiled : compileDomains input fields decls = some domains) :
    List.Forall₂ (DomainMeaning input fields) decls domains := by
  induction decls generalizing domains with
  | nil => simp [compileDomains] at compiled; subst domains; exact .nil
  | cons d rest ih =>
      cases head : compileDomain input fields d with
      | none => simp [compileDomains, head] at compiled
      | some domain =>
          cases tail : compileDomains input fields rest with
          | none => simp [compileDomains, head, tail] at compiled
          | some more =>
              simp [compileDomains, head, tail] at compiled
              subst domains
              exact .cons (compile_domain_correct head) (ih tail)

/-- Independent rule-list admissibility guarantees elaboration succeeds. -/
theorem compile_fields_complete {earlier fields : List (String × Rule)}
    (wf : WellFormedFields earlier fields) :
    ∃ expressions, compileFields earlier fields = some expressions := by
  induction wf with
  | nil => exact ⟨[], rfl⟩
  | cons earlier name rule rest head _ ih =>
      obtain ⟨expression, compiled⟩ := compile_rule_complete earlier rule head
      obtain ⟨expressions, tail⟩ := ih
      exact ⟨(name, expression) :: expressions, by simp [compileFields, compiled, tail]⟩

/-- Every evaluated field satisfies surface meaning, in original clause order. -/
theorem evaluate_fields_correct (input : Input) (domains : List Domain)
    (unique : State.NodupAddr input.acts) {earlier fields : List (String × Rule)}
    {expressions : List (String × Expr)}
    (compiled : compileFields earlier fields = some expressions) :
    FieldsMeaning input domains earlier fields (evaluateFields input domains expressions) := by
  induction fields generalizing earlier expressions with
  | nil =>
      simp [compileFields] at compiled
      subst expressions
      exact .nil _
  | cons pair rest ih =>
      obtain ⟨name, rule⟩ := pair
      cases head : compileRule earlier rule with
      | none => simp [compileFields, head] at compiled
      | some expression =>
          cases tail : compileFields (earlier ++ [(name, rule)]) rest with
          | none => simp [compileFields, head, tail] at compiled
          | some more =>
              simp [compileFields, head, tail] at compiled
              subst expressions
              exact .cons earlier name rule rest _ _
                (compile_rule_correct head input domains _ (evaluate_correct input unique domains expression))
                (ih tail)

/-- No well-formed supported clause can be rejected by the elaborator. -/
theorem compile_clause_complete (input : Input) (clause : Clause)
    (wf : WellFormedClause input clause) :
    ∃ compiled, compileClause input clause = some compiled := by
  obtain ⟨names, fields, domains⟩ := wf
  obtain ⟨resolved, domainEq⟩ := compile_domains_complete input clause.fields clause.domains domains
  obtain ⟨expressions, fieldEq⟩ := compile_fields_complete fields
  exact ⟨⟨resolved, expressions⟩, by simp [compileClause, names, domainEq, fieldEq]⟩

/-- Whole-clause correctness: successful elaboration and evaluation preserve independent meaning. -/
theorem whole_kernel_correct (input : Input) (clause : Clause) (compiled : Compiled)
    (unique : State.NodupAddr input.acts)
    (accepted : compileClause input clause = some compiled) :
    ClauseMeaning input clause (evaluateFields input compiled.domains compiled.fields) := by
  unfold compileClause at accepted
  split at accepted <;> try contradiction
  cases domainEq : compileDomains input clause.fields clause.domains with
  | none => simp [domainEq] at accepted
  | some domains =>
      cases fieldEq : compileFields [] clause.fields with
      | none => simp [domainEq, fieldEq] at accepted
      | some fields =>
          simp [domainEq, fieldEq] at accepted
          subst compiled
          exact ⟨domains, compile_domains_correct domainEq,
            evaluate_fields_correct input domains unique fieldEq⟩

/-- Total correctness for every independently well-formed clause over a unique-address store. -/
theorem well_formed_kernel_correct (input : Input) (clause : Clause)
    (unique : State.NodupAddr input.acts) (wf : WellFormedClause input clause) :
    ∃ compiled, compileClause input clause = some compiled ∧
      ClauseMeaning input clause (evaluateFields input compiled.domains compiled.fields) := by
  obtain ⟨compiled, accepted⟩ := compile_clause_complete input clause wf
  exact ⟨compiled, accepted, whole_kernel_correct input clause compiled unique accepted⟩

end CBCL.StateKernelClause
