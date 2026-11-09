import LeanCbcl.StateDataLocalWorld

/-! Complete authored frozen-value agreement across fresh output compilations. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredFrozenAgreement
open State StateLift StateLVar StateObservation StateObservationPlan StateOutputCompiler
open StateInstalledCompiler StateInstalledLowering StateAuthoredBindings StateFrozenPayload

/-- Exact output correspondence retains names, queries and complete source plans. -/
inductive OutputPair {V : Type} : Output V → Output V → Prop where
  | field (name : String) {left right : Plan V} : Related left right →
      OutputPair (.field name left) (.field name right)
  | threshold (name source : String) (query : Query V) {left right : Plan V} : Related left right →
      OutputPair (.threshold name source query left) (.threshold name source query right)

/-- Optional output compilation preserves rejection and actual instruction pairing. -/
inductive Match {V : Type} : Option (Output V) → Option (Output V) → Prop where
  | none : Match none none
  | some {left right : Output V} : OutputPair left right → Match (some left) (some right)

/-- Related ordered source plans give related actual dictionary lookups. -/
theorem related_lookup {V : Type} (left right : Plans V)
    (related : List.Forall₂ (fun a b => a.1 = b.1 ∧ Related a.2 b.2) left right) :
    StateFrozenCompilation.Environments left right := by
  induction related with
  | nil => intro name; exact .none
  | @cons a b left right head tail ih =>
    intro name
    obtain ⟨leftName,leftPlan⟩ := a
    obtain ⟨rightName,rightPlan⟩ := b
    have names : leftName = rightName := head.1
    subst rightName
    by_cases same : name = leftName
    · subst name
      simpa [List.lookup] using StateFrozenCompilation.Match.some head.2
    · simpa [List.lookup,beq_eq_false_iff_ne.mpr same] using ih name

/-- One output retains the complete related source selected by name. -/
theorem compile_one_related {V : Type} (left right : Plans V) (definitions : Definitions V)
    (declaration : Declaration V) (related : StateFrozenCompilation.Environments left right) :
    Match (compileOne left definitions declaration) (compileOne right definitions declaration) := by
  cases declaration with
  | field name definition =>
    have paired := related name
    cases la : left.lookup name <;> cases rb : right.lookup name <;> simp only [la,rb] at paired
    all_goals cases paired
    · simp [compileOne,la,rb]; exact .none
    · simp [compileOne,la,rb]; exact .some (.field name (by assumption))
  | threshold name source elements =>
    have paired := related source
    cases la : left.lookup source <;> cases rb : right.lookup source <;> simp only [la,rb] at paired
    all_goals cases paired
    · simp [compileOne,la,rb]; exact .none
    · cases found : definitions.lookup source with
      | none => simp [compileOne,la,rb,found]; exact .none
      | some definition =>
        cases query : compileQuery elements definition with
        | none => simp [compileOne,la,rb,found,query]; exact .none
        | some strategy =>
          simp [compileOne,la,rb,found,query]
          exact .some (.threshold name source strategy (by assumption))

/-- Ordered output compilation preserves source pairing while extending the
same installed metadata dictionary. -/
theorem compile_declarations_related {V : Type} (declarations : List (Declaration V))
    (definitions : Definitions V) (left right : Plans V) (first second : List (Output V))
    (related : StateFrozenCompilation.Environments left right)
    (firstCompiled : compileDeclarations left definitions declarations = some first)
    (secondCompiled : compileDeclarations right definitions declarations = some second) :
    List.Forall₂ OutputPair first second := by
  induction declarations generalizing definitions first second with
  | nil =>
    have a : [] = first := Option.some.inj firstCompiled
    have b : [] = second := Option.some.inj secondCompiled
    simp [← a,← b]
  | cons declaration rest ih =>
    have head := compile_one_related left right definitions declaration related
    generalize a : compileOne left definitions declaration = firstHead at head
    generalize b : compileOne right definitions declaration = secondHead at head
    cases head with
    | none => simp [compileDeclarations,a] at firstCompiled
    | @some firstOutput secondOutput paired =>
      cases ft : compileDeclarations left (extend definitions declaration) rest with
      | none => simp [compileDeclarations,a,ft] at firstCompiled
      | some more =>
        cases st : compileDeclarations right (extend definitions declaration) rest with
        | none => simp [compileDeclarations,b,st] at secondCompiled
        | some other =>
          have firstEq : firstOutput::more = first := by simpa [compileDeclarations,a,ft] using firstCompiled
          have secondEq : secondOutput::other = second := by simpa [compileDeclarations,b,st] using secondCompiled
          rw [← firstEq,← secondEq]
          exact .cons paired (ih (extend definitions declaration) more other ft st)

/-- Actual fresh authored compilations derive their complete output pairing. -/
theorem authored_outputs_related (environment : Environment) (entries : List Entry)
    (A B : List Act) (left right : CompiledObservation)
    (leftCompiled : compileAuthored environment entries A = some left)
    (rightCompiled : compileAuthored environment entries B = some right) :
    List.Forall₂ OutputPair left.program.outputs right.program.outputs := by
  obtain ⟨prepared,first,firstCode,installed,firstCompiled,firstInstructions,_,firstProgram⟩ :=
    StateAuthoredOutputReplay.compile_authored_parts environment entries A left leftCompiled
  obtain ⟨other,second,secondCode,otherInstalled,secondCompiled,secondInstructions,_,secondProgram⟩ :=
    StateAuthoredOutputReplay.compile_authored_parts environment entries B right rightCompiled
  have same : prepared = other := Option.some.inj (installed.symm.trans otherInstalled)
  subst other
  have sources := StateFrozenCompilation.authored_plans_related environment entries prepared installed A B first second firstCompiled secondCompiled
  have outputs := compile_declarations_related prepared.declarations [] first second firstCode secondCode
    (related_lookup first second sources) firstInstructions secondInstructions
  simpa [firstProgram,secondProgram] using outputs

/-- Every actual emitted output has an actual paired receiving output. -/
theorem paired_member {V : Type} {left right : List (Output V)} (paired : List.Forall₂ OutputPair left right)
    (output : Output V) (member : output ∈ left) : ∃ other, other ∈ right ∧ OutputPair output other := by
  induction paired with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst output
      exact ⟨_,by simp,head⟩
    · obtain ⟨other,inside,related⟩ := ih later
      exact ⟨other,List.mem_cons_of_mem _ inside,related⟩

/-- Authored query code reports pending, reached or fault; it cannot fabricate
frozen source status. -/
theorem plain_query_not_frozen {V : Type} (query : Query V) (plain : StateOutputWitnessReplay.PlainQuery query)
    (history : List Act) (source : StateReaderValues.Result V) (address : Nat) (value : V) (excluded : FinSet Act) :
    query.run history source ≠ .data (.frozen address value excluded) := by
  intro bad
  cases query with
  | closure alternatives test =>
    cases current : StateReaderValues.unfrozen source with
    | fault evidence => simp [Query.run,StateRuleRefinement.nativeClosureThreshold,current] at bad
    | data datum =>
      cases payload : datum.payload with
      | none => simp [Query.run,StateRuleRefinement.nativeClosureThreshold,current,payload] at bad
      | some raw =>
        cases found : alternatives.find? (fun q => test q raw) <;>
          simp [Query.run,StateRuleRefinement.nativeClosureThreshold,current,payload,found] at bad
  | raw alternatives test state =>
    cases source with
    | fault evidence => simp [Query.run,nativeRawThreshold] at bad
    | data datum =>
      cases found : alternatives.find? (fun q => test q (state (rawHistory history))) <;>
        simp [Query.run,nativeRawThreshold,found] at bad
  | finite spec embed => exact False.elim plain

/-- Successful emitted source status recovers common-world clarity and data. -/
theorem source_frozen_global {V : Type} (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A) (source : Plan V)
    (address : Nat) (value : V) (excluded : FinSet Act)
    (frozen : sourceValue A source = .data (.frozen address value excluded)) :
    errors world (path source) (StateScopePool.normalize A) = none ∧
      data world source (StateScopePool.normalize A) = .frozen address value excluded := by
  rw [StateDataLocalWorld.source_value_global world A valid closed source] at frozen
  cases current : errors world (path source) (StateScopePool.normalize A) with
  | some evidence => simp [observe,current] at frozen
  | none => exact ⟨rfl,by simpa [observe,current] using frozen⟩

/-- Complete actual authored outputs frozen at the same accepted act agree on
underlying values, allowing independently enlarged exclusion metadata. -/
theorem authored_frozen_agreement (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (prepared : Prepared) (installed : prepareStatic environment entries = some prepared)
    (A B : List Act) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (left right : CompiledObservation)
    (leftCompiled : compileAuthored environment entries A = some left)
    (rightCompiled : compileAuthored environment entries B = some right)
    (name : String) (freezer : Act) (presentA : freezer ∈ A) (presentB : freezer ∈ B)
    (leftValue rightValue : StateInstalledLegacy.Value) (leftExcluded rightExcluded : FinSet Act)
    (leftFrozen : (name,.data (.frozen freezer.addr leftValue leftExcluded)) ∈ left.observe)
    (rightFrozen : (name,.data (.frozen freezer.addr rightValue rightExcluded)) ∈ right.observe) :
    leftValue = rightValue := by
  have historyA : left.history = A := by
    obtain ⟨_,_,_,_,_,_,history,_⟩ := StateAuthoredOutputReplay.compile_authored_parts environment entries A left leftCompiled
    exact history
  have historyB : right.history = B := by
    obtain ⟨_,_,_,_,_,_,history,_⟩ := StateAuthoredOutputReplay.compile_authored_parts environment entries B right rightCompiled
    exact history
  obtain ⟨output,member,observed⟩ := List.mem_map.mp leftFrozen
  obtain ⟨other,otherMember,paired⟩ := paired_member (authored_outputs_related environment entries A B left right leftCompiled rightCompiled) output member
  have firstPlain := StateAuthoredOutputReplay.compile_authored_plain environment entries A left leftCompiled output member
  cases paired with
  | @threshold outputName source query first second related =>
    have frozenQuery := (Prod.mk.inj observed).2
    exact False.elim (plain_query_not_frozen query firstPlain _ _ _ _ _ frozenQuery)
  | @field outputName first second related =>
    have names : outputName = name := (Prod.mk.inj observed).1
    subst outputName
    have leftValueEq : sourceValue A first = .data (.frozen freezer.addr leftValue leftExcluded) := by
      simpa [Output.observe,historyA] using (Prod.mk.inj observed).2
    have otherObserved : (name,sourceValue B second) ∈ right.observe := by
      rw [CompiledObservation.observe,historyB,Program.observe]
      exact List.mem_map.mpr ⟨_,otherMember,rfl⟩
    have unique := StateAuthoredFinitePreservation.authored_output_names_unique environment entries prepared installed B right rightCompiled
    have received := StateReaderReachability.lookup_original right.observe unique name _ rightFrozen
    have selected := StateReaderReachability.lookup_original right.observe unique name _ otherObserved
    have rightValueEq : sourceValue B second = .data (.frozen freezer.addr rightValue rightExcluded) :=
      Option.some.inj (selected.symm.trans received)
    obtain ⟨leftClear,leftData⟩ := source_frozen_global world A validA closedA first _ _ _ leftValueEq
    obtain ⟨rightClear,rightData⟩ := source_frozen_global world B validB closedB second _ _ _ rightValueEq
    have normA := StateScopePool.normalize_setEq A
    have normB := StateScopePool.normalize_setEq B
    have closedNormA : CausallyClosed world (StateScopePool.normalize A) := by
      intro child member parent valid edge
      exact (normA parent).mpr (closedA child ((normA child).mp member) parent valid edge)
    have closedNormB : CausallyClosed world (StateScopePool.normalize B) := by
      intro child member parent valid edge
      exact (normB parent).mpr (closedB child ((normB child).mp member) parent valid edge)
    exact StateFrozenSuccess.related_frozen_agreement world related _ _ freezer
      (StateScopePool.normalize_unique A consistentA) (StateScopePool.normalize_unique B consistentB)
      closedNormA closedNormB ((normA freezer).mpr presentA) ((normB freezer).mpr presentB)
      leftClear rightClear leftValue rightValue leftExcluded rightExcluded leftData rightData

end CBCL.StateAuthoredFrozenAgreement
