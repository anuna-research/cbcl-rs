import LeanCbcl.StateOutputThresholdAgreement

/-! Fresh authored compilation changes captured source paths and freeze metadata,
but retains the exact named query code selected by the installed declarations. -/
set_option autoImplicit false
namespace CBCL.StateOutputQueryIdentity
open State StateOutputCompiler StateInstalledLowering StateAuthoredBindings

/-- Query identity retains field names, threshold source names and actual code. -/
def queryIdentity {V : Type} : Output V → String × Option (String × Query V)
  | .field name _ => (name,none)
  | .threshold name source query _ => (name,some (source,query))

/-- Successful compilation of the same declaration retains identical query code,
regardless of the independently compiled source plans. -/
theorem compile_one_identity {V : Type} (leftPlans rightPlans : StateInstalledCompiler.Plans V)
    (definitions : Definitions V) (declaration : Declaration V) (left right : Output V)
    (leftCompiled : compileOne leftPlans definitions declaration = some left)
    (rightCompiled : compileOne rightPlans definitions declaration = some right) :
    queryIdentity left = queryIdentity right := by
  cases declaration with
  | field name definition =>
    cases l : leftPlans.lookup name <;> cases r : rightPlans.lookup name <;>
      simp_all [compileOne,queryIdentity]
    rw [← leftCompiled,← rightCompiled]
  | threshold name source elements =>
    cases l : leftPlans.lookup source <;> cases r : rightPlans.lookup source <;>
      simp only [compileOne,l,r] at leftCompiled rightCompiled
    all_goals first | contradiction | skip
    cases d : definitions.lookup source with
    | none => simp [d] at leftCompiled
    | some definition =>
      cases q : compileQuery elements definition with
      | none => simp [d,q] at leftCompiled
      | some query =>
        simp [d,q] at leftCompiled rightCompiled
        subst left
        subst right
        rfl

/-- Ordered recompilation retains the entire query-identity vector. -/
theorem compile_declarations_identity {V : Type} (declarations : List (Declaration V))
    (definitions : Definitions V) (leftPlans rightPlans : StateInstalledCompiler.Plans V)
    (left right : List (Output V))
    (leftCompiled : compileDeclarations leftPlans definitions declarations = some left)
    (rightCompiled : compileDeclarations rightPlans definitions declarations = some right) :
    left.map queryIdentity = right.map queryIdentity := by
  induction declarations generalizing definitions left right with
  | nil =>
    have l : [] = left := Option.some.inj leftCompiled
    have r : [] = right := Option.some.inj rightCompiled
    simp [← l,← r]
  | cons declaration rest ih =>
    cases l : compileOne leftPlans definitions declaration with
    | none => simp [compileDeclarations,l] at leftCompiled
    | some first =>
      cases r : compileOne rightPlans definitions declaration with
      | none => simp [compileDeclarations,r] at rightCompiled
      | some second =>
        cases lt : compileDeclarations leftPlans (extend definitions declaration) rest with
        | none => simp [compileDeclarations,l,lt] at leftCompiled
        | some more =>
          cases rt : compileDeclarations rightPlans (extend definitions declaration) rest with
          | none => simp [compileDeclarations,r,rt] at rightCompiled
          | some restRight =>
            have leftEq : first::more = left := by simpa [compileDeclarations,l,lt] using leftCompiled
            have rightEq : second::restRight = right := by simpa [compileDeclarations,r,rt] using rightCompiled
            rw [← leftEq,← rightEq,List.map_cons,List.map_cons,
              compile_one_identity leftPlans rightPlans definitions declaration first second l r,
              ih (extend definitions declaration) more restRight lt rt]

/-- Two actual authored compilations retain the same named query code without
requiring accepted-set equality, growth, or source-path pairing as premises. -/
theorem authored_query_identity (environment : Environment) (entries : List Entry)
    (A B : List Act) (left right : CompiledObservation)
    (leftCompiled : compileAuthored environment entries A = some left)
    (rightCompiled : compileAuthored environment entries B = some right) :
    left.program.outputs.map queryIdentity = right.program.outputs.map queryIdentity := by
  obtain ⟨prepared,first,firstCode,installed,_,firstInstructions,_,firstProgram⟩ :=
    StateAuthoredOutputReplay.compile_authored_parts environment entries A left leftCompiled
  obtain ⟨other,second,secondCode,otherInstalled,_,secondInstructions,_,secondProgram⟩ :=
    StateAuthoredOutputReplay.compile_authored_parts environment entries B right rightCompiled
  have same : prepared = other := Option.some.inj (installed.symm.trans otherInstalled)
  subst other
  simpa [firstProgram,secondProgram] using
    compile_declarations_identity prepared.declarations [] first second firstCode secondCode firstInstructions secondInstructions

/-- Equal threshold identities retain the exact query, rather than only its
source name or projected successful payload. -/
theorem threshold_query_eq {V : Type} (leftName rightName leftSource rightSource : String)
    (leftQuery rightQuery : Query V) (leftPlan rightPlan : StateObservationPlan.Plan V)
    (same : queryIdentity (.threshold leftName leftSource leftQuery leftPlan) =
      queryIdentity (.threshold rightName rightSource rightQuery rightPlan)) : leftQuery = rightQuery := by
  exact (Prod.mk.inj (Option.some.inj (Prod.mk.inj same).2)).2

/-- Paired actual threshold instructions with a singleton policy return the same
successful result, even when freshly captured source plans and freezer cuts differ. -/
theorem paired_singleton_success_agreement {V : Type}
    (leftName rightName leftSource rightSource : String) (leftQuery rightQuery : Query V)
    (leftPlan rightPlan : StateObservationPlan.Plan V)
    (same : queryIdentity (.threshold leftName leftSource leftQuery leftPlan) =
      queryIdentity (.threshold rightName rightSource rightQuery rightPlan))
    (element leftResult rightResult : V)
    (singleton : StateOutputThresholdAgreement.alternatives leftQuery = some [element])
    (A B : List Act) (leftFreezes rightFreezes : List (String × StateObservation.FreezeSpec))
    (leftReached : Output.observe A leftFreezes (.threshold leftName leftSource leftQuery leftPlan) =
      (leftName,.data (.reached leftResult)))
    (rightReached : Output.observe B rightFreezes (.threshold rightName rightSource rightQuery rightPlan) =
      (rightName,.data (.reached rightResult))) : leftResult = rightResult := by
  have queries := threshold_query_eq leftName rightName leftSource rightSource leftQuery rightQuery leftPlan rightPlan same
  subst rightQuery
  have left := StateOutputThresholdAgreement.reached_member leftQuery [element]
    (StateThresholdDispatch.referenceScope A leftFreezes leftSource) (sourceValue A leftPlan) leftResult
    singleton (Prod.mk.inj leftReached).2
  have right := StateOutputThresholdAgreement.reached_member leftQuery [element]
    (StateThresholdDispatch.referenceScope B rightFreezes rightSource) (sourceValue B rightPlan) rightResult
    singleton (Prod.mk.inj rightReached).2
  have first : leftResult = element := by simpa using left
  have second : rightResult = element := by simpa using right
  exact first.trans second.symm

end CBCL.StateOutputQueryIdentity
