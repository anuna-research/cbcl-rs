import LeanCbcl.StateAuthoredOutputReplay
import LeanCbcl.StateAuthoredConditionOutputs

/-! Successful authored condition compilation derives its closed query inventory
from real earlier definitions. The exact evidence theorem therefore does not
require dialect authors or receiving replicas to assert a classification. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredConditionPlain
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredOutputReplay StateOutputWitnessReplay StateCondition StateConditionCompiler

universe u v

/-- Successful ordered optional traversal retains each result's proved property. -/
theorem mapM_property {A : Type u} {B : Type v} (inputs : List A) (function : A → Option B)
    (property : B → Prop) (outputs : List B)
    (each : ∀ input ∈ inputs, ∀ output, function input = some output → property output)
    (compiled : inputs.mapM function = some outputs) : ∀ output ∈ outputs, property output := by
  induction inputs generalizing outputs with
  | nil =>
    have empty : outputs = [] := by simpa using compiled.symm
    subst outputs
    simp
  | cons first rest ih =>
    cases head : function first with
    | none => simp [List.mapM_cons,head] at compiled
    | some current =>
      cases tail : rest.mapM function with
      | none => simp [List.mapM_cons,head,tail] at compiled
      | some more =>
        have same : current :: more = outputs := by simpa [List.mapM_cons,head,tail] using compiled
        subst outputs
        intro output member
        rcases List.mem_cons.mp member with equal | inside
        · subst output
          exact each first (by simp) current head
        · exact ih more (fun input member => each input (List.mem_cons_of_mem first member)) tail output inside

/-- Condition trees compiled from the proved authored definition inventory add
no independent query top; every fault remains a source dependency fault. -/
theorem compile_plain (maxNodes : Nat) (plans : Plans Value) (definitions : Definitions Value)
    (prior : PlainDefinitions definitions) (condition : Condition Value) (code : Code Value)
    (compiled : StateConditionCompiler.compile maxNodes plans definitions condition = some code) :
    StateConditionFaults.Plain code := by
  let P := fun condition : Condition Value => ∀ code,
    StateConditionCompiler.compile maxNodes plans definitions condition = some code → StateConditionFaults.Plain code
  apply Condition.rec (motive_1 := P) (motive_2 := fun children => ∀ child ∈ children, P child) ?_ ?_ ?_ ?_ condition code compiled
  · intro field element code built
    obtain ⟨source,definition,query,_,defined,queried,rfl⟩ :=
      compile_read_origin maxNodes plans definitions field element code built
    change PlainQuery query
    exact compile_query_plain [element] definition query (prior field definition defined) queried
  · intro children ih code built
    simp only [StateConditionCompiler.compile,Condition.fold_all] at built
    by_cases invalid : maxNodes < (Condition.all children).size ∨ children.length < 2
    · simp [invalid] at built
    simp only [invalid,↓reduceIte] at built
    change ((children.map (StateConditionCompiler.compile maxNodes plans definitions)).mapM id).bind
      (fun values => some (Code.all values)) = some code at built
    cases traversed : (children.map (StateConditionCompiler.compile maxNodes plans definitions)).mapM id with
    | none => simp [traversed] at built
    | some codes =>
      have same : Code.all codes = code := by simpa [traversed] using built
      subst code
      have all : ∀ child ∈ codes, StateConditionFaults.Plain child :=
        mapM_property children (StateConditionCompiler.compile maxNodes plans definitions) StateConditionFaults.Plain codes
          (fun child member output ran => ih child member output ran)
          (by simpa only [List.mapM_map,Function.comp_def] using traversed)
      simp only [StateConditionFaults.Plain,Code.fold_all]
      intro value member
      obtain ⟨child,inside,rfl⟩ := List.mem_map.mp member
      exact all child inside
  · intro child impossible
    simp at impossible
  · intro head tail headProof tailProof child member
    rcases List.mem_cons.mp member with equal | member
    · simpa only [equal] using headProof
    · exact tailProof child member

/-- Interleaving actual condition instructions retains the closed inventory
from original source declarations and their earlier-definition prefix. -/
theorem emit_plain (maxNodes : Nat) (plans : Plans Value) (entries : List Entry)
    (declarations : List (Declaration Value)) (base : List (Output Value)) (earlier : Definitions Value)
    (outputs : List (Output Value)) (prior : PlainDefinitions earlier)
    (declared : ∀ declaration ∈ declarations, PlainDeclaration declaration)
    (basePlain : ∀ output ∈ base, PlainOutput output)
    (compiled : emitAuthored maxNodes plans entries declarations base earlier = some outputs) :
    ∀ output ∈ outputs, PlainOutput output := by
  induction entries generalizing declarations base earlier outputs with
  | nil =>
    cases declarations <;> cases base <;> simp [emitAuthored] at compiled
    subst outputs
    simp
  | cons entry rest ih =>
    cases entry with
    | condition name expression =>
      cases built : StateConditionCompiler.compile maxNodes plans earlier expression with
      | none => simp [emitAuthored,built] at compiled
      | some code =>
        cases tail : emitAuthored maxNodes plans rest declarations base earlier with
        | none => simp [emitAuthored,built,tail] at compiled
        | some more =>
          have same : Output.condition name (.element (.scalar (.bool true))) code :: more = outputs := by
            simpa [emitAuthored,built,tail] using compiled
          subst outputs
          have remaining := ih declarations base earlier more prior declared basePlain tail
          intro output member
          rcases List.mem_cons.mp member with equal | inside
          · subst output
            exact compile_plain maxNodes plans earlier prior expression code built
          · exact remaining output inside
    | field name _ | threshold name _ _ =>
      cases declarations with
      | nil => simp [emitAuthored] at compiled
      | cons declaration later =>
        cases base with
        | nil => simp [emitAuthored] at compiled
        | cons current remainingBase =>
          by_cases same : name = declaration.name
          · cases tail : emitAuthored maxNodes plans rest later remainingBase (extend earlier declaration) with
            | none => simp [emitAuthored,same,tail] at compiled
            | some more =>
              have equal : current :: more = outputs := by simpa [emitAuthored,same,tail] using compiled
              subst outputs
              have extendedPrior := extend_plain earlier declaration prior (declared declaration (by simp))
              have remaining := ih later remainingBase (extend earlier declaration) more extendedPrior
                (fun value member => declared value (List.mem_cons_of_mem declaration member))
                (fun value member => basePlain value (List.mem_cons_of_mem current member)) tail
              intro output member
              rcases List.mem_cons.mp member with equal | inside
              · subst output
                exact basePlain current (by simp)
              · exact remaining output inside
          · simp [emitAuthored,same] at compiled
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih declarations base earlier outputs prior declared basePlain (by simpa [emitAuthored] using compiled)

/-- Every actual full authored program, including newly interleaved conditions,
derives the exact-evidence query inventory from successful original preparation. -/
theorem authored_plain (environment : Environment) (entries : List Entry) (whole : List Act)
    (observation : CompiledObservation)
    (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries whole = some observation) :
    ∀ output ∈ observation.program.outputs, PlainOutput output := by
  obtain ⟨prepared,sources,base,outputs,installed,_,baseBuilt,emitted,same⟩ :=
    StateAuthoredConditionOutputs.compiled_parts environment entries whole observation compiled
  subst observation
  have prior : PlainDefinitions ([] : Definitions Value) := by intro name definition impossible; simp at impossible
  have declared := prepared_declarations_plain environment entries prepared installed
  have basePlain := compile_declarations_plain prepared.declarations declared sources [] base prior baseBuilt
  exact emit_plain environment.profile.definition.bounds.maxList sources entries prepared.declarations base [] outputs
    prior declared basePlain emitted

/-- Full authored fault meaning follows from original preparation and actual
emitted membership; callers supply no query-strategy classification. -/
theorem authored_fault_refinement (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (whole : List Act) (valid : ∀ act ∈ whole, world act) (closed : CausallyClosed world whole)
    (observation : CompiledObservation)
    (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries whole = some observation)
    (output : Output Value) (member : output ∈ observation.program.outputs) (ids : Evidence) :
    output.observe whole observation.program.freezes = (outputName output,.fault ids) ↔
      observe world (outputSource output) whole = .fault ids := by
  exact output_fault_iff world whole valid closed output
    (authored_plain environment entries whole observation compiled output member) observation.program.freezes ids

end CBCL.StateAuthoredConditionPlain
