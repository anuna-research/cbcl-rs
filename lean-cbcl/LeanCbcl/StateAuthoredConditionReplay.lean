import LeanCbcl.StateAuthoredConditionPlain
import LeanCbcl.StateAuthoredConditionPreparation

/-! Exact witness replay for the complete authored condition output inventory. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredConditionReplay
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredOutputReplay StateOutputWitnessReplay StateCondition StateConditionCompiler

universe u v w

/-- Successful traversals of the same syntax retain paired compiled children. -/

theorem mapM_related {α : Type u} {β : Type v} {γ : Type w} (inputs : List α) (left : α → Option β) (right : α → Option γ)
    (relation : β → γ → Prop) (xs : List β) (ys : List γ)
    (each : ∀ input ∈ inputs, ∀ x y, left input = some x → right input = some y → relation x y)
    (first : inputs.mapM left = some xs) (second : inputs.mapM right = some ys) :
    List.Forall₂ relation xs ys := by
  induction inputs generalizing xs ys with
  | nil =>
    have hx : [] = xs := Option.some.inj first
    have hy : [] = ys := Option.some.inj second
    subst xs; subst ys
    exact .nil
  | cons head rest ih =>
    simp only [List.mapM_cons] at first second
    obtain ⟨x,hx,tx⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨xt,hxt,ex⟩ := Option.bind_eq_some_iff.mp tx
    obtain ⟨y,hy,ty⟩ := Option.bind_eq_some_iff.mp second
    obtain ⟨yt,hyt,ey⟩ := Option.bind_eq_some_iff.mp ty
    have ex' : x :: xt = xs := Option.some.inj ex
    have ey' : y :: yt = ys := Option.some.inj ey
    subst xs; subst ys
    exact .cons (each head (by simp) x y hx hy)
      (ih xt yt (fun input member => each input (List.mem_cons_of_mem head member)) hxt hyt)

/-- The dependency product retains every paired leaf error path. -/
theorem product_related (domains : List StateInstalledDomains.Domain) (A B : List Act) (truth : Value)
    (left right : List (Plan Value))
    (paired : List.Forall₂ (fun a b => StateReplayPaths.Related domains A B (path a) (path b)) left right) :
    StateReplayPaths.Related domains A B (path (StateConditionFaults.product truth left))
      (path (StateConditionFaults.product truth right)) := by
  induction paired with
  | nil => exact .same .clear True.intro
  | cons head tail ih => exact .join head ih

/-- Actual condition compilation pairs complete dependency paths across fresh
source dictionaries; no caller supplies a condition path or query classifier. -/
theorem compile_related (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (maxNodes : Nat) (left right : Plans Value) (definitions : Definitions Value)
    (related : StateReplayPaths.Environments domains A B (StateCompiledFreezeGrowth.paths left) (StateCompiledFreezeGrowth.paths right))
    (condition : Condition Value) (first second : Code Value)
    (compiledA : StateConditionCompiler.compile maxNodes left definitions condition = some first)
    (compiledB : StateConditionCompiler.compile maxNodes right definitions condition = some second) (truth : Value) :
    StateReplayPaths.Related domains A B (path (StateConditionFaults.dependencies truth first))
      (path (StateConditionFaults.dependencies truth second)) := by
  let P := fun condition : Condition Value => ∀ first second,
    StateConditionCompiler.compile maxNodes left definitions condition = some first →
    StateConditionCompiler.compile maxNodes right definitions condition = some second →
    StateReplayPaths.Related domains A B (path (StateConditionFaults.dependencies truth first))
      (path (StateConditionFaults.dependencies truth second))
  apply Condition.rec (motive_1 := P) (motive_2 := fun children => ∀ child ∈ children, P child)
    ?_ ?_ ?_ ?_ condition first second compiledA compiledB
  · intro field element first second ca cb
    obtain ⟨source,definition,query,found,_,_,rfl⟩ := compile_read_origin maxNodes left definitions field element first ca
    obtain ⟨other,_,_,otherFound,_,_,rfl⟩ := compile_read_origin maxNodes right definitions field element second cb
    have paired := related field
    rw [StateCompiledFreezeGrowth.lookup_paths,StateCompiledFreezeGrowth.lookup_paths,found,otherFound] at paired
    cases paired with
    | some proof => exact proof
  · intro children ih first second ca cb
    simp only [StateConditionCompiler.compile,Condition.fold_all] at ca cb
    by_cases invalid : maxNodes < (Condition.all children).size ∨ children.length < 2
    · simp [invalid] at ca
    simp only [invalid,↓reduceIte] at ca cb
    obtain ⟨xs,xa,xe⟩ := Option.bind_eq_some_iff.mp ca
    obtain ⟨ys,yb,ye⟩ := Option.bind_eq_some_iff.mp cb
    have fx : Code.all xs = first := Option.some.inj xe
    have fy : Code.all ys = second := Option.some.inj ye
    subst first; subst second
    have pairs := mapM_related children (StateConditionCompiler.compile maxNodes left definitions)
      (StateConditionCompiler.compile maxNodes right definitions)
      (fun x y => StateReplayPaths.Related domains A B (path (StateConditionFaults.dependencies truth x))
        (path (StateConditionFaults.dependencies truth y))) xs ys ih
      (by simpa only [List.mapM_map,Function.comp_def] using xa)
      (by simpa only [List.mapM_map,Function.comp_def] using yb)
    simp only [StateConditionFaults.dependencies,Code.fold_all]
    apply product_related
    clear ca cb xa yb xe ye

    induction pairs with
    | nil => exact .nil
    | cons head tail ih => exact .cons head ih
  · intro child impossible; simp at impossible
  · intro head tail headProof tailProof child member
    rcases List.mem_cons.mp member with equal | inside
    · simpa only [equal] using headProof
    · exact tailProof child inside


/-- Original authored interleaving preserves paired base and condition paths. -/
theorem emit_related (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (maxNodes : Nat) (left right : Plans Value)
    (related : StateReplayPaths.Environments domains A B (StateCompiledFreezeGrowth.paths left) (StateCompiledFreezeGrowth.paths right))
    (entries : List Entry) (declarations : List (Declaration Value)) (earlier : Definitions Value)
    (baseA baseB outputsA outputsB : List (Output Value))
    (baseRelated : List.Forall₂ (OutputRelated domains A B) baseA baseB)
    (first : emitAuthored maxNodes left entries declarations baseA earlier = some outputsA)
    (second : emitAuthored maxNodes right entries declarations baseB earlier = some outputsB) :
    List.Forall₂ (OutputRelated domains A B) outputsA outputsB := by
  induction entries generalizing declarations earlier baseA baseB outputsA outputsB with
  | nil =>
    cases declarations <;> cases baseA <;> simp [emitAuthored] at first
    subst outputsA
    cases baseB <;> simp [emitAuthored] at second
    subst outputsB
    exact .nil
  | cons entry rest ih =>
    cases entry with
    | condition name expression =>
      obtain ⟨codeA,ca,afterA⟩ := Option.bind_eq_some_iff.mp first
      obtain ⟨tailA,ta,fa⟩ := Option.bind_eq_some_iff.mp afterA
      obtain ⟨codeB,cb,afterB⟩ := Option.bind_eq_some_iff.mp second
      obtain ⟨tailB,tb,fb⟩ := Option.bind_eq_some_iff.mp afterB
      have ea : Output.condition name (.element (.scalar (.bool true))) codeA :: tailA = outputsA := Option.some.inj fa
      have eb : Output.condition name (.element (.scalar (.bool true))) codeB :: tailB = outputsB := Option.some.inj fb
      subst outputsA; subst outputsB
      exact .cons ⟨rfl,compile_related domains A B maxNodes left right earlier related expression codeA codeB ca cb _⟩
        (ih declarations earlier baseA baseB tailA tailB baseRelated ta tb)
    | field name _ | threshold name _ _ =>
      cases declarations with
      | nil => simp [emitAuthored] at first
      | cons declaration later =>
        cases baseRelated with
        | nil => simp [emitAuthored] at first
        | @cons a b as bs head tail =>
          by_cases names : name = declaration.name
          · cases ta : emitAuthored maxNodes left rest later as (extend earlier declaration) with
            | none => simp [emitAuthored,names,ta] at first
            | some xs =>
              cases tb : emitAuthored maxNodes right rest later bs (extend earlier declaration) with
              | none => simp [emitAuthored,names,tb] at second
              | some ys =>
                have ea : a :: xs = outputsA := by simpa [emitAuthored,names,ta] using first
                have eb : b :: ys = outputsB := by simpa [emitAuthored,names,tb] using second
                subst outputsA; subst outputsB
                exact .cons head (ih later (extend earlier declaration) as bs xs ys tail ta tb)
          · simp [emitAuthored,names] at first
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih declarations earlier baseA baseB outputsA outputsB baseRelated
        (by simpa [emitAuthored] using first) (by simpa [emitAuthored] using second)

/-- Successful complete compilation exposes source compilation and exact history. -/
theorem compiled_parts (environment : Environment) (entries : List Entry) (whole : List Act)
    (observation : CompiledObservation)
    (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries whole = some observation) :
    ∃ prepared sources base,
      prepareStatic environment entries = some prepared ∧
      StateAuthoredBindings.compile environment entries whole = some sources ∧
      compileDeclarations sources [] prepared.declarations = some base ∧
      emitAuthored environment.profile.definition.bounds.maxList sources entries prepared.declarations base [] = some observation.program.outputs ∧
      observation.history = whole := by
  obtain ⟨prepared,sources,base,outputs,installed,plans,built,emitted,same⟩ :=
    StateAuthoredConditionOutputs.compiled_parts environment entries whole observation compiled
  subst observation
  refine ⟨prepared,sources,base,installed,?_,built,emitted,rfl⟩
  simpa [StateAuthoredBindings.compile,prepare,installed,clauseAt] using plans

/-- Freshly compiled complete authored vectors pair all dependency paths. -/
theorem authored_outputs_related (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (A B : List Act) (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (left right : CompiledObservation)
    (leftCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
    (rightCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right) :
    ∃ prepared, prepareStatic environment entries = some prepared ∧
      List.Forall₂ (OutputRelated prepared.domains A B) left.program.outputs right.program.outputs := by
  obtain ⟨prepared,first,baseA,installed,sourceA,builtA,emittedA,_⟩ := compiled_parts environment entries A left leftCompiled
  obtain ⟨other,second,baseB,otherInstalled,sourceB,builtB,emittedB,_⟩ := compiled_parts environment entries B right rightCompiled
  have same : prepared = other := Option.some.inj (installed.symm.trans otherInstalled)
  subst other
  have paths := StateReplayPaths.authored_paths_related world environment entries prepared installed A B valid closed rooted
    first second sourceA sourceB
  have lookup := related_lookup prepared.domains A B _ _ paths
  have base := compile_declarations_related prepared.domains A B prepared.declarations [] first second baseA baseB lookup builtA builtB
  exact ⟨prepared,installed,emit_related prepared.domains A B _ first second lookup entries prepared.declarations []
    baseA baseB left.program.outputs right.program.outputs base emittedA emittedB⟩

/-- Actual emitted authored observations replay faults with containing evidence
across complete receiver recompilation. Neither a plain-query assumption nor a
caller-supplied source-plan pairing remains. -/
theorem authored_output_fault_replays (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (A B : List Act) (unique : NodupAddr A) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (left right : CompiledObservation)
    (leftCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
    (rightCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right)
    (name : String) (e : Evidence) (fault : (name,.fault e) ∈ left.observe)
    (accepted : StateWitnessReplay.Accepts A e B) :
    ∃ enlarged, (name,.fault enlarged) ∈ right.observe ∧ ∀ id ∈ e, id ∈ enlarged := by
  obtain ⟨prepared,_,paired⟩ := authored_outputs_related world environment entries A B validA closedB rooted
    left right leftCompiled rightCompiled
  obtain ⟨_,_,_,_,_,_,_,firstHistory⟩ := compiled_parts environment entries A left leftCompiled
  obtain ⟨_,_,_,_,_,_,_,secondHistory⟩ := compiled_parts environment entries B right rightCompiled
  have sourceFault : (name,.fault e) ∈ left.program.outputs.map (Output.observe A left.program.freezes) := by
    simpa [CompiledObservation.observe,Program.observe,firstHistory] using fault
  obtain ⟨enlarged,emitted,contains⟩ := code_fault_replays world prepared.domains A B unique validA validB closedA closedB
    left.program.outputs right.program.outputs paired (StateAuthoredConditionPlain.authored_plain environment entries A left leftCompiled)
    left.program.freezes right.program.freezes name e sourceFault accepted
  exact ⟨enlarged,by simpa [CompiledObservation.observe,Program.observe,secondHistory] using emitted,contains⟩

/-- Actual emitted authored faults report only accepted act identities. -/
theorem authored_output_evidence_supported (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (A : List Act) (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A)
    (observation : CompiledObservation) (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries A = some observation)
    (name : String) (e : Evidence) (fault : (name,.fault e) ∈ observation.observe) :
    StateEvidenceSupport.Supported A e := by
  obtain ⟨_,_,_,_,_,_,_,history⟩ := compiled_parts environment entries A observation compiled
  have member : (name,.fault e) ∈ observation.program.outputs.map (Output.observe A observation.program.freezes) := by
    simpa [CompiledObservation.observe,Program.observe,history] using fault
  obtain ⟨output,inside,emitted⟩ := List.mem_map.mp member
  have correctName : (output.observe A observation.program.freezes).1 = outputName output := by cases output <;> rfl
  have nameEqual : outputName output = name := correctName.symm.trans (congrArg Prod.fst emitted)
  have sourceFault := (output_fault_iff world A valid closed output
    (StateAuthoredConditionPlain.authored_plain environment entries A observation compiled output inside) observation.program.freezes e).mp
      (by simpa [nameEqual] using emitted)
  exact StateEvidenceSupport.observation_supported world (outputSource output) A e sourceFault

/-- Authored output code can be recompiled at a ranked content-consistent
receiver history, using the already proved complete output/cache compiler. -/
theorem authored_output_recompiles (environment : Environment) (entries : List Entry) (A B : List Act)
    (left : CompiledObservation) (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
    (ranked : StateExecutableFreeze.Ranked B) (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ right, StateAuthoredConditionOutputs.compileAuthored environment entries B = some right := by
  obtain ⟨prepared,_,_,installed,_,_,_,_⟩ := compiled_parts environment entries A left compiled
  exact StateAuthoredConditionPreparation.prepared_output_exists environment entries prepared installed B ranked consistent

open StateKernelDelivery AdmissionStratification StateRefinement

/-- A finite exact list of reported actual witness acts suffices for eventual
same-named faults in every freshly compiled emitted receiver output vector.
All earlier evidence is retained; no whole-source-history delivery is used. -/
theorem eventual_authored_output_witness_fault {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (environment : Environment) (entries : List Entry)
    (atTime : Nat) (observation : CompiledObservation)
    (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries (left.run atTime).accepted = some observation)
    (name : String) (e : Evidence) (fault : (name,.fault e) ∈ observation.observe) :
    ∃ witness : List Act,
      (∀ act, act ∈ witness ↔ act ∈ (left.run atTime).accepted ∧ act.addr ∈ e) ∧
      (∀ id, id ∈ witness.map Act.addr ↔ id ∈ e) ∧
      ∃ time, ∀ n, time ≤ n → ∃ current enlarged,
        StateAuthoredConditionOutputs.compileAuthored environment entries (right.run n).accepted = some current ∧
        (name,.fault enlarged) ∈ current.observe ∧ ∀ id ∈ e, id ∈ enlarged := by
  classical
  let A := (left.run atTime).accepted
  have validA := accepted_valid left atTime
  have closedA := replica_causal_closed left admission atTime
  have uniqueA := (reachable_wellFormed (behavior_reachable left.behavior atTime)).accepted_unique
  have support := authored_output_evidence_supported H.contains environment entries A validA closedA observation compiled name e fault
  let witness := A.filter (fun act => decide (act.addr ∈ e))
  have exactWitness : ∀ act, act ∈ witness ↔ act ∈ A ∧ act.addr ∈ e := by intro act; simp [witness]
  have exactIds : ∀ id, id ∈ witness.map Act.addr ↔ id ∈ e := by
    intro id
    constructor
    · intro member
      obtain ⟨act,inside,identity⟩ := List.mem_map.mp member
      simpa [identity] using ((exactWitness act).mp inside).2
    · intro member
      obtain ⟨act,inside,identity⟩ := List.mem_map.mp (support id member)
      exact List.mem_map.mpr ⟨act,(exactWitness act).mpr ⟨inside,by simpa [identity] using member⟩,identity⟩
  obtain ⟨time,delivered⟩ := witness_dissemination left right witness atTime
    (fun act inside => ((exactWitness act).mp inside).1)
  have rooted := StateContextReplay.rooted_openers_of_dependencies H causal (StateInstalledContext.evidenceInput environment.profile)
  refine ⟨witness,exactWitness,exactIds,time,fun n later => ?_⟩
  have uniqueB := (reachable_wellFormed (behavior_reachable right.behavior n)).accepted_unique
  obtain ⟨current,currentCompiled⟩ := authored_output_recompiles environment entries A (right.run n).accepted observation compiled
    (replica_ranked right admission causal n) (fun a ma b mb same => uniqueB.eq_of_addr ma mb same)
  have accepted : StateWitnessReplay.Accepts A e (right.run n).accepted := by
    intro act inside named
    exact delivered n later act ((exactWitness act).mpr ⟨inside,named⟩)
  obtain ⟨enlarged,emitted,contains⟩ := authored_output_fault_replays H.contains environment entries A (right.run n).accepted
    uniqueA validA (accepted_valid right n) closedA (replica_causal_closed right admission n) rooted
    observation current compiled currentCompiled name e fault accepted
  exact ⟨current,enlarged,currentCompiled,emitted,contains⟩


end CBCL.StateAuthoredConditionReplay
