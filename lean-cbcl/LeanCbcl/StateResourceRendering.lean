import LeanCbcl.StateResourceVerifier
import LeanCbcl.StateAddressPool
import LeanCbcl.StateFaultRendering

/-! Executable complete resource witness enumeration and canonical JSON.
Address projection and diagnostic reason are explicit representation inputs;
literal native metadata extraction is not assumed proved by this module. -/
set_option autoImplicit false
namespace CBCL.StateResourceRendering
open State CheckpointEvidence StateResource StateResourcePreflight StateResourceVerifier

/-- Recognize configured resource facts and cast-bearing context. -/
def relevantCheck (c : ResourceConfig) (node : ResourceFact) : Bool :=
  node.data.selected.verb == c.initialVerb ||
    StateResourceCycle.operationVerbCheck c node.data.selected.verb || node.data.selected.bindings != .absent

/-- Resource relevance check preserves the certificate's semantic selection. -/
theorem relevant_check (c : ResourceConfig) (node : ResourceFact) :
    relevantCheck c node = true ↔ relevant c node := by
  simp only [relevantCheck,Bool.or_eq_true,beq_iff_eq,bne_iff_ne,
    StateResourceCycle.operationVerbCheck_iff,relevant,initial,or_assoc]

/-- Check every causal, owner-previous and declared dependency citation. -/
def citedCheck (node : ResourceFact) (id : Nat) : Bool :=
  node.data.selected.predecessors.contains id || (links node).contains id

/-- Citation checks preserve all semantic resource reference classes. -/
theorem cited_check (node : ResourceFact) (id : Nat) :
    citedCheck node id = true ↔ cited node id := by
  simp [citedCheck,cited]

/-- Enumerate present relevant facts and present cited context only.
Unsupported profiles keep their existing empty contextual evidence. -/
def witnesses (c : ResourceConfig) (facts : Facts) : List Nat :=
  if unsupportedCheck c then [] else
    (facts.filter (fun node => relevantCheck c node ||
      facts.any (fun parent => relevantCheck c parent && citedCheck parent node.id))).map Fact.id

/-- Enumeration realizes exactly the complete contextual certificate predicate;
no caller supplies its support, availability or ordering. -/
theorem witnesses_realize (c : ResourceConfig) (facts : Facts) :
    StateFaultRendering.Realizes (factsEvidence c facts) (witnesses c facts) := by
  intro id
  cases supported : unsupportedCheck c with
  | true => simp [witnesses,supported,factsEvidence]
  | false =>
    simp only [witnesses,supported,Bool.false_eq_true,ite_false,List.mem_map,List.mem_filter,
      Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true,relevant_check,cited_check,factsEvidence,true_and]
    constructor
    · rintro ⟨node,⟨member,selected⟩,same⟩
      subst id
      exact ⟨node,member,rfl,selected⟩
    · rintro ⟨node,member,same,selected⟩
      subst id
      exact ⟨node,⟨member,selected⟩,rfl⟩

/-- Serialize only the complete evidence array with the same operational pool
sorting and deduplication used by the full fault wrapper. -/
def evidenceBytes (c : ResourceConfig) (facts : Facts) (address : Nat → String) : Option String :=
  ((StateAddressPool.sortPool ((witnesses c facts).map address).toArray).map StateAddressDigits.adjacent).map
    (fun names => StateJsonValue.emit (.list (names.map StateJsonValue.Value.str)) "")

/-- Operational evidence bytes match the exact canonical witness presentation. -/
theorem evidence_bytes (c : ResourceConfig) (facts : Facts) (address : Nat → String) :
    evidenceBytes c facts address = some (StateJsonValue.render (.list
      ((StateFaultRendering.canonical ((witnesses c facts).map address)).map StateJsonValue.Value.str))) := by
  simp only [evidenceBytes,StateAddressPool.canonical_output,Option.map_some,StateJsonValue.empty_buffer]

/-- Native-shaped witness normalization and byte emission after actual verifier
classification, using the proved operational address-pool implementation. -/
def faultBytes (input : Input) (reason : String) (address : Nat → String) : Option String :=
  if StateResourceValidated.isFault (StateResourceVerifier.observe input) then
    StateAddressPool.faultBytes reason ((witnesses input.config input.facts).map address).toArray
  else none

/-- Actual fault classification yields exact canonical certificate JSON,
including the complete semantic witness set, without a chosen enumeration. -/
theorem fault_serialized (input : Input) (reason : String) (address : Nat → String)
    (faulted : StateResourceValidated.isFault (StateResourceVerifier.observe input) = true) :
    faultBytes input reason address = some (StateJsonValue.render
      (StateFaultRendering.semanticFault reason address (factsEvidence input.config input.facts)
        ⟨witnesses input.config input.facts,witnesses_realize input.config input.facts⟩)) := by
  simp only [faultBytes,faulted,ite_true,StateAddressPool.faultBytes_refinement]
  rw [StateFaultRendering.realized_fault reason address _ _ (witnesses_realize input.config input.facts)]

/-- The proved concrete resource certificate, full verifier, evidence enumeration
and JSON renderer compose through one public fault result. -/
theorem certificate_serialized (input : Input) (reason : String) (address : Nat → String)
    (cause : Cause input.config input.facts) :
    faultBytes input reason address = some (StateJsonValue.render
      (StateFaultRendering.semanticFault reason address (factsEvidence input.config input.facts)
        ⟨witnesses input.config input.facts,witnesses_realize input.config input.facts⟩)) :=
  fault_serialized input reason address ((native_verifier_certificate_iff input).mpr cause)

/-- Growth of immutable accepted facts retains every executable witness,
including context that becomes relevant only through a later citation. -/
theorem witnesses_grow (c : ResourceConfig) {A B : Facts} (inside : Included A B) :
    ∀ id ∈ witnesses c A, id ∈ witnesses c B := by
  intro id member
  apply (witnesses_realize c B id).mpr
  obtain ⟨supported,node,accepted,same,selected⟩ := (witnesses_realize c A id).mp member
  refine ⟨supported,node,inside node accepted,same,?_⟩
  rcases selected with direct | ⟨parent,parentAccepted,parentRelevant,citation⟩
  · exact Or.inl direct
  · exact Or.inr ⟨parent,inside parent parentAccepted,parentRelevant,citation⟩

/-- Sorting and deduplication retain all previously emitted witness names under
one fixed address representation; no ordering or uniqueness oracle is supplied. -/
theorem names_grow (c : ResourceConfig) {A B : Facts} (inside : Included A B) (address : Nat → String) :
    ∀ name ∈ StateFaultRendering.canonical ((witnesses c A).map address),
      name ∈ StateFaultRendering.canonical ((witnesses c B).map address) := by
  apply StateFaultRendering.canonical_growth
  intro name member
  obtain ⟨id,insideA,rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨id,witnesses_grow c inside id insideA,rfl⟩

/-- A real serialized resource fault cannot disappear under accepted growth.
The later diagnostic reason may differ; canonical evidence retains every earlier
name. Configuration and immutable address projection remain fixed. -/
theorem serialized_fault_persists (left right : Input) (sameConfig : right.config = left.config)
    (inside : Included left.facts right.facts) (leftReason rightReason : String) (address : Nat → String)
    (bytes : String) (emitted : faultBytes left leftReason address = some bytes) :
    ∃ later, faultBytes right rightReason address = some later ∧
      ∀ name ∈ StateFaultRendering.canonical ((witnesses left.config left.facts).map address),
        name ∈ StateFaultRendering.canonical ((witnesses right.config right.facts).map address) := by
  have faulted : StateResourceValidated.isFault (StateResourceVerifier.observe left) = true := by
    cases checked : StateResourceValidated.isFault (StateResourceVerifier.observe left) with
    | false => simp [faultBytes,checked] at emitted
    | true => rfl
  have cause := (native_verifier_certificate_iff left).mp faulted
  have enlarged : Cause right.config right.facts := by
    rw [sameConfig]
    exact cause_mono left.config inside cause
  refine ⟨_,certificate_serialized right rightReason address enlarged,?_⟩
  rw [sameConfig]
  exact names_grow left.config inside address

end CBCL.StateResourceRendering
