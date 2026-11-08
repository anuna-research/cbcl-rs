import LeanCbcl.StateInstalledContext

/-! Executable context observations for the live oracle. Frontier predicates
and fault witnesses are enumerable; cast, pin, roster and metadata semantics
come from the installed context factories rather than a separate interpreter. -/
set_option autoImplicit false
namespace CBCL.StateExecutableContext
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledLegacy
open StateInstalledContext

/-- Enumerable fault identities interpreted as the existing semantic error. -/
def semanticError (error : Option (List Nat)) : Error :=
  error.map (fun addresses => fun address => address ∈ addresses)

/-- Collect addresses selected by a concrete contribution predicate. -/
def identities (selected : Act → Bool) (A : List Act) : List Nat := (A.filter selected).map Act.addr

/-- The sole-value lattice retains exactly the selected accepted identities. -/
theorem identities_evidence (selected : Act → Bool) (decode : Act → Option Val) (A : List Act) (address : Nat) :
    address ∈ identities selected A ↔
      Sole.evidence (lift (fun act => if selected act then Sole.one act.addr (decode act) else .bot) A) address := by
  change address ∈ identities selected A ↔ address ∈ Sole.evidence (lift (fun act => if selected act then Sole.one act.addr (decode act) else .bot) A)
  induction A with
  | nil => simp [identities,lift_nil,Sole.evidence,JoinSemilatticeBot.bot]
  | cons act rest ih =>
    rw [lift_cons,sole_evidence_join]
    cases chosen : selected act with
    | false =>
      simpa only [identities,List.filter_cons,chosen,Bool.false_eq_true,if_false,Sole.evidence,
        Lattice.Set.mem_empty,false_or] using ih
    | true =>
      simpa only [identities,List.filter_cons,chosen,if_true,List.map_cons,List.mem_cons,Sole.evidence,
        Lattice.Set.mem_singleton] using (or_congr (Iff.refl (address = act.addr)) ih)

/-- All root identities accompany a context-root fault, including malformed casts. -/
def rootError (profile : Profile) (A : List Act) : Option (List Nat) :=
  match StateContext.read (rootDecoder profile) A with
  | .fault _ => some (identities (fun act => act.preds.isEmpty) A)
  | _ => none

/-- Concrete root witness lists equal the semantic root-fault channel. -/
theorem root_error_refinement (profile : Profile) (A : List Act) :
    semanticError (rootError profile A) = (StateContextEvidence.rootSpec (evidenceInput profile)).read A := by
  cases observed : StateContext.read (rootDecoder profile) A with
  | pending | value _ => simp [rootError,observed,StateContextEvidence.rootSpec,semanticError,evidenceInput,contextError]
  | fault evidence =>
    have witnesses := StateContext.fault_evidence observed
    simp only [rootError,observed,semanticError,Option.map_some,StateContextEvidence.rootSpec,evidenceInput,contextError]
    apply congrArg some
    funext address
    apply propext
    rw [witnesses]
    exact identities_evidence (fun act => act.preds.isEmpty) (rootDecoder profile) A address

/-- Mixed-thread witnesses retain every accepted identity. -/
def mixedError (profile : Profile) (A : List Act) : Option (List Nat) :=
  if StateContextEvidence.mixedCheck (evidenceInput profile) A then some (A.map Act.addr) else none

/-- Concrete mixed-thread witnesses equal the existing semantic channel. -/
theorem mixed_error_refinement (profile : Profile) (A : List Act) :
    semanticError (mixedError profile A) = StateContextEvidence.mixedError (evidenceInput profile) A := by
  unfold mixedError StateContextEvidence.mixedError
  split
  · simp only [semanticError,Option.map_some]
    apply congrArg some
    funext address
    apply propext
    simp only [List.mem_map,acceptedEvidence]
  · rfl

/-- Competing opener witnesses are visible only after some thread root is present. -/
def openerError (profile : Profile) (A : List Act) : Option (List Nat) :=
  if StateContextEvidence.hasRoot A then
    match lift (StateContextEvidence.openerContribution (evidenceInput profile)) A with
    | .top _ => some (identities (fun act => profile.definition.opener == some act.verb) A)
    | _ => none
  else none

/-- Concrete opener witnesses equal the existing semantic opener-fault channel. -/
theorem opener_error_refinement (profile : Profile) (A : List Act) :
    semanticError (openerError profile A) = StateContextEvidence.openerError (evidenceInput profile) A := by
  unfold openerError StateContextEvidence.openerError
  split
  · cases carrier : lift (StateContextEvidence.openerContribution (evidenceInput profile)) A with
    | bot | one _ _ => simp [carrier,semanticError,StateContextEvidence.soleError]
    | top evidence =>
      simp only [carrier,semanticError,Option.map_some,StateContextEvidence.soleError]
      apply congrArg some
      funext address
      apply propext
      have selected := identities_evidence (fun act => profile.definition.opener == some act.verb) (fun _ => none) A address
      have carrier' : lift (fun act => if profile.definition.opener == some act.verb then Sole.one act.addr none else .bot) A = .top evidence := by
        simpa only [StateContextEvidence.openerContribution,evidenceInput] using carrier
      rw [carrier'] at selected
      exact selected
  · rfl

/-- Concatenate independent evidence lists while preserving the absence channel. -/
def join (left right : Option (List Nat)) : Option (List Nat) :=
  match left,right with
  | none,other | other,none => other
  | some a,some b => some (a ++ b)

/-- Enumerable concatenation implements semantic witness union exactly. -/
theorem join_refinement (left right : Option (List Nat)) :
    semanticError (join left right) = unionError (semanticError left) (semanticError right) := by
  cases left <;> cases right <;> simp only [join,semanticError,Option.map_none,Option.map_some,unionError]
  next a b =>
    apply congrArg some
    funext address
    exact propext List.mem_append

/-- Context paths select the same root/mixed/opener channels as the installed factory. -/
def error (profile : Profile) (path : List String) (A : List Act) : Option (List Nat) :=
  if needsThread path then join (rootError profile A)
    (join (mixedError profile A) (if observesOpener path then openerError profile A else none)) else none

/-- All executable context faults, including diagnostic-precedence unions, refine the existing reader. -/
theorem error_refinement (profile : Profile) (path : List String) (A : List Act) :
    semanticError (error profile path A) =
      if needsThread path then StateContextEvidence.nativeRead (evidenceInput profile) (observesOpener path) A else none := by
  have openerMap : semanticError (if observesOpener path then openerError profile A else none) =
      if observesOpener path then StateContextEvidence.openerError (evidenceInput profile) A else none := by
    cases observesOpener path <;> simp only [Bool.false_eq_true,if_false,if_true]
    · rfl
    · exact opener_error_refinement profile A
  have emptyRight (error : Error) : unionError error none = error := by cases error <;> rfl
  unfold error
  split
  · rw [join_refinement,join_refinement,root_error_refinement,mixed_error_refinement,openerMap,
      StateContextEvidence.native_context_witness_refinement]
    cases observesOpener path <;>
      simp [StateContextEvidence.spec,StateContextEvidence.joinSpec,StateContextEvidence.mixedSpec,
        StateContextEvidence.openerSpec,emptyRight]
  · rfl

/-- Compute frontier membership by finite parent scans. -/
def frontier (profile : Profile) (A : List Act) : Value := .kernel (.values (fun value =>
  A.any (fun act => value == .str (profile.address act.addr) &&
    !(A.any (fun child => child.preds.contains act.addr)))))

/-- Executable frontier membership equals the original logical predicate. -/
theorem frontier_refinement (profile : Profile) (A : List Act) :
    frontier profile A = StateInstalledContext.frontier profile A := by
  classical
  apply congrArg Value.kernel
  apply congrArg StateKernel.Observation.values
  funext value
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true,List.any_eq_false]

/-- Current accepted-set size and frontier using executable definitions. -/
def observation (profile : Profile) (A : List Act) : Value :=
  .object [("accepted-count",number (FinSet.card (lift StateLift.address A))),("frontier",frontier profile A)]

/-- The executable observation map equals the original snapshot metadata. -/
theorem observation_refinement (profile : Profile) (A : List Act) :
    observation profile A = StateInstalledContext.observation profile A := by
  simp only [observation,StateInstalledContext.observation,frontier_refinement]

/-- Execute the same closed context path grammar, replacing only snapshot enumeration. -/
def value (profile : Profile) (path : List String) (A : List Act) : Option Value :=
  match path with
  | [] => some (.object [("dialect",dialect profile.definition),("thread",(thread profile A).getD absent),
      ("observation",observation profile A)])
  | "dialect"::rest => some (lookupPath (dialect profile.definition) rest)
  | "thread"::rest => (thread profile A).map (fun current => lookupPath current rest)
  | "observation"::rest => some (lookupPath (observation profile A) rest)
  | _ => none

/-- Every executable path value equals the installed context value. -/
theorem value_refinement (profile : Profile) (path : List String) (A : List Act) :
    value profile path A = StateInstalledContext.value profile path A := by
  cases path with
  | nil => simp [value,StateInstalledContext.value,observation_refinement]
  | cons head rest =>
    by_cases dialectPath : head = "dialect"
    · simp [value,StateInstalledContext.value,dialectPath]
    · by_cases threadPath : head = "thread"
      · simp [value,StateInstalledContext.value,threadPath]
      · by_cases observationPath : head = "observation"
        · simp [value,StateInstalledContext.value,observationPath,observation_refinement]
        · simp [value,StateInstalledContext.value,dialectPath,threadPath,observationPath]

/-- Enumerable context result before canonical serialization. -/
structure Result where
  /-- Optional concrete terminal witness list. -/
  error : Option (List Nat)
  /-- Available typed context data. -/
  value : Option Value

/-- Convert the computable result into the existing typed context observation. -/
def Result.semantic (stable : Bool) (result : Result) : Observation Value :=
  match result.error with
  | some addresses => .fault (fun address => address ∈ addresses)
  | none => .data (optionalData stable result.value)

/-- Compute a complete context read without classical witness enumeration. -/
def read (profile : Profile) (path : List String) (A : List Act) : Result :=
  ⟨error profile path A,value profile path A⟩

/-- Complete executable context read refinement, with no host fault classifier. -/
theorem read_refinement (profile : Profile) (path : List String) (A : List Act) :
    (read profile path A).semantic (stablePath path) = nativeRead profile path A := by
  have faults := error_refinement profile path A
  unfold read Result.semantic nativeRead
  rw [← faults,← value_refinement]
  cases error profile path A <;> rfl

end CBCL.StateExecutableContext
