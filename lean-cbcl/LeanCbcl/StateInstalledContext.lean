import LeanCbcl.StateInstalledLegacy
import LeanCbcl.StateContextEvidence

/-! Closed context-path factories over recognized installed metadata and typed
per-address message metadata. Cast/wire extraction is an input boundary;
cardinality, completeness, duplicate and dialect-pin checks are executable here.
No history fault classifier or display callback is provided by the caller. -/
set_option autoImplicit false

namespace CBCL.StateInstalledContext
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open CheckpointEvidence StateInstalledLegacy

/-- An installed role name and its singleton or indexed cardinality. -/
structure Role where
  /-- The installed name. -/
  name : String
  /-- Whether the role admits an indexed roster instead of one account. -/
  indexed : Bool
  deriving DecidableEq

/-- The fixed state bounds exposed as dialect context data. -/
structure Bounds where
  /-- The installed maximum number of state fields. -/
  maxFields : Nat
  /-- The installed list-size bound. -/
  maxList : Nat
  /-- The installed numeric bound. -/
  maxNumber : Int
  /-- The installed string-size bound. -/
  maxString : Nat

/-- Immutable dialect identity, role, bound, and protocol-opener metadata. -/
structure Definition where
  /-- The installed name. -/
  name : String
  /-- The immutable content-address representation. -/
  address : String
  /-- The immutable dialect body address. -/
  bodyAddress : String
  /-- The optional installed dialect author identity. -/
  author : Option String
  /-- Render every declared role roster from the same validated cast. -/
  roles : List Role
  /-- The installed state representation bounds. -/
  bounds : Bounds
  /-- The protocol opener verb, when the installed protocol defines one. -/
  opener : Option String

/-- Typed fields reconstructed from each accepted message. Absence and malformed
cast/pin syntax are retained separately, as in native recognized inputs. -/
structure MessageMetadata where
  /-- Render sealed root, role, and opener metadata from accepted history. -/
  thread : Option String
  /-- Validate typed cast and pin metadata against the installed definition. -/
  cast : ResourceField (List ResourceRoleBinding)
  /-- The recognized optional dialect-address pin. -/
  pin : ResourceField String

/-- The installed definition and immutable per-address metadata extraction boundary. -/
structure Profile where
  /-- The fixed installed dialect definition. -/
  definition : Definition
  /-- Typed message metadata indexed by accepted act address. -/
  metadata : Nat → MessageMetadata
  /-- The immutable content-address representation. -/
  address : Nat → String

/-- The common context payload for a missing scalar value. -/
def absent : Value := .kernel (.cell .absent)
/-- Embed a context string in the common installed observation payload. -/
def text (value : String) : Value := .kernel (.cell (.value (.str value)))
/-- Embed a context integer in the common installed observation payload. -/
def number (value : Int) : Value := .kernel (.integer value)
/-- Render optional text, preserving absence when metadata is unavailable. -/
def optionalText (value : Option String) : Value := value.map text |>.getD absent

/-- Read an object member, returning absence when it is missing. -/
def lookup (value : Value) (key : String) : Value :=
  match value with
  | .object fields => (fields.lookup key).getD absent
  | _ => absent

/-- Follow the declared context path through the rendered object. -/
def lookupPath (value : Value) (path : List String) : Value := path.foldl lookup value

/-- Check role completeness, known roles, roster uniqueness, and declared cardinality. -/
def bindingsCheck (definition : Definition) (bindings : List ResourceRoleBinding) : Bool :=
  decide (bindings.map ResourceRoleBinding.role).Nodup &&
    bindings.all (fun binding => !binding.accounts.isEmpty && decide binding.accounts.Nodup &&
      definition.roles.any (fun role => role.name == binding.role && (role.indexed || binding.accounts.length == 1))) &&
    definition.roles.all (fun role => bindings.any (fun binding => binding.role == role.name))

/-- Validate typed cast and pin metadata against the installed definition. -/
def cast (profile : Profile) (address : Nat) : Option (List ResourceRoleBinding) := do
  let metadata := profile.metadata address
  match metadata.pin with
  | .malformed _ => none
  | .value pin => if pin != profile.definition.address then none else pure ()
  | .absent => pure ()
  match metadata.cast with
  | .absent => if profile.definition.roles.isEmpty then some [] else none
  | .malformed _ => none
  | .value bindings => if bindingsCheck profile.definition bindings then some bindings else none

/-- Decode a validated root into its immutable identity and signer token. -/
def rootDecoder (profile : Profile) (act : Act) : Option Val :=
  (cast profile act.addr).map (fun _ => .list [.int (Int.ofNat act.addr),.str act.signer])

/-- Generate fault-check metadata from this same installed context profile. -/
def evidenceInput (profile : Profile) : StateContextEvidence.Input :=
  ⟨rootDecoder profile,(fun act => (profile.metadata act.addr).thread),profile.definition.opener⟩

/-- Render the immutable installed dialect metadata map. -/
def dialect (definition : Definition) : Value := .object [
  ("name",text definition.name),("address",text definition.address),("body-address",text definition.bodyAddress),
  ("author",optionalText definition.author),
  ("roles",.object (definition.roles.map (fun role => (role.name,text (if role.indexed then "indexed" else "singleton"))))),
  ("bounds",.object [("max-fields",number definition.bounds.maxFields),("max-list",number definition.bounds.maxList),
    ("max-number",number definition.bounds.maxNumber),("max-string",number definition.bounds.maxString)])]

/-- Read one declared role roster from the validated sealed cast. -/
def roster (members : List String) : Value :=
  .kernel (.values (fun value => match value with | .str name => members.contains name | _ => false))

/-- Render every declared role roster from the same validated cast. -/
def roles (bindings : List ResourceRoleBinding) : Value :=
  .object (bindings.map (fun binding => (binding.role,roster binding.accounts)))

/-- Read the sole accepted opener identity, or pending/conflicting evidence. -/
def openerValue (profile : Profile) (A : List Act) : Value :=
  match lift (StateContextEvidence.openerContribution (evidenceInput profile)) A with
  | .one address _ => text (profile.address address)
  | _ => absent -- The independent fault channel handles a fork.

/-- Render sealed root, role, and opener metadata from accepted history. -/
def thread (profile : Profile) (A : List Act) : Option Value := do
  match StateContext.read (rootDecoder profile) A with
  | .pending | .fault _ => none
  | .value token => match token with
    | .list [.int address,.str signer] => do
      let bindings ← cast profile address.toNat
      some (.object [("id",optionalText (profile.metadata address.toNat).thread),
        ("root",text (profile.address address.toNat)),("initiator",text signer),
        ("opener",openerValue profile A),("roles",roles bindings)])
    | _ => none

/-- The accepted act addresses not referenced by another accepted act. -/
noncomputable def frontier (profile : Profile) (A : List Act) : Value := by
  classical
  exact .kernel (.values (fun value => decide (∃ act ∈ A, value = .str (profile.address act.addr) ∧
    ¬∃ child ∈ A, act.addr ∈ child.preds)))

/-- Render current accepted-count and frontier snapshot metadata. -/
noncomputable def observation (profile : Profile) (A : List Act) : Value :=
  .object [("accepted-count",number (FinSet.card (lift StateLift.address A))),("frontier",frontier profile A)]

/-- Render the requested closed context path on accepted history. -/
noncomputable def value (profile : Profile) (path : List String) (A : List Act) : Option Value :=
  match path with
  | [] => some (.object [("dialect",dialect profile.definition),("thread",(thread profile A).getD absent),
      ("observation",observation profile A)])
  | "dialect"::rest => some (lookupPath (dialect profile.definition) rest)
  | "thread"::rest => (thread profile A).map (fun current => lookupPath current rest)
  | "observation"::rest => some (lookupPath (observation profile A) rest)
  | _ => none

/-- Recognize the complete context path grammar, including declared nested roles. -/
def validPath (definition : Definition) : List String → Bool
  | [] | ["dialect"] | ["thread"] | ["observation"] => true
  | ["dialect","address"] | ["dialect","body-address"] | ["dialect","name"] | ["dialect","author"]
  | ["dialect","roles"] | ["dialect","bounds"] => true
  | ["dialect","bounds","max-fields"] | ["dialect","bounds","max-list"]
  | ["dialect","bounds","max-number"] | ["dialect","bounds","max-string"] => true
  | ["dialect","roles",role] | ["thread","roles",role] => definition.roles.any (fun declared => declared.name == role)
  | ["thread","id"] | ["thread","root"] | ["thread","initiator"] | ["thread","opener"] | ["thread","roles"] => true
  | ["observation","accepted-count"] | ["observation","frontier"] => true
  | _ => false

/-- Identify immutable dialect and sealed thread leaf projections. -/
def stablePath : List String → Bool
  | "dialect"::_ => true
  | "thread"::key::_ => ["id","root","initiator","opener","roles"].contains key
  | _ => false

/-- Whether this path depends on accepted opener uniqueness. -/
def observesOpener : List String → Bool
  | [] | ["thread"] | ["thread","opener"] => true
  | _ => false

/-- Whether this path depends on sealed thread evidence. -/
def needsThread : List String → Bool
  | [] | "thread"::_ => true
  | _ => false

/-- Build the path-scoped context fault channels from the same profile. -/
def errorSpec (profile : Profile) (path : List String) : ErrorSpec :=
  if needsThread path then StateContextEvidence.spec (evidenceInput profile) (observesOpener path)
  else {read := fun _ => none,equiv := fun _ => rfl,grow := by intros; intro evidence fault; contradiction}

/-- Construct the context source with its path-specific status and error guard. -/
noncomputable def source (profile : Profile) (path : List String) : Source Value :=
  .guardCertified (errorSpec profile path) (.read (stablePath path)
    (fun carrier => value profile path (StateInstalledLegacy.history carrier)))

/-- Permit existing membership reads only on declared sealed role rosters. -/
def queryPolicy (path : List String) : Option (StateInstalledLowering.NativeRead Value) :=
  match path with
  | ["thread","roles",_] => some ⟨readTest,readCheck (fun element => match element with | .member value => scalar value | _ => false)⟩
  | _ => none

/-- Validate a context path before constructing its source and read policy. -/
noncomputable def make (profile : Profile) (path : List String) : Option (StateInstalledLowering.Definition Value) :=
  if validPath profile.definition path then some (.native (source profile path) (queryPolicy path)) else none

theorem openerValue_setEq (profile : Profile) {A B : List Act} (same : SetEq A B) :
    openerValue profile A = openerValue profile B := by
  simp only [openerValue,lift_setEq (StateContextEvidence.openerContribution (evidenceInput profile)) same]

theorem thread_setEq (profile : Profile) {A B : List Act} (same : SetEq A B) :
    thread profile A = thread profile B := by
  simp only [thread,StateContext.read_setEq (rootDecoder profile) same,openerValue_setEq profile same]

theorem frontier_setEq (profile : Profile) {A B : List Act} (same : SetEq A B) :
    frontier profile A = frontier profile B := by
  classical
  apply congrArg Value.kernel
  apply congrArg StateKernel.Observation.values
  funext value
  apply decide_eq_decide.2
  have membership : ∀ act, act ∈ A ↔ act ∈ B := same
  simp only [membership]

theorem observation_setEq (profile : Profile) {A B : List Act} (same : SetEq A B) :
    observation profile A = observation profile B := by
  simp only [observation,lift_setEq StateLift.address same,frontier_setEq profile same]

theorem value_setEq (profile : Profile) (path : List String) {A B : List Act} (same : SetEq A B) :
    value profile path A = value profile path B := by
  simp only [value,thread_setEq profile same,observation_setEq profile same]

/-- Independent typed native context reader: diagnostic precedence is handled
by the verified witness normalizer; value availability and tags follow paths. -/
noncomputable def nativeRead (profile : Profile) (path : List String) (A : List Act) :
    StateObservationPlan.Observation Value :=
  let fault := if needsThread path then
    StateContextEvidence.nativeRead (evidenceInput profile) (observesOpener path) A else none
  match fault with
  | some evidence => .fault evidence
  | none => .data (optionalData (stablePath path) (value profile path A))

/-- The concrete metadata factory refines the native reader on the actual
accepted history, not merely on a selected representative. -/
theorem concrete_context_read_refinement (profile : Profile) (path : List String) (A : List Act) :
    sourceRead (source profile path) A = nativeRead profile path A := by
  have values := value_setEq profile path (StateInstalledLegacy.history_setEq A)
  unfold source nativeRead
  simp only [sourceRead,values]
  have errors : (errorSpec profile path).read A =
      (if needsThread path then StateContextEvidence.nativeRead (evidenceInput profile) (observesOpener path) A else none) := by
    unfold errorSpec
    split
    · exact (StateContextEvidence.native_context_witness_refinement _ _ _).symm
    · rfl
  rw [errors]
  cases current : (if needsThread path then StateContextEvidence.nativeRead (evidenceInput profile) (observesOpener path) A else none) <;> rfl

/-- Only the closed sealed-roster path gets a membership read strategy. -/
theorem roster_query_only (path : List String) (policy : StateInstalledLowering.NativeRead Value)
    (accepted : queryPolicy path = some policy) : ∃ role, path = ["thread","roles",role] := by
  unfold queryPolicy at accepted
  split at accepted
  · exact ⟨_,rfl⟩
  · contradiction

end CBCL.StateInstalledContext
