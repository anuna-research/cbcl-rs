import LeanCbcl.CheckpointSummary

/-!
Typed evidence projections for checkpoint continuation. Retained facts contain
IDs and selected verifier metadata, never `Act` or an application-body archive.
The projection and accepted-identity update equations are proved here. Native
admission, cryptographic identity binding, extraction from wire messages and the
resource verifier remain explicit boundaries. Fact tables may grow with history;
there is no constant-space claim and object endorsement quorum grants no resource
authority. Native legacy collective/quorum resource faults remain classifier
outcomes, not locally invented finalization rules.
-/
namespace CBCL.CheckpointEvidence
open State CheckpointSummary StateKernelExtensions

/-- A retained identity and its selected typed metadata; no hidden source act. -/
structure Fact (α : Type) where
  /-- Accepted native identity; cryptographic binding is supplied at admission. -/
  id : Nat
  /-- Only the selected typed metadata for this retained identity. -/
  data : α
  deriving DecidableEq

/-- Extract only the fields needed by this profile from each accepted act. -/
def project (extract : Act → α) (H : List Act) : List (Fact α) :=
  H.map fun a => ⟨a.addr, extract a⟩

/-- First binding, matching the immutable accepted-store identity discipline. -/
def materialize : List (Fact α) → Nat → Option α
  | [], _ => none
  | f :: fs, id => if f.id = id then some f.data else materialize fs id

/-- Reference ID query on source history; used only in specifications/proofs. -/
def referenceStore (extract : Act → α) : List Act → Nat → Option α
  | [], _ => none
  | a :: H, id => if a.addr = id then some (extract a) else referenceStore extract H id

theorem materialize_project (extract : Act → α) (H : List Act) :
    materialize (project extract H) = referenceStore extract H := by
  funext id
  induction H with
  | nil => rfl
  | cons a H ih =>
    change (if a.addr = id then some (extract a) else materialize (project extract H) id) =
      (if a.addr = id then some (extract a) else referenceStore extract H id)
    rw [ih]

/-- Authenticated accepted-identity membership, not a semantic verdict. -/
def present (fs : List (Fact α)) (id : Nat) : Bool := fs.any (fun f => f.id == id)

@[simp] theorem present_project (extract : Act → α) (H : List Act) (id : Nat) :
    present (project extract H) id = covered H id := by
  simp [present, project, covered, List.any_map, Function.comp_def]

/-- Incoming facts are projected only after native admission; duplicates do not
replace an established binding. Conflicting identity payloads must be rejected
at that admission boundary, not legitimized by this duplicate guard. -/
def step (fs : List (Fact α)) (f : Fact α) : List (Fact α) :=
  if present fs f.id then fs else f :: fs

/-- Apply an ordered finite tail of selected facts with identity deduplication. -/
def advance (fs tail : List (Fact α)) : List (Fact α) := tail.foldl step fs

/-- Build a selected-fact checkpoint from genesis using the concrete update. -/
def checkpoint (extract : Act → α) (H : List Act) : List (Fact α) :=
  advance [] (project extract H)

theorem materialize_step_fresh (fs : List (Fact α)) (f : Fact α)
    (fresh : present fs f.id = false) (id : Nat) :
    materialize (step fs f) id = if f.id = id then some f.data else materialize fs id := by
  simp [step, fresh, materialize]

theorem step_duplicate (fs : List (Fact α)) (f : Fact α)
    (duplicate : present fs f.id = true) : step fs f = fs := by
  simp [step, duplicate]

/-- Exact projection commutes with one actual accepted-store update. -/
theorem project_ingest (extract : Act → α) (H : List Act) (a : Act) :
    step (project extract H) ⟨a.addr, extract a⟩ = project extract (ingest H a) := by
  simp only [step, present_project, ingest]
  split <;> simp_all [project]

/-- Exact tail equation; no continuation-correctness premise is assumed. -/
theorem project_replay (extract : Act → α) (H D : List Act) :
    advance (project extract H) (project extract D) = project extract (replay H D) := by
  induction D generalizing H with
  | nil => rfl
  | cons a D ih =>
    change advance (step (project extract H) ⟨a.addr, extract a⟩) (project extract D) = _
    rw [project_ingest]
    exact ih (ingest H a)

theorem checkpoint_project (extract : Act → α) (H : List Act) :
    checkpoint extract H = project extract (normalize H) :=
  project_replay extract [] H

theorem checkpoint_tail (extract : Act → α) (H D : List Act) :
    advance (checkpoint extract H) (project extract D) = project extract (normalize (H ++ D)) := by
  rw [checkpoint_project, project_replay, normalize_append]

theorem materialize_checkpoint_tail (extract : Act → α) (H D : List Act) :
    materialize (advance (checkpoint extract H) (project extract D)) =
      referenceStore extract (normalize (H ++ D)) := by
  rw [checkpoint_tail, materialize_project]

@[simp] theorem project_ids (extract : Act → α) (H : List Act) :
    (project extract H).map Fact.id = H.map Act.addr := by
  simp [project, List.map_map, Function.comp_def]

/-- Evidence is only thread, wire verb and causal predecessor, plus its ID. -/
abbrev ProtocolFact := Fact Repeat.Evidence

theorem resolve_checkpoint_tail (extract : Act → Repeat.Evidence) (H D : List Act)
    (fuel thread : Nat) (verb : String) (limit id : Nat) :
    Repeat.resolve fuel (materialize (advance (checkpoint extract H) (project extract D)))
      thread verb limit id =
    Repeat.resolve fuel (referenceStore extract (normalize (H ++ D))) thread verb limit id := by
  rw [materialize_checkpoint_tail]

/-- Every observation resolves against the current materialized evidence. A
cached maximum is insufficient: a tail may resolve a previously missing parent. -/
def progress (fs : List ProtocolFact) (thread : Nat) (verb : String) (limit : Nat) : Nat :=
  StateProgress.progress (materialize fs) thread verb limit (fs.map Fact.id)

theorem progress_factorization (extract : Act → Repeat.Evidence) (H : List Act)
    (thread : Nat) (verb : String) (limit : Nat) :
    progress (project extract H) thread verb limit =
      protocolProgress (referenceStore extract H) thread verb limit H := by
  simp [progress, materialize_project, protocolProgress]

theorem progress_checkpoint_tail (extract : Act → Repeat.Evidence) (H D : List Act)
    (thread : Nat) (verb : String) (limit : Nat) :
    progress (advance (checkpoint extract H) (project extract D)) thread verb limit =
      protocolProgress (referenceStore extract (normalize (H ++ D)))
        thread verb limit (normalize (H ++ D)) := by
  rw [checkpoint_tail, progress_factorization]

/-- Direct endpoint in the unchanged native expression evaluator. -/
theorem progress_native (extract : Act → Repeat.Evidence) (H : List Act)
    (input : StateKernel.Input) (domains : List StateKernelSemantics.Domain) (verb : String) :
    StateKernel.evaluate {input with acts := H, causal := referenceStore extract H} domains
      (.progress verb) =
    .integer (Int.ofNat (progress (project extract H) input.thread verb (input.limit verb))) := by
  rw [progress_factorization]
  rfl

theorem progress_checkpoint_tail_native (extract : Act → Repeat.Evidence) (H D : List Act)
    (input : StateKernel.Input) (domains : List StateKernelSemantics.Domain) (verb : String) :
    StateKernel.Observation.integer (Int.ofNat
      (progress (advance (checkpoint extract H) (project extract D))
        input.thread verb (input.limit verb))) =
    StateKernel.evaluate {input with acts := normalize (H ++ D), causal := referenceStore extract (normalize (H ++ D))} domains (.progress verb) := by
  rw [checkpoint_tail]
  exact (progress_native extract (normalize (H ++ D)) input domains verb).symm

/-- Resource act categories are selected metadata, not new authority rules. -/
inductive ResourceKind where
  | castRoot | initialize | increment | decrement | transfer | transferHeadroom
  | checkpoint | endorsement | other
  deriving DecidableEq

/-- Opaque native identity/structural commitment, using the same abstract Nat
representation as accepted IDs. Its wire/cryptographic binding is a boundary. -/
abbrev ResourceDigest := Nat
/-- Account/amount associations preserving order, duplicates and invalid amounts for native checks. -/
abbrev ResourceAccounts := List (String × Int)

/-- Retain association order and duplicates for the native allocation/cast
checks, rather than silently normalizing malformed input into a valid map. -/
structure ResourceRoleBinding where
  /-- Authenticated cast role name interpreted under the pinned native configuration. -/
  role : String
  /-- Cast accounts for this role, retaining native association ordering. -/
  accounts : List String
  deriving DecidableEq

/-- Recognized malformed-field categories retained for the native classifier. -/
inductive ResourceProjectionError where
  | wrongType | malformedBinding | malformedRole | malformedAccount | malformedAssociation
  deriving DecidableEq

/-- Absence, malformed syntax, and a recognized typed field are distinct native
verifier inputs. Invalid syntax cannot become absence or a default amount. -/
inductive ResourceField (α : Type) where
  | absent
  | malformed (reason : ResourceProjectionError)
  | value (data : α)
  deriving DecidableEq

/-- Distinguish a missing, malformed or successfully recognized selected scalar field. -/
inductive ResourceFieldStatus where
  | absent | malformed | recognized
  deriving DecidableEq

/-- Native per-account or collective resource ownership mode. -/
inductive ResourceOwnership where
  | account | collective
  deriving DecidableEq

/-- Native legacy mode or an explicitly pinned resource quorum policy identity. -/
inductive ResourceCertification where
  | legacy
  | quorum (policy : ResourceDigest)
  deriving DecidableEq

/-- Pinned native verb and selected field names for one resource operation. -/
structure ResourceOperation where
  /-- Native wire performative used by the configured resource classifier. -/
  verb : String
  /-- Configured native keyword naming this operation amount. -/
  amountKey : String
  /-- Configured recipient keyword for transfers, absent for unary operations. -/
  recipientKey : Option String := none
  deriving DecidableEq

/-- Installed CounterRule metadata is fixed classifier context, not reconstructed
from an object certificate or inferred from an endorsed drawing snapshot. -/
structure ResourceConfig where
  /-- Pinned native ownership mode; object certificates cannot replace it. -/
  ownership : ResourceOwnership
  /-- Pinned resource-certification mode, separate from object endorsement quorum. -/
  certification : ResourceCertification
  /-- Configured or selected lower bound; not a proof of available resource rights. -/
  floor : Int
  /-- Configured or selected optional upper bound. -/
  ceiling : Option Int
  /-- Pinned opener verb used by native resource classification. -/
  initialVerb : String
  /-- Opener keyword containing the initial account rights associations. -/
  initialKey : String
  /-- Optional opener keyword containing initial headroom associations. -/
  headroomKey : Option String
  /-- Cast role whose authenticated occupants may issue increments. -/
  issuerRole : String
  /-- Pinned increment verb and amount-field selector. -/
  increment : ResourceOperation
  /-- Pinned decrement verb and amount-field selector. -/
  decrement : ResourceOperation
  /-- Optional pinned transfer operation, including recipient and amount selectors. -/
  transfer : Option ResourceOperation
  /-- Optional pinned headroom-transfer operation; requires a configured ceiling. -/
  transferHeadroom : Option ResourceOperation
  deriving DecidableEq

/-- Selected resource-verifier footprint, not arbitrary keyword data. Full
causal predecessors are separate from escrow-prev/deps. Binding and allocation
lists retain data required by native observe_facts, including headroom checks.
Language/thread/from and structural commitments retain its instance/duplicate
checks. Typed recognition/commitment fidelity is an explicit extraction boundary.
The native classifier does not read escrow-nonce; the Simple commitment covers
that identity distinction without retaining the nonce or complete source body. -/
structure ResourceSelected where
  /-- Resource instance/configuration name within the pinned target context. -/
  resource : String
  /-- Selected resource account, when this profile supplies one. -/
  owner : Option String := none
  /-- Recognized transfer recipient, interpreted with recipientStatus. -/
  recipient : Option String := none
  /-- Configured or selected lower bound; not a proof of available resource rights. -/
  floor : Option Int := none
  /-- Configured or selected optional upper bound. -/
  ceiling : Option Int := none
  /-- Selected configuration epoch, when present in the pinned profile. -/
  epoch : Option Nat := none
  /-- Native wire performative used by the configured resource classifier. -/
  verb : String := ""
  /-- All authenticated causal predecessors, distinct from escrow previous/dependency links. -/
  predecessors : List Nat := []
  /-- Pinned native language identity used to reject foreign resource instances. -/
  language : Option String := none
  /-- Native thread identity under the same abstract ID encoding as protocol evidence. -/
  thread : Option Nat := none
  /-- Recognized native from field, preserving absence and malformed syntax. -/
  authenticatedFrom : ResourceField String := .absent
  /-- Authenticated role/account bindings required by native opener/cast checks. -/
  bindings : ResourceField (List ResourceRoleBinding) := .absent
  /-- Typed initial rights associations, preserving absent or malformed fields. -/
  initialAllocations : ResourceField ResourceAccounts := .absent
  /-- Typed initial headroom associations used for ceiling conservation checks. -/
  headroomAllocations : ResourceField ResourceAccounts := .absent
  /-- Recognition status of the amount stored in ResourceData.amount. -/
  amountStatus : ResourceFieldStatus := .absent
  /-- Recognition status of the escrow previous link stored in ResourceData.prev. -/
  previousStatus : ResourceFieldStatus := .absent
  /-- Recognition status of the escrow dependency list stored in ResourceData.deps. -/
  dependenciesStatus : ResourceFieldStatus := .absent
  /-- Recognition status of the selected transfer recipient. -/
  recipientStatus : ResourceFieldStatus := .absent
  /-- Commitment to the original native Simple structure, without retaining its body. -/
  identity : ResourceDigest := 0
  /-- Optional structural cast commitment for native duplicate consistency checks. -/
  castIdentity : Option ResourceDigest := none
  deriving DecidableEq

/-- Minimal verifier record under an ID. Native extraction must recognize these
fields and authenticate signer/edges; this structure cannot smuggle an Act. -/
structure ResourceData where
  /-- Authenticated resource act signer from native admission. -/
  signer : String
  /-- Selected operation category; it confers no independent resource authority. -/
  kind : ResourceKind
  /-- Selected integer amount, interpreted with amountStatus and native range checks. -/
  amount : Int
  /-- Selected escrow previous identity, distinct from causal predecessors. -/
  prev : Option Nat
  /-- Selected escrow dependency identities, preserving order and duplicates. -/
  deps : List Nat
  /-- Additional typed fields actually read by the native resource verifier. -/
  selected : ResourceSelected
  deriving DecidableEq

/-- A native accepted identity paired with selected resource metadata, never a full Act. -/
abbrev ResourceFact := Fact ResourceData

/-- Set-extensional equality of complete typed facts, ignoring enumeration and multiplicity. -/
def FactSetEq (xs ys : List (Fact α)) : Prop := ∀ f, f ∈ xs ↔ f ∈ ys

theorem project_setEq (extract : Act → α) {H K : List Act} (same : SetEq H K) :
    FactSetEq (project extract H) (project extract K) := by
  intro f
  simp only [project, List.mem_map]
  constructor
  · rintro ⟨a, ha, eq⟩; exact ⟨a, (same a).mp ha, eq⟩
  · rintro ⟨a, ha, eq⟩; exact ⟨a, (same a).mpr ha, eq⟩

/-- Native verifier port: the SAME classifier is used for reference history and
checkpoint facts. Set extensionality is the SEC-style verifier obligation,
not an assumed checkpoint continuation law or a claim of resource finality. -/
structure ResourcePort where
  /-- Native recognized metadata projection; wire/cryptographic fidelity remains a boundary. -/
  extract : Act → ResourceData
  /-- Shared native resource verifier port used by reference and checkpoint observations. -/
  classify : List ResourceFact → String → ResourceInput
  classify_ext : ∀ xs ys, FactSetEq xs ys → classify xs = classify ys

/-- Instantiate a port with explicit pinned native configurations. This helper
does not assert that a classifier implements Rust: that remains the native
verifier boundary. In particular legacy collective/quorum fault behavior must
be retained; an object endorsement threshold is not resource authority. -/
def ResourcePort.fromClassifier
    (configuration : String → ResourceConfig) (extract : Act → ResourceData)
    (classify : ResourceConfig → List ResourceFact → ResourceInput)
    (extensional : ∀ config xs ys, FactSetEq xs ys → classify config xs = classify config ys) :
    ResourcePort where
  extract := extract
  classify := fun fs name => classify (configuration name) fs
  classify_ext := by
    intro xs ys same
    funext name
    exact extensional (configuration name) xs ys same

/-- Reference native classifier input obtained from selected history facts. -/
def ResourcePort.resourceInput (port : ResourcePort) (H : List Act) : String → ResourceInput :=
  port.classify (project port.extract H)

/-- Invoke the same native classifier on retained facts and preserve its tagged observation. -/
def ResourcePort.observe (port : ResourcePort) (fs : List ResourceFact) (name : String) : ResourceView :=
  resourceObserve (port.classify fs name)

theorem resource_materialization (port : ResourcePort) (H D : List Act) :
    materialize (advance (checkpoint port.extract H) (project port.extract D)) =
      referenceStore port.extract (normalize (H ++ D)) :=
  materialize_checkpoint_tail port.extract H D

theorem resourceInput_checkpoint_tail (port : ResourcePort) (H D : List Act) :
    port.classify (advance (checkpoint port.extract H) (project port.extract D)) =
      port.resourceInput (normalize (H ++ D)) := by
  rw [checkpoint_tail]
  rfl

theorem resource_checkpoint_tail (port : ResourcePort) (H D : List Act) (name : String) :
    port.observe (advance (checkpoint port.extract H) (project port.extract D)) name =
      resourceObserve (port.resourceInput (normalize (H ++ D)) name) := by
  rw [checkpoint_tail]
  rfl

/-- The native SEC resource port's set-extensionality follows from the fact
projection and classifier extensionality, independently of continuation. -/
theorem resourceInput_setEq (port : ResourcePort) {H K : List Act} (same : SetEq H K) :
    port.resourceInput H = port.resourceInput K :=
  port.classify_ext _ _ (project_setEq port.extract same)

theorem resource_observe_setEq (port : ResourcePort) {xs ys : List ResourceFact}
    (same : FactSetEq xs ys) (name : String) : port.observe xs name = port.observe ys name := by
  unfold ResourcePort.observe
  rw [port.classify_ext xs ys same]

theorem resource_native (port : ResourcePort) (H : List Act) (input : StateKernel.Input)
    (domains : List StateKernelSemantics.Domain) (name : String) :
    StateKernel.evaluate {input with acts := H, resource := port.resourceInput H} domains (.bounded name) =
      .resource (port.observe (project port.extract H) name) := rfl

theorem resource_checkpoint_tail_native (port : ResourcePort) (H D : List Act)
    (input : StateKernel.Input) (domains : List StateKernelSemantics.Domain) (name : String) :
    StateKernel.Observation.resource
      (port.observe (advance (checkpoint port.extract H) (project port.extract D)) name) =
    StateKernel.evaluate {input with acts := normalize (H ++ D), resource := port.resourceInput (normalize (H ++ D))} domains (.bounded name) := by
  rw [checkpoint_tail]
  exact (resource_native port (normalize (H ++ D)) input domains name).symm

end CBCL.CheckpointEvidence
