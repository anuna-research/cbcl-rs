import LeanCbcl.ConsensusFree.Collective

/-! SPEC-028. Explicit actor requests and durable receipt provenance over the
single-pool engine. Signatures are an ideal relation on complete typed payloads;
no crypto, codec, physical journal or Rust-extraction theorem is assumed. -/
namespace CBCL.ConsensusFree.CollectiveActors
open CBCL.ValidatorBudget

/-- Actor signing identities plus the deliberately unauthenticated pool identity. -/
inductive Identity (K : Nat) where
  | actor (id : Fin K)
  | pool
  deriving DecidableEq, Repr

/-- Application request phases bound into authenticated packets. -/
inductive Payload (T P : Nat) where
  | genesis
  | operation (tx : Fin T)
  | cancellation (tx : Fin T)
  | checkpoint (p : Fin P)
  deriving DecidableEq, Repr

/-- Instance-scoped request with an explicit signing identity. -/
structure Packet (K T P : Nat) where
  /-- Instance domain included in authenticated requests. -/
  domain : Nat
  /-- Identity claimed by the packet signer. -/
  signer : Identity K
  /-- Complete application request carried by the packet. -/
  payload : Payload T P
  deriving DecidableEq, Repr

-- Lean generates a precedence parameter that these record printers do not use.
attribute [nolint unusedArguments] instReprPacket.repr

/-- Cast membership and roles controlling collective requests. -/
structure Policy (K L : Nat) where
  /-- Whether an actor belongs to the protocol cast. -/
  cast : Fin K → Bool
  /-- Roles assigned to each actor. -/
  role : Fin K → Fin L → Bool
  /-- Role permitted to open the counter instance. -/
  initializer : Fin L
  /-- Role permitted to request increments. -/
  increment : Fin L
  /-- Role permitted to request decrements. -/
  decrement : Fin L
  /-- Optional role required for minting rights. -/
  issuer : Option (Fin L)

/-- Require both cast membership and the requested role. -/
def Policy.admitted (p : Policy K L) (a : Fin K) (r : Fin L) := p.cast a && p.role a r

/-- Check the configured issuer role; no issuer role admits nobody. -/
def Policy.issues (p : Policy K L) (a : Fin K) : Bool :=
  match p.issuer with | none => false | some r => p.admitted a r

/-- Allow cast members with increment or decrement roles to propose checkpoints. -/
def Policy.checkpoints (p : Policy K L) (a : Fin K) : Bool :=
  p.cast a && (p.role a p.increment || p.role a p.decrement)

/-- Single-pool checkpoint books before application authorization is attached. -/
structure Manifest (T P : Nat) where
  /-- Immediate predecessor epoch of the checkpoint. -/
  parent : Epoch 1 P
  /-- Depth of an epoch in this configuration. -/
  depth : Nat
  /-- Operations whose debits are included in the manifest. -/
  held : Fin T → Bool
  /-- Held operations whose cancellation restores their debit. -/
  refunded : Fin T → Bool
  /-- Final operations whose credits are included in the manifest. -/
  credited : Fin T → Bool
  /-- Available resource vector after applying the manifest books. -/
  allocation : Fin 2 → Nat

/-- Instance domain, roles, authenticated actors and immutable request catalogue. -/
structure Context (K L T P : Nat) where
  /-- Instance domain included in authenticated requests. -/
  domain : Nat
  /-- Application admission policy for the instance. -/
  policy : Policy K L
  /-- Ideal verified signatures bind key, instance, phase and complete payload ID. -/
  authenticated : Fin K → Nat → Payload T P → Bool
  /-- Actor designated to open the instance. -/
  opener : Fin K
  /-- Lower bound of the counter value. -/
  floor : Int
  /-- Optional upper bound of the counter value. -/
  ceiling : Option Int
  /-- Rights allocated at genesis above the counter floor. -/
  initialRights : Nat
  /-- Catalogue of proposed checkpoint bodies. -/
  manifests : Fin P → Manifest T P
  /-- Source epoch for each operation. -/
  epoch : Fin T → Epoch 1 P
  /-- Actor requesting each operation. -/
  actor : Fin T → Fin K
  /-- Whether an operation increments rather than decrements the counter. -/
  isMint : Fin T → Bool
  /-- Nonnegative amount carried by an operation. -/
  amount : Fin T → Nat

/-- Construct the instance-scoped packet for an actor and payload. -/
def canonical (c : Context K L T P) (body : Payload T P) (a : Fin K) : Packet K T P :=
  ⟨c.domain, .actor a, body⟩

/-- Initial capacity below the ceiling, or zero for an uncapped counter. -/
def headroom (c : Context K L T P) : Nat :=
  match c.ceiling with | none => 0 | some cap => (cap - c.floor - c.initialRights).toNat

/-- Check that the initial counter value does not exceed the ceiling. -/
def genesisBounds (c : Context K L T P) : Bool :=
  match c.ceiling with | none => true | some cap => decide (c.floor + c.initialRights ≤ cap)

/-- Select the increment or decrement role for an operation. -/
def roleFor (c : Context K L T P) (tx : Fin T) : Fin L :=
  if c.isMint tx then c.policy.increment else c.policy.decrement

/-- Check actor authentication, admission, positive amount and mint authority. -/
def operationAuthorized (c : Context K L T P) (tx : Fin T) : Bool :=
  c.authenticated (c.actor tx) c.domain (.operation tx) &&
  c.policy.admitted (c.actor tx) (roleFor c tx) && decide (0 < c.amount tx) &&
  (if c.isMint tx then c.policy.issues (c.actor tx) else true)

/-- Verify a packet's domain, actor signature and phase-specific admission. -/
def verify (c : Context K L T P) (packet : Packet K T P) : Bool :=
  match packet.signer with
  | .pool => false
  | .actor a =>
    decide (packet.domain = c.domain) && c.authenticated a packet.domain packet.payload &&
    match packet.payload with
    | .genesis => decide (a = c.opener) && c.policy.admitted a c.policy.initializer && genesisBounds c
    | .operation tx => decide (a = c.actor tx) && operationAuthorized c tx
    | .cancellation tx => decide (a = c.actor tx)
    | .checkpoint _ => c.policy.checkpoints a

/-- Whether an eligible actor authenticates the checkpoint request. -/
def checkpointAuthorized (c : Context K L T P) (p : Fin P) : Bool :=
  (List.finRange K).any (fun a => verify c (canonical c (.checkpoint p) a))

/-- Attach verified application authorization to a checkpoint body. -/
def checkpoint (c : Context K L T P) (p : Fin P) : Checkpoint 1 T P 2 where
  owner := 0
  parent := (c.manifests p).parent
  depth := (c.manifests p).depth
  held := (c.manifests p).held
  refunded := (c.manifests p).refunded
  credited := (c.manifests p).credited
  allocation := (c.manifests p).allocation
  authorized := checkpointAuthorized c p

/-- Translate authenticated collective requests into the business resource context. -/
def business (c : Context K L T P) : Collective.Context K T P where
  checkpoints := checkpoint c
  epoch := c.epoch
  actor := c.actor
  isMint := c.isMint
  amount := c.amount
  signatureValid := fun tx => c.authenticated (c.actor tx) c.domain (.operation tx)
  roleAdmitted := fun tx => c.policy.admitted (c.actor tx) (roleFor c tx)
  isIssuer := c.policy.issues
  initialRights := c.initialRights
  initialHeadroom := headroom c
  capped := c.ceiling.isSome

/-- Build the resource protocol configuration from the application context. -/
def config (c : Context K L T P) (committee : Committee f) := Collective.config (business c) committee

@[simp] theorem pool_rejected (c : Context K L T P) (i : Nat) (body : Payload T P) :
    verify c ⟨i, .pool, body⟩ = false := rfl

theorem wrong_instance_rejected (c : Context K L T P) (p : Packet K T P)
    (wrong : p.domain ≠ c.domain) : verify c p = false := by
  cases signer : p.signer <;> simp [verify, signer, wrong]

theorem wrong_cancel_actor_rejected (c : Context K L T P) (a : Fin K) (tx : Fin T)
    (wrong : a ≠ c.actor tx) : verify c (canonical c (.cancellation tx) a) = false := by
  simp [verify, canonical, wrong]

theorem cancel_verified (c : Context K L T P) (a : Fin K) (tx : Fin T)
    (h : verify c (canonical c (.cancellation tx) a) = true) :
    a = c.actor tx ∧ c.authenticated a c.domain (.cancellation tx) = true := by
  simp [verify, canonical] at h
  exact ⟨h.2, h.1⟩

theorem checkpoint_verified (c : Context K L T P) (a : Fin K) (p : Fin P)
    (h : verify c (canonical c (.checkpoint p) a) = true) :
    c.authenticated a c.domain (.checkpoint p) = true ∧ c.policy.cast a = true ∧
      (c.policy.role a c.policy.increment = true ∨ c.policy.role a c.policy.decrement = true) := by
  simpa [verify, canonical, Policy.checkpoints, Bool.and_eq_true_iff, Bool.or_eq_true_iff,
    and_assoc] using h

theorem checkpoint_authorized_iff (c : Context K L T P) (p : Fin P) :
    checkpointAuthorized c p = true ↔ ∃ a, verify c (canonical c (.checkpoint p) a) = true := by
  simp [checkpointAuthorized, List.any_eq_true]

theorem operation_authorized_eq (c : Context K L T P) (tx : Fin T) :
    (config c committee).authorized tx = operationAuthorized c tx := by
  cases mint : c.isMint tx <;>
    simp [config, Collective.config, Collective.currency, Currency.config, Currency.authorized,
      Collective.actorAuthorized, business, operationAuthorized, mint, Bool.and_assoc,
      Bool.and_comm, Bool.and_left_comm]

/-- Resource protocol state with genesis authentication and local request receipts. -/
structure State (K T P : Nat) where
  /-- Underlying resource-protocol state. -/
  core : CBCL.ConsensusFree.State 1 T P 2
  /-- Authenticated packet that opened this instance. -/
  genesis : Packet K T P
  /-- A bit identifies the full canonical request, retaining all eligible actors. -/
  receipts : Nat → Payload T P → Fin K → Bool

/-- Initialize protocol state and empty delivery receipts from the genesis packet. -/
def initialState (c : Context K L T P) (committee : Committee f) (genesis : Packet K T P) : State K T P where
  core := initial (config c committee)
  genesis := genesis
  receipts := fun _ _ _ => false

/-- Create state only for a verified genesis packet. -/
def admitGenesis (c : Context K L T P) (committee : Committee f) (packet : Packet K T P) : Option (State K T P) :=
  if packet.payload = .genesis ∧ verify c packet = true then some (initialState c committee packet) else none

/-- Record delivery of a canonical actor request to a validator. -/
def stamp (s : State K T P) (w : Nat) (body : Payload T P) (a : Fin K) : State K T P :=
  {s with receipts := two s.receipts w body (setAt (s.receipts w body) a true)}

/-- Whether a validator has received the operation actor's request. -/
def opReady (c : Context K L T P) (s : State K T P) (tx : Fin T) (w : Nat) :=
  s.receipts w (.operation tx) (c.actor tx)
/-- Whether a validator has received the operation actor's cancellation request. -/
def cancelReady (c : Context K L T P) (s : State K T P) (tx : Fin T) (w : Nat) :=
  s.receipts w (.cancellation tx) (c.actor tx)
/-- Whether a validator has received any actor's checkpoint request. -/
def checkpointReady (s : State K T P) (p : Fin P) (w : Nat) :=
  (List.finRange K).any (fun a => s.receipts w (.checkpoint p) a)

/-- Require authenticated request delivery before honest protocol actions. -/
def guard (c : Context K L T P) (committee : Committee f) (s : State K T P) : Command 1 T P → Bool
  | .sign tx w | .receiveOperation tx w | .receiveFinal tx w | .effect tx w =>
    if w ∈ committee.core then opReady c s tx w else true
  | .fence tx w => if w ∈ committee.core then opReady c s tx w && cancelReady c s tx w else true
  | .endorse p w | .record p w => if w ∈ committee.core then checkpointReady s p w else true
  | _ => true

/-- An asynchronous packet delivery or local protocol command. -/
inductive Event (K T P : Nat) where
  | deliver (validator : Nat) (packet : Packet K T P)
  | protocol (command : Command 1 T P)
  deriving DecidableEq, Repr

/-- Deliver an authenticated request or execute a guarded local protocol command. -/
def execute (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (event : Event K T P) : Option (Fin T) × State K T P :=
  match event with
  | .deliver w packet =>
    if Member (config c committee) w ∧ verify c packet = true then
      match packet.signer with
      | .actor a => (none, stamp s w packet.payload a)
      | .pool => (none, s)
    else (none, s)
  | .protocol command =>
    if guard c committee s command then
      let next := CBCL.ConsensusFree.execute (config c committee) s.core command
      (next.1, {s with core := next.2})
    else (none, s)

theorem execute_erases (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (event : Event K T P) :
    Step (config c committee) s.core (execute c committee s event).1 (execute c committee s event).2.core := by
  cases event with
  | deliver w packet =>
      simp only [execute]
      split
      · cases packet.signer <;> exact Step.replay _
      · exact Step.replay _
  | protocol command =>
      simp only [execute]
      split
      · exact execute_sound (config c committee) s.core command
      · exact Step.replay _

/-- Replay asynchronous events in order, collecting finalization labels. -/
def run (c : Context K L T P) (committee : Committee f) (s : State K T P) :
    List (Event K T P) → List (Option (Fin T)) × State K T P
  | [] => ([],s)
  | e :: rest =>
    let next := execute c committee s e
    let tail := run c committee next.2 rest
    (next.1 :: tail.1, tail.2)

theorem run_erases (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (events : List (Event K T P)) :
    Trace (config c committee) s.core (run c committee s events).1 (run c committee s events).2.core := by
  induction events generalizing s with
  | nil => exact Trace.nil _
  | cons e rest ih => exact Trace.cons (execute_erases c committee s e) (ih _)

theorem funded_refinement (c : Context K L T P) (committee : Committee f) (genesis : Packet K T P)
    (events : List (Event K T P)) :
    BusinessRun (config c committee) (initial (config c committee)).balance
      ((run c committee (initialState c committee genesis) events).1.filterMap id)
      (run c committee (initialState c committee genesis) events).2.core.balance :=
  trace_simulation (initial_invariant _) (run_erases c committee (initialState c committee genesis) events)

theorem resources_nonnegative (c : Context K L T P) (committee : Committee f) (genesis : Packet K T P)
    (events : List (Event K T P)) :
    ∀ d, 0 ≤ (run c committee (initialState c committee genesis) events).2.core.balance d :=
  resource_nonnegative (trace_invariant (initial_invariant _) (run_erases c committee (initialState c committee genesis) events))


set_option linter.unusedSimpArgs false in
private theorem signature_frame_perform (cfg : Config 1 T P 2 f)
    (s t : CBCL.ConsensusFree.State 1 T P 2) (cmd : Command 1 T P) (tx : Fin T) (w : Nat)
    (result : perform cfg s cmd = some (label,t)) (h : t.signatures tx w = true) :
    s.signatures tx w = true ∨ cmd = .sign tx w := by
  cases cmd <;> simp only [perform] at result
  all_goals simp_all [signed, freeze, release, endorse, record, install, receiveOperation,
    receiveFinal, effect, emit, fence, two, setAt]
  all_goals repeat' first
    | (rcases result with ⟨_,result⟩)
    | (subst t <;> simp_all [signed, freeze, release, endorse, record, install,
        receiveOperation, receiveFinal, effect, emit, fence, two, setAt])
    | (split at result <;> simp_all [signed, freeze, release, endorse, record, install,
        receiveOperation, receiveFinal, effect, emit, fence, two, setAt])
    | (split at h <;> simp_all [two, setAt])
  all_goals simp_all [signed, freeze, release, endorse, record, install, receiveOperation,
    receiveFinal, effect, emit, fence, two, setAt]
  all_goals repeat' (split at h <;> simp_all [two, setAt])
  all_goals exact h.elim (fun eq => Or.inr eq.symm) Or.inl

private theorem signature_frame (cfg : Config 1 T P 2 f)
    (s : CBCL.ConsensusFree.State 1 T P 2) (cmd : Command 1 T P) (tx : Fin T) (w : Nat)
    (h : (CBCL.ConsensusFree.execute cfg s cmd).2.signatures tx w = true) :
    s.signatures tx w = true ∨ cmd = .sign tx w := by
  cases result : perform cfg s cmd with
  | none => exact Or.inl (by simpa [CBCL.ConsensusFree.execute,result] using h)
  | some pair =>
      exact signature_frame_perform cfg s pair.2 cmd tx w result
        (by simpa [CBCL.ConsensusFree.execute,result] using h)

set_option linter.unusedSimpArgs false in
private theorem fence_frame_perform (cfg : Config 1 T P 2 f)
    (s t : CBCL.ConsensusFree.State 1 T P 2) (cmd : Command 1 T P) (tx : Fin T) (w : Nat)
    (result : perform cfg s cmd = some (label,t)) (h : t.fences tx w = true) :
    s.fences tx w = true ∨ cmd = .fence tx w := by
  cases cmd <;> simp only [perform] at result
  all_goals simp_all [signed, freeze, release, endorse, record, install, receiveOperation,
    receiveFinal, effect, emit, fence, two, setAt]
  all_goals repeat' first
    | (rcases result with ⟨_,result⟩)
    | (subst t <;> simp_all [signed, freeze, release, endorse, record, install,
        receiveOperation, receiveFinal, effect, emit, fence, two, setAt])
    | (split at result <;> simp_all [signed, freeze, release, endorse, record, install,
        receiveOperation, receiveFinal, effect, emit, fence, two, setAt])
    | (split at h <;> simp_all [two, setAt])
  all_goals simp_all [signed, freeze, release, endorse, record, install, receiveOperation,
    receiveFinal, effect, emit, fence, two, setAt]
  all_goals repeat' (split at h <;> simp_all [two, setAt])
  all_goals exact h.elim (fun eq => Or.inr eq.symm) Or.inl

private theorem fence_frame (cfg : Config 1 T P 2 f)
    (s : CBCL.ConsensusFree.State 1 T P 2) (cmd : Command 1 T P) (tx : Fin T) (w : Nat)
    (h : (CBCL.ConsensusFree.execute cfg s cmd).2.fences tx w = true) :
    s.fences tx w = true ∨ cmd = .fence tx w := by
  cases result : perform cfg s cmd with
  | none => exact Or.inl (by simpa [CBCL.ConsensusFree.execute,result] using h)
  | some pair =>
      exact fence_frame_perform cfg s pair.2 cmd tx w result
        (by simpa [CBCL.ConsensusFree.execute,result] using h)

set_option linter.unusedSimpArgs false in
private theorem vote_frame_perform (cfg : Config 1 T P 2 f)
    (s t : CBCL.ConsensusFree.State 1 T P 2) (cmd : Command 1 T P) (p : Fin P) (w : Nat)
    (result : perform cfg s cmd = some (label,t)) (h : t.votes p w = true) :
    s.votes p w = true ∨ cmd = .endorse p w := by
  cases cmd <;> simp only [perform] at result
  all_goals simp_all [signed, freeze, release, endorse, record, install, receiveOperation,
    receiveFinal, effect, emit, fence, two, setAt]
  all_goals repeat' first
    | (rcases result with ⟨_,result⟩)
    | (subst t <;> simp_all [signed, freeze, release, endorse, record, install,
        receiveOperation, receiveFinal, effect, emit, fence, two, setAt])
    | (split at result <;> simp_all [signed, freeze, release, endorse, record, install,
        receiveOperation, receiveFinal, effect, emit, fence, two, setAt])
    | (split at h <;> simp_all [two, setAt])
  all_goals simp_all [signed, freeze, release, endorse, record, install, receiveOperation,
    receiveFinal, effect, emit, fence, two, setAt]
  all_goals repeat' (split at h <;> simp_all [two, setAt])
  all_goals exact h.elim (fun eq => Or.inr eq.symm) Or.inl

private theorem vote_frame (cfg : Config 1 T P 2 f)
    (s : CBCL.ConsensusFree.State 1 T P 2) (cmd : Command 1 T P) (p : Fin P) (w : Nat)
    (h : (CBCL.ConsensusFree.execute cfg s cmd).2.votes p w = true) :
    s.votes p w = true ∨ cmd = .endorse p w := by
  cases result : perform cfg s cmd with
  | none => exact Or.inl (by simpa [CBCL.ConsensusFree.execute,result] using h)
  | some pair =>
      exact vote_frame_perform cfg s pair.2 cmd p w result
        (by simpa [CBCL.ConsensusFree.execute,result] using h)

private theorem stamp_cases (s : State K T P) (w v : Nat) (body key : Payload T P) (a b : Fin K)
    (h : (stamp s w body a).receipts v key b = true) :
    s.receipts v key b = true ∨ (v = w ∧ key = body ∧ b = a) := by
  by_cases hw : v = w <;> by_cases hk : key = body <;> by_cases ha : b = a <;>
    simp_all [stamp, two, setAt]

private theorem stamp_mono (s : State K T P) (w v : Nat) (body key : Payload T P) (a b : Fin K)
    (h : s.receipts v key b = true) : (stamp s w body a).receipts v key b = true := by
  by_cases hw : v = w <;> by_cases hk : key = body <;> by_cases ha : b = a <;>
    simp_all [stamp, two, setAt]

/-- Genesis, receipt and honest-action authentication invariants. -/
structure ControlInvariant (c : Context K L T P) (committee : Committee f) (s : State K T P) : Prop where
  genesis : s.genesis.payload = .genesis ∧ verify c s.genesis = true
  receipts : ∀ w body a, s.receipts w body a = true → verify c (canonical c body a) = true
  signatures : ∀ tx w, w ∈ committee.core → s.core.signatures tx w = true → opReady c s tx w = true
  fences : ∀ tx w, w ∈ committee.core → s.core.fences tx w = true →
    opReady c s tx w = true ∧ cancelReady c s tx w = true
  votes : ∀ p w, w ∈ committee.core → s.core.votes p w = true → checkpointReady s p w = true

private theorem checkpoint_ready_mono (s t : State K T P)
    (mono : ∀ w body a, s.receipts w body a = true → t.receipts w body a = true)
    (p : Fin P) (w : Nat) (h : checkpointReady s p w = true) : checkpointReady t p w = true := by
  simp only [checkpointReady, List.any_eq_true] at h ⊢
  obtain ⟨a, mem, received⟩ := h
  exact ⟨a, mem, mono _ _ _ received⟩

private theorem verified_canonical (c : Context K L T P) (p : Packet K T P) (a : Fin K)
    (signer : p.signer = .actor a) (h : verify c p = true) :
    verify c (canonical c p.payload a) = true := by
  have same : p.domain = c.domain := by
    simp only [verify, signer, Bool.and_eq_true_iff, decide_eq_true_eq] at h
    exact h.1.1
  have equality : p = canonical c p.payload a := by
    cases p; simp_all [canonical]
  simpa [← equality] using h

theorem control_initial (c : Context K L T P) (committee : Committee f) (genesis : Packet K T P)
    (valid : genesis.payload = .genesis ∧ verify c genesis = true) :
    ControlInvariant c committee (initialState c committee genesis) := by
  refine ⟨valid, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [initialState, initial]

theorem control_step (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (event : Event K T P) (h : ControlInvariant c committee s) :
    ControlInvariant c committee (execute c committee s event).2 := by
  cases event with
  | deliver w packet =>
      simp only [execute]
      split
      next accepted =>
        cases signer : packet.signer with
        | pool => exact h
        | actor a =>
          refine ⟨h.genesis, ?_, ?_, ?_, ?_⟩
          · intro v body b received
            rcases stamp_cases s w v packet.payload body a b received with old | same
            · exact h.receipts _ _ _ old
            · rcases same with ⟨rfl,rfl,rfl⟩
              exact verified_canonical c packet _ signer accepted.2
          · intro tx v honest signed
            exact stamp_mono _ _ _ _ _ _ _ (h.signatures tx v honest signed)
          · intro tx v honest fenced
            have old := h.fences tx v honest fenced
            exact ⟨stamp_mono _ _ _ _ _ _ _ old.1, stamp_mono _ _ _ _ _ _ _ old.2⟩
          · intro p v honest voted
            exact checkpoint_ready_mono _ _ (stamp_mono s w · packet.payload · a ·) p v (h.votes p v honest voted)
      next => exact h
  | protocol cmd =>
      simp only [execute]
      split
      next allowed =>
        refine ⟨h.genesis, h.receipts, ?_, ?_, ?_⟩
        · intro tx w honest signed
          rcases signature_frame _ _ cmd tx w signed with old | same
          · exact h.signatures tx w honest old
          · subst cmd; simpa [guard, honest] using allowed
        · intro tx w honest fenced
          rcases fence_frame _ _ cmd tx w fenced with old | same
          · exact h.fences tx w honest old
          · subst cmd
            have pair : opReady c s tx w = true ∧ cancelReady c s tx w = true := by simpa [guard, honest] using allowed
            exact pair
        · intro p w honest voted
          rcases vote_frame _ _ cmd p w voted with old | same
          · exact h.votes p w honest old
          · subst cmd; simpa [guard, honest] using allowed
      next => exact h

theorem control_run (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (events : List (Event K T P)) (h : ControlInvariant c committee s) :
    ControlInvariant c committee (run c committee s events).2 := by
  induction events generalizing s with
  | nil => exact h
  | cons e rest ih => exact ih _ (control_step c committee s e h)


theorem honest_fence_has_original_request (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (h : ControlInvariant c committee s) (tx : Fin T) (w : Nat)
    (honest : w ∈ committee.core) (fenced : s.core.fences tx w = true) :
    s.receipts w (.cancellation tx) (c.actor tx) = true ∧
    c.authenticated (c.actor tx) c.domain (.cancellation tx) = true := by
  have received := (h.fences tx w honest fenced).2
  exact ⟨received, (cancel_verified c _ tx (h.receipts w _ _ received)).2⟩

theorem cancel_quorum_has_original_request (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (h : ControlInvariant c committee s) (tx : Fin T)
    (certificate : cancelCert (config c committee) s.core tx = true) :
    ∃ w ∈ committee.core, s.receipts w (.cancellation tx) (c.actor tx) = true ∧
      c.authenticated (c.actor tx) c.domain (.cancellation tx) = true := by
  obtain ⟨w, honest, voted⟩ := quorum_has_core (config c committee) _ certificate
  exact ⟨w, honest, honest_fence_has_original_request c committee s h tx w honest voted⟩

theorem honest_checkpoint_has_eligible_request (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (h : ControlInvariant c committee s) (p : Fin P) (w : Nat)
    (honest : w ∈ committee.core) (voted : s.core.votes p w = true) :
    ∃ a, s.receipts w (.checkpoint p) a = true ∧
      c.authenticated a c.domain (.checkpoint p) = true ∧ c.policy.cast a = true ∧
      (c.policy.role a c.policy.increment = true ∨ c.policy.role a c.policy.decrement = true) := by
  have ready := h.votes p w honest voted
  simp only [checkpointReady, List.any_eq_true] at ready
  obtain ⟨a, _, received⟩ := ready
  exact ⟨a, received, checkpoint_verified c a p (h.receipts w _ _ received)⟩

theorem checkpoint_quorum_has_eligible_request (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (h : ControlInvariant c committee s) (p : Fin P)
    (certificate : checkpointCert (config c committee) s.core p = true) :
    ∃ w ∈ committee.core, ∃ a, s.receipts w (.checkpoint p) a = true ∧
      c.authenticated a c.domain (.checkpoint p) = true ∧ c.policy.cast a = true ∧
      (c.policy.role a c.policy.increment = true ∨ c.policy.role a c.policy.decrement = true) := by
  obtain ⟨w, honest, voted⟩ := quorum_has_core (config c committee) _ certificate
  exact ⟨w, honest, honest_checkpoint_has_eligible_request c committee s h p w honest voted⟩

theorem genesis_bounds_of_verified (c : Context K L T P) (packet : Packet K T P)
    (body : packet.payload = .genesis) (verified : verify c packet = true) : genesisBounds c = true := by
  cases signer : packet.signer with
  | pool => simp [verify, signer] at verified
  | actor a =>
      simp only [verify, signer, body, Bool.and_eq_true_iff] at verified
      exact verified.2.2

theorem declared_cap_bound (c : Context K L T P) (packet : Packet K T P)
    (valid : packet.payload = .genesis ∧ verify c packet = true) (cap : Int)
    (bounded : c.ceiling = some cap) :
    c.floor + (c.initialRights : Int) + (headroom c : Int) = cap := by
  have allowed := genesis_bounds_of_verified c packet valid.1 valid.2
  have bound : c.floor + (c.initialRights : Int) ≤ cap := by
    simpa [genesisBounds,bounded] using allowed
  have nonnegative : 0 ≤ cap - c.floor - (c.initialRights : Int) := by omega
  have cast := Int.toNat_of_nonneg nonnegative
  simp only [headroom,bounded] at *
  omega

theorem receipt_step_mono (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (event : Event K T P) (w : Nat) (body : Payload T P) (a : Fin K)
    (received : s.receipts w body a = true) : (execute c committee s event).2.receipts w body a = true := by
  cases event with
  | deliver v packet =>
      simp only [execute]
      split
      · cases packet.signer with
        | pool => exact received
        | actor b => exact stamp_mono _ _ _ _ _ _ _ received
      · exact received
  | protocol cmd => simp only [execute]; split <;> exact received

theorem receipt_run_mono (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (events : List (Event K T P)) (w : Nat) (body : Payload T P) (a : Fin K)
    (received : s.receipts w body a = true) : (run c committee s events).2.receipts w body a = true := by
  induction events generalizing s with
  | nil => exact received
  | cons e rest ih => exact ih _ (receipt_step_mono c committee s e w body a received)

theorem released_cannot_finalize (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (valid : Invariant (config c committee) s.core) (events : List (Event K T P))
    (tx : Fin T) (w : Nat) (honest : w ∈ committee.core) (released : s.core.released tx w = true) :
    finalCert (config c committee) (run c committee s events).2.core tx = false :=
  released_never_finalizes valid (run_erases c committee s events) tx w honest released

theorem admitted_state (c : Context K L T P) (committee : Committee f) (packet : Packet K T P)
    (accepted : admitGenesis c committee packet = some s) :
    s = initialState c committee packet ∧ packet.payload = .genesis ∧ verify c packet = true := by
  simp only [admitGenesis] at accepted
  split at accepted
  next good => cases accepted; exact ⟨rfl,good⟩
  next => simp at accepted

theorem admitted_run (c : Context K L T P) (committee : Committee f) (packet : Packet K T P)
    (accepted : admitGenesis c committee packet = some s) (events : List (Event K T P)) :
    ControlInvariant c committee (run c committee s events).2 ∧
    Invariant (config c committee) (run c committee s events).2.core ∧
    BusinessRun (config c committee) s.core.balance ((run c committee s events).1.filterMap id)
      (run c committee s events).2.core.balance := by
  obtain ⟨rfl,valid⟩ := admitted_state c committee packet accepted
  exact ⟨control_run c committee _ events (control_initial c committee packet valid),
    trace_invariant (initial_invariant _) (run_erases c committee (initialState c committee packet) events),
    funded_refinement c committee packet events⟩

theorem infinite_refinement (c : Context K L T P) (committee : Committee f) (packet : Packet K T P)
    (states : Nat → State K T P) (events : Nat → Event K T P) (labels : Nat → Option (Fin T))
    (accepted : admitGenesis c committee packet = some (states 0))
    (steps : ∀ n, execute c committee (states n) (events n) = (labels n,states (n+1))) :
    (∀ n, ControlInvariant c committee (states n)) ∧
    (∀ n, Simulates (config c committee) (states n).core (labels n) (states (n+1)).core) ∧
    (∀ n d, 0 ≤ (states n).core.balance d) := by
  obtain ⟨start,valid⟩ := admitted_state c committee packet accepted
  have controls : ∀ n, ControlInvariant c committee (states n) := by
    intro n
    induction n with
    | zero => rw [start]; exact control_initial c committee packet valid
    | succ n ih =>
        have next := control_step c committee (states n) (events n) ih
        simpa [steps n] using next
  have base := infinite_async_refinement (config c committee) (fun n => (states n).core) labels
    (by change (states 0).core = _; rw [start]; rfl) (fun n => by simpa [steps n] using execute_erases c committee (states n) (events n))
  exact ⟨controls,base.2⟩

theorem replay_same_log (c : Context K L T P) (committee : Committee f) (s : State K T P)
    (before after : List (Event K T P)) (same : before = after) :
    run c committee s before = run c committee s after := congrArg (run c committee s) same


private theorem sum_two (balance : Fin 2 → Int) :
    isum (List.finRange 2) balance = balance 0 + balance 1 := by
  change balance 0 + (balance 1 + 0) = balance 0 + balance 1
  omega

private theorem initial_rights (c : Context K L T P) (committee : Committee f) :
    (initial (config c committee)).balance 0 = (c.initialRights : Int) := rfl

private theorem initial_headroom (c : Context K L T P) (committee : Committee f) (cap : Int)
    (bounded : c.ceiling = some cap) :
    (initial (config c committee)).balance 1 = (headroom c : Int) := by
  simp [initial,config,Collective.config,Collective.currency,Currency.config,business,bounded]
  have same : Fin.addCases (fun _ : Fin 1 => c.initialRights) (fun _ : Fin 1 => headroom c)
      (Fin.natAdd 1 (0 : Fin 1)) = headroom c := Fin.addCases_right (0 : Fin 1)
  exact congrArg (fun n : Nat => (n : Int)) same

theorem declared_floor (c : Context K L T P) (committee : Committee f) (genesis : Packet K T P)
    (events : List (Event K T P)) :
    c.floor ≤ c.floor + (run c committee (initialState c committee genesis) events).2.core.balance 0 := by
  have nonnegative := resources_nonnegative c committee genesis events 0
  omega

theorem declared_ceiling (c : Context K L T P) (committee : Committee f) (genesis : Packet K T P)
    (valid : genesis.payload = .genesis ∧ verify c genesis = true) (cap : Int)
    (bounded : c.ceiling = some cap) (events : List (Event K T P)) :
    c.floor + (run c committee (initialState c committee genesis) events).2.core.balance 0 ≤ cap := by
  have conservation := Currency.business_run_conservation (funded_refinement c committee genesis events)
    (List.finRange 2) (Currency.capped_conservation (Collective.currency (business c)) (by simp [Collective.currency,business,bounded]))
  rw [sum_two, sum_two, initial_rights, initial_headroom c committee cap bounded] at conservation
  have positive := resources_nonnegative c committee genesis events 1
  have bound := declared_cap_bound c genesis valid cap bounded
  omega


theorem operation_verified (c : Context K L T P) (a : Fin K) (tx : Fin T)
    (verified : verify c (canonical c (.operation tx) a) = true) :
    a = c.actor tx ∧ operationAuthorized c tx = true := by
  simp only [verify,canonical,decide_true,Bool.true_and,Bool.and_eq_true_iff,decide_eq_true_eq] at verified
  exact verified.2

theorem operation_quorum_has_authorized_actor (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (h : ControlInvariant c committee s) (tx : Fin T)
    (certificate : operationCert (config c committee) s.core tx = true) :
    ∃ w ∈ committee.core, s.receipts w (.operation tx) (c.actor tx) = true ∧
      operationAuthorized c tx = true := by
  obtain ⟨w,honest,voted⟩ := quorum_has_core (config c committee) _ certificate
  have received := h.signatures tx w honest voted
  exact ⟨w,honest,received,(operation_verified c _ tx (h.receipts w _ _ received)).2⟩

theorem finality_has_authorized_actor (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (h : ControlInvariant c committee s) (valid : Invariant (config c committee) s.core)
    (tx : Fin T) (certificate : finalCert (config c committee) s.core tx = true) :
    operationAuthorized c tx = true := by
  obtain ⟨_,_,_,auth⟩ := operation_quorum_has_authorized_actor c committee s h tx
    (final_operation valid.evidence tx certificate)
  exact auth

theorem minted_finality_checks_issuer (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (h : ControlInvariant c committee s) (valid : Invariant (config c committee) s.core)
    (tx : Fin T) (mint : c.isMint tx = true)
    (certificate : finalCert (config c committee) s.core tx = true) :
    c.policy.issues (c.actor tx) = true := by
  have auth := finality_has_authorized_actor c committee s h valid tx certificate
  simp only [operationAuthorized,mint,Bool.and_eq_true_iff] at auth
  exact auth.2

theorem honest_successor_choice_persists (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (valid : Invariant (config c committee) s.core) (events : List (Event K T P))
    (p : Fin P) (w : Nat) (honest : w ∈ committee.core) (voted : s.core.votes p w = true) :
    (run c committee s events).2.core.choices (checkpoint c p).parent w = some p := by
  have trace := run_erases c committee s events
  have newer := trace_invariant valid trace
  exact newer.evidence.voted_choice p w honest ((trace_journals trace).votes p w voted)

theorem byzantine_auth_guard_unrestricted (c : Context K L T P) (committee : Committee f)
    (s : State K T P) (tx : Fin T) (p : Fin P) (w : Nat) (outside : w ∉ committee.core) :
    guard c committee s (.sign tx w) = true ∧ guard c committee s (.fence tx w) = true ∧
      guard c committee s (.endorse p w) = true := by simp [guard,outside]

/-- Verify genesis and replay the persisted event journal. -/
def recover (c : Context K L T P) (committee : Committee f) (packet : Packet K T P)
    (journal : List (Event K T P)) : Option (State K T P) :=
  (admitGenesis c committee packet).map (fun state => (run c committee state journal).2)

theorem recover_control (c : Context K L T P) (committee : Committee f) (packet : Packet K T P)
    (journal : List (Event K T P)) (restored : recover c committee packet journal = some s) :
    ControlInvariant c committee s ∧ Invariant (config c committee) s.core := by
  simp only [recover] at restored
  cases accepted : admitGenesis c committee packet with
  | none => simp [accepted] at restored
  | some start =>
      simp only [accepted,Option.map_some,Option.some.injEq] at restored
      subst s
      have result := admitted_run c committee packet accepted journal
      exact ⟨result.1,result.2.1⟩

end CBCL.ConsensusFree.CollectiveActors
