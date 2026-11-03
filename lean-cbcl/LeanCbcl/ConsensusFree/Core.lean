import LeanCbcl.ConsensusFreeArithmetic

/-! SPEC-025. No consensus, reservation authority, shared available funds or winner
selection service. The archive records authenticated certificates, not decisions. -/
namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

/-- Genesis roots and historical single-parent checkpoints. -/
inductive Epoch (A P : Nat) where
  | root (owner : Fin A)
  | checkpoint (id : Fin P)
  deriving DecidableEq, Repr

/-- Immutable single-parent manifest carrying exact resource books. -/
structure Checkpoint (A T P R : Nat) where
  /-- Account owning an epoch in this configuration. -/
  owner : Fin A
  /-- Immediate predecessor epoch of the checkpoint. -/
  parent : Epoch A P
  /-- Depth of an epoch in this configuration. -/
  depth : Nat
  /-- Operations whose debits are included in the manifest. -/
  held : Fin T → Bool
  /-- Held operations whose cancellation restores their debit. -/
  refunded : Fin T → Bool
  /-- Final operations whose credits are included in the manifest. -/
  credited : Fin T → Bool
  /-- Available resource vector after applying the manifest books. -/
  allocation : Fin R → Nat
  /-- Whether the request has valid application authorization. -/
  authorized : Bool

/-- Account that owns a root or checkpoint epoch. -/
def epochOwner (cp : Fin P → Checkpoint A T P R) : Epoch A P → Fin A
  | .root a => a
  | .checkpoint p => (cp p).owner

/-- Root depth zero or the depth declared by a checkpoint. -/
def epochDepth (cp : Fin P → Checkpoint A T P R) : Epoch A P → Nat
  | .root _ => 0
  | .checkpoint p => (cp p).depth

/-- Fixed operation catalogue, resource accounting and committee assumptions. -/
structure Config (A T P R f : Nat) where
  /-- Validator committee used to count certificates. -/
  committee : Committee f
  /-- Genesis resource allocation for each coordinate. -/
  initial : Fin R → Nat
  /-- Catalogue of immutable checkpoint manifests. -/
  checkpoints : Fin P → Checkpoint A T P R
  /-- Source epoch of each operation. -/
  opEpoch : Fin T → Epoch A P
  /-- Account that controls each resource coordinate. -/
  resourceOwner : Fin R → Fin A
  /-- Resource debit required by an operation. -/
  cost : Fin T → Fin R → Nat
  /-- Resource credit produced by an operation. -/
  credit : Fin T → Fin R → Nat
  /-- Whether the request has valid application authorization. -/
  authorized : Fin T → Bool
  cost_local : ∀ tx d, resourceOwner d ≠ epochOwner checkpoints (opEpoch tx) → cost tx d = 0
  disjoint : ∀ tx d, cost tx d = 0 ∨ credit tx d = 0

/-- Account owning an epoch in this configuration. -/
abbrev owner (c : Config A T P R f) := epochOwner c.checkpoints
/-- Depth of an epoch in this configuration. -/
abbrev depth (c : Config A T P R f) := epochDepth c.checkpoints

/-- Operations whose debits are included in the manifest. -/
def held (c : Config A T P R f) : Epoch A P → Fin T → Bool
  | .root _, _ => false
  | .checkpoint p, tx => (c.checkpoints p).held tx
/-- Held operations whose cancellation restores their debit. -/
def refunded (c : Config A T P R f) : Epoch A P → Fin T → Bool
  | .root _, _ => false
  | .checkpoint p, tx => (c.checkpoints p).refunded tx
/-- Final operations whose credits are included in the manifest. -/
def credited (c : Config A T P R f) : Epoch A P → Fin T → Bool
  | .root _, _ => false
  | .checkpoint p, tx => (c.checkpoints p).credited tx
/-- Root allocation or checkpoint allocation for an epoch. -/
def allowance (c : Config A T P R f) : Epoch A P → Fin R → Nat
  | .root a, d => if c.resourceOwner d = a then c.initial d else 0
  | .checkpoint p, d => (c.checkpoints p).allocation d

/-- Update one entry of a function indexed by two keys. -/
def two [DecidableEq α] [DecidableEq β] (fn : α → β → γ) (a : α) (b : β) (v : γ) :=
  setAt fn a (setAt (fn a) b v)

/-- Validator-local journals, delivered evidence, archive and ghost balances. -/
structure State (A T P R : Nat) where
  /-- Currently installed epoch for each validator and account. -/
  active : Nat → Fin A → Epoch A P
  /-- Persistent operation reservations indexed by transaction and validator. -/
  signatures : Fin T → Nat → Bool
  /-- Reservations reclaimed after cancellation certification. -/
  released : Fin T → Nat → Bool
  /-- Epochs in which a validator has stopped fresh signing. -/
  sealed : Epoch A P → Nat → Bool
  /-- Checkpoint endorsements indexed by manifest and validator. -/
  votes : Fin P → Nat → Bool
  /-- Single successor endorsed by a validator for each predecessor. -/
  choices : Epoch A P → Nat → Option (Fin P)
  /-- Persistent effect votes indexed by transaction and validator. -/
  effects : Fin T → Nat → Bool
  /-- Persistent cancellation votes indexed by transaction and validator. -/
  fences : Fin T → Nat → Bool
  /-- Operation certificates delivered to each validator. -/
  seenOperation : Fin T → Nat → Bool
  /-- Final effect certificates delivered to each validator. -/
  seenFinal : Fin T → Nat → Bool
  /-- Checkpoint certificates delivered to each validator. -/
  seenCheckpoint : Fin P → Nat → Bool
  /-- Certified epoch recorded at each account and depth. -/
  archive : Fin A → Nat → Option (Epoch A P)
  /-- Greatest recorded checkpoint depth for each account. -/
  frontier : Fin A → Nat
  /-- Ghost business balance determined by final effects. -/
  balance : Fin R → Int

/-- Initialize empty validator journals, genesis archive entries and business balances. -/
def initial (c : Config A T P R f) : State A T P R where
  active := fun _ a => .root a
  signatures := fun _ _ => false
  released := fun _ _ => false
  sealed := fun _ _ => false
  votes := fun _ _ => false
  choices := fun _ _ => none
  effects := fun _ _ => false
  fences := fun _ _ => false
  seenOperation := fun _ _ => false
  seenFinal := fun _ _ => false
  seenCheckpoint := fun _ _ => false
  archive := fun a n => if n = 0 then some (.root a) else none
  frontier := fun _ => 0
  balance := fun d => c.initial d

/-- Whether votes contain at least `2*f+1` committee members. -/
def quorum (c : Config A T P R f) (v : Nat → Bool) : Bool :=
  decide (2*f+1 ≤ voteCount (c.committee.core ++ c.committee.others) v)
/-- Whether an operation has a quorum of reservation signatures. -/
def operationCert (c : Config A T P R f) (s : State A T P R) (tx : Fin T) := quorum c (s.signatures tx)
/-- Whether an operation has a quorum of effect votes. -/
def finalCert (c : Config A T P R f) (s : State A T P R) (tx : Fin T) := quorum c (s.effects tx)
/-- Whether an operation has a quorum of cancellation votes. -/
def cancelCert (c : Config A T P R f) (s : State A T P R) (tx : Fin T) := quorum c (s.fences tx)
/-- Whether a checkpoint has a quorum of endorsements. -/
def checkpointCert (c : Config A T P R f) (s : State A T P R) (p : Fin P) := quorum c (s.votes p)
/-- An epoch occupies its account and depth in the archive. -/
def Known (c : Config A T P R f) (s : State A T P R) (e : Epoch A P) : Prop :=
  s.archive (owner c e) (depth c e) = some e
instance : Decidable (Known c s e) := inferInstanceAs (Decidable (_ = _))
/-- A validator belongs to the configured committee. -/
def Member (c : Config A T P R f) (w : Nat) : Prop := w ∈ c.committee.core ++ c.committee.others
instance : Decidable (Member c w) := inferInstanceAs (Decidable (_ ∈ _))

/-- A signer's own active reservations only. No business observation or frontier. -/
def charge (c : Config A T P R f) (s : State A T P R) (e : Epoch A P) (w : Nat) (d : Fin R) : Nat :=
  sumOn (List.finRange T) (fun tx =>
    if c.opEpoch tx = e ∧ s.signatures tx w = true ∧ s.released tx w = false
    then (2*f+1) * c.cost tx d else 0)

/-- Record a validator's persistent operation reservation. -/
def signed (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with signatures := two s.signatures tx w true }
/-- Stop a validator from signing fresh operations in an epoch. -/
def freeze (s : State A T P R) (e : Epoch A P) (w : Nat) : State A T P R :=
  { s with sealed := two s.sealed e w true }
/-- Mark a validator's reservation as reclaimed. -/
def release (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with released := two s.released tx w true }
/-- Record an endorsement and the validator's successor choice. -/
def endorse (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : State A T P R :=
  { s with
    votes := two s.votes p w true,
    choices := two s.choices (c.checkpoints p).parent w (some p) }
/-- Archive a checkpoint certificate and advance its account frontier. -/
def record (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : State A T P R :=
  { s with
    archive := two s.archive (c.checkpoints p).owner (c.checkpoints p).depth (some (.checkpoint p)),
    frontier := setAt s.frontier (c.checkpoints p).owner (max (s.frontier (c.checkpoints p).owner) (c.checkpoints p).depth),
    seenCheckpoint := two s.seenCheckpoint p w true }
/-- Set a validator's active epoch to a checkpoint. -/
def install (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : State A T P R :=
  { s with active := two s.active w (c.checkpoints p).owner (.checkpoint p) }
/-- Record delivery of an operation certificate to a validator. -/
def receiveOperation (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with seenOperation := two s.seenOperation tx w true }
/-- Record delivery of a final effect certificate to a validator. -/
def receiveFinal (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with seenFinal := two s.seenFinal tx w true }
/-- Record one validator's effect vote. -/
def emit (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with effects := two s.effects tx w true }
/-- Record one validator's cancellation vote. -/
def fence (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with fences := two s.fences tx w true }
/-- Whether the next effect vote first completes a final certificate. -/
def newlyFinal (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) :=
  !finalCert c s tx && finalCert c (emit s tx w) tx

/-- Emit an effect vote and update the ghost balance only on first finality. -/
def effect (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  if newlyFinal c s tx w then
    { emit s tx w with balance := fun d => s.balance d + c.credit tx d - c.cost tx d }
  else emit s tx w

/-- The manifest includes every reservation signed by the reporting validator. -/
def Fits (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : Prop :=
  ∀ tx, c.opEpoch tx = (c.checkpoints p).parent → s.signatures tx w = true → (c.checkpoints p).held tx = true
instance : Decidable (Fits c s p w) := by unfold Fits; infer_instance

/-- Byzantine reports are an unrestricted overapproximation. Honest complete
reports are exactly their sealed journals; future fresh signing there is forbidden. -/
def reporter (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : Bool :=
  s.sealed (c.checkpoints p).parent w && decide (w ∈ c.committee.core → Fits c s p w)

/-- Authorization, ancestry, locality and exact resource books of a manifest. -/
def ManifestStatic (c : Config A T P R f) (p : Fin P) : Prop :=
  let m := c.checkpoints p
  m.authorized = true ∧ owner c m.parent = m.owner ∧ m.depth = depth c m.parent + 1 ∧
  (∀ tx, held c m.parent tx = true → m.held tx = true) ∧
  (∀ tx, refunded c m.parent tx = true → m.refunded tx = true) ∧
  (∀ tx, credited c m.parent tx = true → m.credited tx = true) ∧
  (∀ tx, m.refunded tx = true → m.held tx = true) ∧
  (∀ tx, m.held tx = true → owner c (c.opEpoch tx) = m.owner ∧ depth c (c.opEpoch tx) < m.depth) ∧
  (∀ d, c.resourceOwner d ≠ m.owner → m.allocation d = 0) ∧
  (∀ d, c.resourceOwner d = m.owner → (m.allocation d : Int) = (c.initial d : Int) +
    isum (List.finRange T) (fun tx => if m.credited tx then (c.credit tx d : Int) else 0) -
    isum (List.finRange T) (fun tx => if m.held tx then (c.cost tx d : Int) else 0) +
    isum (List.finRange T) (fun tx => if m.refunded tx then (c.cost tx d : Int) else 0))
instance : Decidable (ManifestStatic c p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Static validity plus the certificates needed to admit a checkpoint. -/
def ManifestLive (c : Config A T P R f) (s : State A T P R) (p : Fin P) : Prop :=
  ManifestStatic c p ∧ Known c s (c.checkpoints p).parent ∧ quorum c (reporter c s p) = true ∧
  (∀ tx, (c.checkpoints p).credited tx = true → finalCert c s tx = true) ∧
  (∀ tx, (c.checkpoints p).refunded tx = true → cancelCert c s tx = true)
instance : Decidable (ManifestLive c s p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Honest signing requires authorization, an active open epoch and sufficient local budget. -/
def SignAllowed (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : Prop :=
  w ∈ c.committee.core → c.authorized tx = true ∧ s.active w (owner c (c.opEpoch tx)) = c.opEpoch tx ∧
    s.sealed (c.opEpoch tx) w = false ∧ s.released tx w = false ∧
    (∀ d, charge c (signed s tx w) (c.opEpoch tx) w d ≤ (f+1) * allowance c (c.opEpoch tx) d)
instance : Decidable (SignAllowed c s tx w) := inferInstanceAs (Decidable (_ → _ ∧ _ ∧ _ ∧ _ ∧ _))
/-- Honest endorsement requires a valid manifest, sealed journal coverage and one successor. -/
def EndorseAllowed (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : Prop :=
  w ∈ c.committee.core → ManifestLive c s p ∧ s.sealed (c.checkpoints p).parent w = true ∧ Fits c s p w ∧
    (s.choices (c.checkpoints p).parent w = none ∨ s.choices (c.checkpoints p).parent w = some p)
instance : Decidable (EndorseAllowed c s p w) := inferInstanceAs (Decidable (_ → _ ∧ _ ∧ _ ∧ _))
/-- Honest effects require a delivered operation certificate and no cancellation vote. -/
def EffectAllowed (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : Prop :=
  w ∈ c.committee.core → s.seenOperation tx w = true ∧ s.fences tx w = false
instance : Decidable (EffectAllowed c s tx w) := inferInstanceAs (Decidable (_ → _ ∧ _))
/-- Honest cancellation cannot follow an effect vote. -/
def FenceAllowed (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : Prop :=
  w ∈ c.committee.core → s.effects tx w = false
instance : Decidable (FenceAllowed c s tx w) := inferInstanceAs (Decidable (_ → _))

/-- One permitted protocol transition, labelled only when an operation becomes final. -/
inductive Step (c : Config A T P R f) : State A T P R → Option (Fin T) → State A T P R → Prop where
  | sign (s) (tx) (w) (member : Member c w) (fresh : s.signatures tx w = false)
      (allowed : SignAllowed c s tx w) : Step c s none (signed s tx w)
  | freeze (s) (e) (w) (member : Member c w) : Step c s none (freeze s e w)
  | release (s) (tx) (w) (member : Member c w) (reserved : s.signatures tx w = true)
      (certificate : cancelCert c s tx = true) : Step c s none (release s tx w)
  | endorse (s) (p) (w) (member : Member c w) (allowed : EndorseAllowed c s p w) : Step c s none (endorse c s p w)
  | record (s) (p) (w) (member : Member c w) (certificate : checkpointCert c s p = true)
      (valid : ManifestLive c s p) : Step c s none (record c s p w)
  | install (s) (p) (w) (member : Member c w) (received : s.seenCheckpoint p w = true)
      (parent : s.active w (c.checkpoints p).owner = (c.checkpoints p).parent)
      (credits : ∀ tx, (c.checkpoints p).credited tx = true → s.seenFinal tx w = true) : Step c s none (install c s p w)
  | receiveOperation (s) (tx) (w) (member : Member c w) (certificate : operationCert c s tx = true) :
      Step c s none (receiveOperation s tx w)
  | receiveFinal (s) (tx) (w) (member : Member c w) (certificate : finalCert c s tx = true) :
      Step c s none (receiveFinal s tx w)
  | effect (s) (tx) (w) (member : Member c w) (allowed : EffectAllowed c s tx w) :
      Step c s (if newlyFinal c s tx w then some tx else none) (effect c s tx w)
  | fence (s) (tx) (w) (member : Member c w) (allowed : FenceAllowed c s tx w) : Step c s none (fence s tx w)
  | replay (s) : Step c s none s

end CBCL.ConsensusFree
