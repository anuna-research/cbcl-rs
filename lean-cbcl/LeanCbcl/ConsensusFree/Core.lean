import LeanCbcl.ConsensusFreeArithmetic

/-! SPEC-025. No consensus, reservation authority, shared available funds or winner
selection service. The archive records authenticated certificates, not decisions. -/
namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

inductive Epoch (A P : Nat) where
  | root (owner : Fin A)
  | checkpoint (id : Fin P)
  deriving DecidableEq, Repr

structure Checkpoint (A T P R : Nat) where
  owner : Fin A
  parent : Epoch A P
  depth : Nat
  held : Fin T → Bool
  refunded : Fin T → Bool
  credited : Fin T → Bool
  allocation : Fin R → Nat
  authorized : Bool

def epochOwner (cp : Fin P → Checkpoint A T P R) : Epoch A P → Fin A
  | .root a => a
  | .checkpoint p => (cp p).owner

def epochDepth (cp : Fin P → Checkpoint A T P R) : Epoch A P → Nat
  | .root _ => 0
  | .checkpoint p => (cp p).depth

structure Config (A T P R f : Nat) where
  committee : Committee f
  initial : Fin R → Nat
  checkpoints : Fin P → Checkpoint A T P R
  opEpoch : Fin T → Epoch A P
  resourceOwner : Fin R → Fin A
  cost : Fin T → Fin R → Nat
  credit : Fin T → Fin R → Nat
  authorized : Fin T → Bool
  cost_local : ∀ tx d, resourceOwner d ≠ epochOwner checkpoints (opEpoch tx) → cost tx d = 0
  disjoint : ∀ tx d, cost tx d = 0 ∨ credit tx d = 0

abbrev owner (c : Config A T P R f) := epochOwner c.checkpoints
abbrev depth (c : Config A T P R f) := epochDepth c.checkpoints

def held (c : Config A T P R f) : Epoch A P → Fin T → Bool
  | .root _, _ => false
  | .checkpoint p, tx => (c.checkpoints p).held tx
def refunded (c : Config A T P R f) : Epoch A P → Fin T → Bool
  | .root _, _ => false
  | .checkpoint p, tx => (c.checkpoints p).refunded tx
def credited (c : Config A T P R f) : Epoch A P → Fin T → Bool
  | .root _, _ => false
  | .checkpoint p, tx => (c.checkpoints p).credited tx
def allowance (c : Config A T P R f) : Epoch A P → Fin R → Nat
  | .root a, d => if c.resourceOwner d = a then c.initial d else 0
  | .checkpoint p, d => (c.checkpoints p).allocation d

def two [DecidableEq α] [DecidableEq β] (fn : α → β → γ) (a : α) (b : β) (v : γ) :=
  setAt fn a (setAt (fn a) b v)

structure State (A T P R : Nat) where
  active : Nat → Fin A → Epoch A P
  signatures : Fin T → Nat → Bool
  released : Fin T → Nat → Bool
  sealed : Epoch A P → Nat → Bool
  votes : Fin P → Nat → Bool
  choices : Epoch A P → Nat → Option (Fin P)
  effects : Fin T → Nat → Bool
  fences : Fin T → Nat → Bool
  seenOperation : Fin T → Nat → Bool
  seenFinal : Fin T → Nat → Bool
  seenCheckpoint : Fin P → Nat → Bool
  archive : Fin A → Nat → Option (Epoch A P)
  frontier : Fin A → Nat
  balance : Fin R → Int

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

def quorum (c : Config A T P R f) (v : Nat → Bool) : Bool :=
  decide (2*f+1 ≤ voteCount (c.committee.core ++ c.committee.others) v)
def operationCert (c : Config A T P R f) (s : State A T P R) (tx : Fin T) := quorum c (s.signatures tx)
def finalCert (c : Config A T P R f) (s : State A T P R) (tx : Fin T) := quorum c (s.effects tx)
def cancelCert (c : Config A T P R f) (s : State A T P R) (tx : Fin T) := quorum c (s.fences tx)
def checkpointCert (c : Config A T P R f) (s : State A T P R) (p : Fin P) := quorum c (s.votes p)
def Known (c : Config A T P R f) (s : State A T P R) (e : Epoch A P) : Prop :=
  s.archive (owner c e) (depth c e) = some e
instance : Decidable (Known c s e) := inferInstanceAs (Decidable (_ = _))
def Member (c : Config A T P R f) (w : Nat) : Prop := w ∈ c.committee.core ++ c.committee.others
instance : Decidable (Member c w) := inferInstanceAs (Decidable (_ ∈ _))

/-- A signer's own active reservations only. No business observation or frontier. -/
def charge (c : Config A T P R f) (s : State A T P R) (e : Epoch A P) (w : Nat) (d : Fin R) : Nat :=
  sumOn (List.finRange T) (fun tx =>
    if c.opEpoch tx = e ∧ s.signatures tx w = true ∧ s.released tx w = false
    then (2*f+1) * c.cost tx d else 0)

def signed (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with signatures := two s.signatures tx w true }
def freeze (s : State A T P R) (e : Epoch A P) (w : Nat) : State A T P R :=
  { s with sealed := two s.sealed e w true }
def release (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with released := two s.released tx w true }
def endorse (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : State A T P R :=
  { s with
    votes := two s.votes p w true,
    choices := two s.choices (c.checkpoints p).parent w (some p) }
def record (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : State A T P R :=
  { s with
    archive := two s.archive (c.checkpoints p).owner (c.checkpoints p).depth (some (.checkpoint p)),
    frontier := setAt s.frontier (c.checkpoints p).owner (max (s.frontier (c.checkpoints p).owner) (c.checkpoints p).depth),
    seenCheckpoint := two s.seenCheckpoint p w true }
def install (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : State A T P R :=
  { s with active := two s.active w (c.checkpoints p).owner (.checkpoint p) }
def receiveOperation (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with seenOperation := two s.seenOperation tx w true }
def receiveFinal (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with seenFinal := two s.seenFinal tx w true }
def emit (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with effects := two s.effects tx w true }
def fence (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  { s with fences := two s.fences tx w true }
def newlyFinal (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) :=
  !finalCert c s tx && finalCert c (emit s tx w) tx

def effect (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : State A T P R :=
  if newlyFinal c s tx w then
    { emit s tx w with balance := fun d => s.balance d + c.credit tx d - c.cost tx d }
  else emit s tx w

def Fits (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : Prop :=
  ∀ tx, c.opEpoch tx = (c.checkpoints p).parent → s.signatures tx w = true → (c.checkpoints p).held tx = true
instance : Decidable (Fits c s p w) := by unfold Fits; infer_instance

/-- Byzantine reports are an unrestricted overapproximation. Honest complete
reports are exactly their sealed journals; future fresh signing there is forbidden. -/
def reporter (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : Bool :=
  s.sealed (c.checkpoints p).parent w && decide (w ∈ c.committee.core → Fits c s p w)

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

def ManifestLive (c : Config A T P R f) (s : State A T P R) (p : Fin P) : Prop :=
  ManifestStatic c p ∧ Known c s (c.checkpoints p).parent ∧ quorum c (reporter c s p) = true ∧
  (∀ tx, (c.checkpoints p).credited tx = true → finalCert c s tx = true) ∧
  (∀ tx, (c.checkpoints p).refunded tx = true → cancelCert c s tx = true)
instance : Decidable (ManifestLive c s p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def SignAllowed (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : Prop :=
  w ∈ c.committee.core → c.authorized tx = true ∧ s.active w (owner c (c.opEpoch tx)) = c.opEpoch tx ∧
    s.sealed (c.opEpoch tx) w = false ∧ s.released tx w = false ∧
    (∀ d, charge c (signed s tx w) (c.opEpoch tx) w d ≤ (f+1) * allowance c (c.opEpoch tx) d)
instance : Decidable (SignAllowed c s tx w) := inferInstanceAs (Decidable (_ → _ ∧ _ ∧ _ ∧ _ ∧ _))
def EndorseAllowed (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) : Prop :=
  w ∈ c.committee.core → ManifestLive c s p ∧ s.sealed (c.checkpoints p).parent w = true ∧ Fits c s p w ∧
    (s.choices (c.checkpoints p).parent w = none ∨ s.choices (c.checkpoints p).parent w = some p)
instance : Decidable (EndorseAllowed c s p w) := inferInstanceAs (Decidable (_ → _ ∧ _ ∧ _ ∧ _))
def EffectAllowed (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : Prop :=
  w ∈ c.committee.core → s.seenOperation tx w = true ∧ s.fences tx w = false
instance : Decidable (EffectAllowed c s tx w) := inferInstanceAs (Decidable (_ → _ ∧ _))
def FenceAllowed (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) : Prop :=
  w ∈ c.committee.core → s.effects tx w = false
instance : Decidable (FenceAllowed c s tx w) := inferInstanceAs (Decidable (_ → _))

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
