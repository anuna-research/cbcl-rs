import LeanCbcl.ConsensusFree.OwnerFunding

/-! SPEC-034 initialized finite-capacity owner/validator/message product.
Wire hashes and signature verification are idealized immutable identities. Local
first-time durable actions are interleaved; retries, failed writes and duplicate
messages stutter. There is no global ledger decision or cancellation command. -/
namespace CBCL.ConsensusFree.OwnerProduct
open CBCL.ValidatorBudget
variable {N W R f : Nat}

/-- Kinds of durable request-indexed owner facts. -/
inductive U where
  | accepted | issued | final | income | batch | version | activated | operation | complete
  deriving DecidableEq, Repr
/-- Kinds of request-indexed evidence and votes stored for individual validators. -/
inductive L where
  | act | metadata | adopted | vote | voteReceived | operation | effect | effectReceived | final | income
  deriving DecidableEq, Repr
/-- Permanent owner-wide freeze and observed seal-certificate facts. -/
inductive G where
  | frozen | seal
  deriving DecidableEq, Repr
/-- Kinds of validator-indexed seal votes, receipts and verified root evidence. -/
inductive P where
  | sealVote | sealReceived | root
  deriving DecidableEq, Repr
/-- Finite coordinates of the product's monotone durable evidence projection. -/
inductive Flag (N W : Nat) where
  | u (kind : U) (request : Fin N)
  | l (kind : L) (request : Fin N) (validator : Fin W)
  | g (kind : G)
  | p (kind : P) (validator : Fin W)
  | root (request : Fin N)
  | snapshot (version income : Fin N)
  | external (income object : Fin N) (validator : Fin W)
  deriving DecidableEq, Repr

/-- Pinned financial inputs, committee identities and finite external proof catalogues. -/
structure Config (N W R f : Nat) where
  /-- Immutable identities and resource effects used for admission and version books. -/
  costs : OwnerFunding.Costs N R
  /-- Distinct honest validators whose votes alone meet the quorum threshold. -/
  core : List (Fin W)
  /-- Remaining committee members, which may behave Byzantine or remain silent. -/
  others : List (Fin W)
  distinct : (core ++ others).Nodup
  coreSize : core.length = 2*f+1
  otherSize : others.length ≤ f
  /-- Correct local replica whose adoption permits owner activation. -/
  ownerValidator : Fin W
  ownerHonest : ownerValidator ∈ core
  /-- A received external effects proof retains its finite verified dependency
  closure. These nodes are existing public evidence, never future signatures. -/
  external : Fin N → OwnedProgress.Retry.Catalogue N
  externalVerified : ∀ i, costs.incomingAuthenticated i = true →
    ∀ node, (external i).verified node = true
  /-- Integer envelope pinned by the initial version. -/
  limit : Fin R → Nat
  safeLimit : ∀ d, limit d * (2*f+1) ≤ costs.initial d * (f+1)

/-- Durable product evidence and immutable resource books pinned for each version. -/
structure State (N W R : Nat) where
  /-- Monotone durable owner, validator, receipt and evidence facts. -/
  bits : Flag N W → Bool
  /-- Exact books pinned at first publication of this immutable version. -/
  allocation : Fin N → Fin R → Int

/-- Product state before any admission, publication, vote or receipt. -/
def initial : State N W R := ⟨fun _ => false, fun _ _ => 0⟩
/-- Project owner admission and verified receipt facts into the funding model. -/
def funds (s : State N W R) : OwnerFunding.State N R :=
  ⟨s.bits ∘ Flag.u .accepted, s.bits ∘ Flag.u .issued,
   s.bits ∘ Flag.u .final, s.bits ∘ Flag.u .income⟩
/-- Retain a finite set of newly durable facts without clearing existing facts. -/
def add (s : State N W R) (flags : List (Flag N W)) : State N W R :=
  {s with bits := fun k => if k ∈ flags then true else s.bits k}
/-- External credit identities copied into a newly pinned version. -/
def snapshots (s : State N W R) (i : Fin N) : List (Flag N W) :=
  ((List.finRange N).filter (fun j => s.bits (.u .income j))).map (Flag.snapshot i)
/-- Publish immutable version books and choose the first root intent exactly once. -/
def pin (c : Config N W R f) (s : State N W R) (i : Fin N) : State N W R :=
  { add s (if (List.finRange N).any (fun j => s.bits (.u .version j))
      then [.u .version i] ++ snapshots s i else [.u .version i, .root i] ++ snapshots s i) with
    allocation := setAt s.allocation i (OwnerFunding.allocation c.costs (funds s)) }

/-- Count actual signature facts from the distinct pinned committee. -/
def quorum (c : Config N W R f) (votes : Fin W → Bool) : Bool :=
  decide (2*f+1 ≤ (c.core ++ c.others).countP votes)
/-- Total resource debit of the entire owner-issued concurrent batch. -/
def batchTotal (c : Config N W R f) (s : State N W R) (d : Fin R) : Int :=
  OwnerFunding.marked (fun i => s.bits (.u .batch i)) (fun i => c.costs.debit i d)
/-- Whether one more request fits the initial allocation and concurrent envelope. -/
def batchFits (c : Config N W R f) (s : State N W R) (i : Fin N) : Prop :=
  ∀ d, c.costs.debit i d ≤ c.costs.initial d ∧
    batchTotal c s d + c.costs.debit i d ≤ c.limit d
/-- The next accepted unissued request in durable FIFO issuance order. -/
def head (s : State N W R) (i : Fin N) : Prop :=
  s.bits (.u .accepted i) = true ∧ s.bits (.u .issued i) = false ∧
  ∀ j, j < i → s.bits (.u .issued j) = true
/-- Whether every issued request has an owner-journaled completion record. -/
def drained (s : State N W R) : Prop :=
  ∀ i, s.bits (.u .issued i) = true → s.bits (.u .complete i) = true
/-- Whether the owner has published a permanent root intent. -/
def rootExists (s : State N W R) : Prop := ∃ i, s.bits (.root i) = true
/-- Local predecessor metadata, settled history and incoming proof prerequisites. -/
def versionKnown (s : State N W R) (i : Fin N) (w : Fin W) : Prop :=
  (∀ j, j < i → s.bits (.u .version j) = true → s.bits (.l .metadata j w) = true) ∧
  (∀ j, j < i → s.bits (.l .final j w) = true) ∧
  (∀ j, s.bits (.snapshot i j) = true → s.bits (.l .income j w) = true)
/-- Whether every retained local operation vote is covered by the target history. -/
def historyCovered (s : State N W R) (i : Fin N) (w : Fin W) : Prop :=
  ∀ j, s.bits (.l .vote j w) = true → j ≤ i
/-- Whether a validator has adopted the target version and no later version. -/
def current (s : State N W R) (i : Fin N) (w : Fin W) : Prop :=
  s.bits (.l .adopted i w) = true ∧
  ∀ j, i < j → s.bits (.l .adopted j w) = false

/-- Concrete honest signing guard for concurrent envelope or full owned allocation. -/
def signReady (c : Config N W R f) (s : State N W R) (i : Fin N) (w : Fin W) : Prop :=
  s.bits (.u .issued i) = true ∧ s.bits (.l .act i w) = true ∧
  s.bits (.l .operation i w) = false ∧
  (if s.bits (.u .batch i) then
    s.bits (.p .sealVote w) = false ∧ s.bits (.p .root w) = false ∧
    (∀ j, s.bits (.l .adopted j w) = false) ∧
    (∀ d, OwnerFunding.marked (fun j => s.bits (.l .vote j w) && s.bits (.u .batch j))
      (fun j => c.costs.debit j d) + c.costs.debit i d ≤ c.limit d)
  else current s i w ∧ historyCovered s i w ∧
    (∀ d, (c.costs.debit i d : Int) ≤ s.allocation i d))

/-- Owner decisions, local validation, network receipts and optional Byzantine disclosures. -/
inductive Action (N W : Nat) where
  | admit (i : Fin N) | income (i : Fin N) | issueBatch (i : Fin N)
  | freeze (i : Fin N) | manifest (i : Fin N) | activate (i : Fin N)
  | issueOwned (i : Fin N) | seal (w : Fin W) | receiveSeal (w : Fin W)
  | formSeal | deliverRoot (w : Fin W)
  | metadata (i : Fin N) (w : Fin W) | adopt (i : Fin N) (w : Fin W)
  | act (i : Fin N) (w : Fin W) | sign (i : Fin N) (w : Fin W)
  | receiveVote (i : Fin N) (w : Fin W) | formOperation (i : Fin N)
  | deliverOperation (i : Fin N) (w : Fin W)
  | effect (i : Fin N) (w : Fin W) | receiveEffect (i : Fin N) (w : Fin W)
  | formFinal (i : Fin N) | deliverFinal (i : Fin N) (w : Fin W)
  | complete (i : Fin N)
  /-- Optional genuinely formed certificates privately disclosed by Byzantine peers.
  These commands are never included in honest-service fairness. -/
  | privateOperation (i : Fin N) (w : Fin W)
  | privateFinal (i : Fin N) (w : Fin W)
  | feedbackOperation (i : Fin N) (w : Fin W)
  | feedbackFinal (i : Fin N) (w : Fin W)
  | privateRoot (w : Fin W) | feedbackRoot (w : Fin W)
  | external (income node : Fin N) (w : Fin W) | deliverIncome (i : Fin N) (w : Fin W)
  | replay
  deriving DecidableEq, Repr

/-- First-time durable fact produced by an action, excluding replay. -/
def target : Action N W → Option (Flag N W)
  | .admit i => some (.u .accepted i) | .income i => some (.u .income i)
  | .issueBatch i | .issueOwned i => some (.u .issued i)
  | .freeze _ => some (.g .frozen) | .manifest i => some (.u .version i)
  | .activate i => some (.u .activated i) | .seal w => some (.p .sealVote w)
  | .receiveSeal w => some (.p .sealReceived w) | .formSeal => some (.g .seal)
  | .deliverRoot w => some (.p .root w) | .metadata i w => some (.l .metadata i w)
  | .adopt i w => some (.l .adopted i w) | .act i w => some (.l .act i w)
  | .sign i w => some (.l .vote i w) | .receiveVote i w => some (.l .voteReceived i w)
  | .formOperation i | .feedbackOperation i _ => some (.u .operation i)
  | .deliverOperation i w | .privateOperation i w => some (.l .operation i w)
  | .effect i w => some (.l .effect i w) | .receiveEffect i w => some (.l .effectReceived i w)
  | .formFinal i | .feedbackFinal i _ => some (.u .final i)
  | .deliverFinal i w | .privateFinal i w => some (.l .final i w)
  | .privateRoot w => some (.p .root w) | .feedbackRoot _ => some (.g .seal)
  | .external i node w => some (.external i node w)
  | .deliverIncome i w => some (.l .income i w)
  | .complete i => some (.u .complete i) | .replay => none

/-- Native prerequisite guard for each modeled action before its target freshness check. -/
def requires (c : Config N W R f) (s : State N W R) : Action N W → Prop
  | .admit i => (∀ j, j < i → s.bits (.u .accepted j) = true) ∧
      ∀ d, (c.costs.debit i d : Int) ≤ OwnerFunding.available c.costs (funds s) d
  | .income i => c.costs.incomingAuthenticated i = true
  | .issueBatch i => head s i ∧ s.bits (.g .frozen) = false ∧ batchFits c s i
  | .freeze i => head s i ∧ s.bits (.g .frozen) = false ∧ ¬ batchFits c s i
  | .manifest i => head s i ∧ s.bits (.g .frozen) = true ∧ drained s
  | .activate i => s.bits (.u .version i) = true ∧ s.bits (.g .seal) = true ∧
      current s i c.ownerValidator
  | .issueOwned i => head s i ∧ s.bits (.u .activated i) = true ∧ drained s ∧
      ∀ d, (c.costs.debit i d : Int) ≤ s.allocation i d
  | .seal w => (∃ i, s.bits (.root i) = true ∧ s.bits (.l .metadata i w) = true) ∧
      (if w ∈ c.core then s.bits (.p .root w) = false ∧
        (∀ i, s.bits (.u .batch i) = true → s.bits (.l .final i w) = true) ∧
        (∀ i, s.bits (.l .vote i w) = true → s.bits (.u .batch i) = true)
       else True)
  | .receiveSeal w => s.bits (.p .sealVote w) = true
  | .formSeal => rootExists s ∧ quorum c (fun w => s.bits (.p .sealReceived w)) = true
  | .deliverRoot w => s.bits (.g .seal) = true ∧
      ∃ i, s.bits (.root i) = true ∧ s.bits (.l .metadata i w) = true
  | .metadata i w => s.bits (.u .version i) = true ∧ versionKnown s i w
  | .adopt i w => s.bits (.l .metadata i w) = true ∧ s.bits (.p .root w) = true ∧
      (∀ j, j < i → s.bits (.u .version j) = true → s.bits (.l .adopted j w) = true) ∧
      (∀ j, i < j → s.bits (.l .adopted j w) = false) ∧
      (∀ j, s.bits (.l .vote j w) = true → j < i)
  | .act i w => s.bits (.u .issued i) = true ∧
      (s.bits (.u .batch i) = true ∨ s.bits (.l .metadata i w) = true)
  | .sign i w => if w ∈ c.core then signReady c s i w else s.bits (.u .issued i) = true
  | .receiveVote i w => s.bits (.l .vote i w) = true
  | .formOperation i => s.bits (.u .issued i) = true ∧
      quorum c (fun w => s.bits (.l .voteReceived i w)) = true
  | .deliverOperation i w => s.bits (.u .operation i) = true ∧ s.bits (.l .act i w) = true
  | .effect i w => if w ∈ c.core then
      s.bits (.l .operation i w) = true ∧ s.bits (.l .act i w) = true ∧ s.bits (.l .final i w) = false
      else s.bits (.u .issued i) = true
  | .receiveEffect i w => s.bits (.l .effect i w) = true
  | .formFinal i => s.bits (.u .issued i) = true ∧ s.bits (.u .operation i) = true ∧
      quorum c (fun w => s.bits (.l .effectReceived i w)) = true
  | .deliverFinal i w => s.bits (.u .final i) = true ∧ s.bits (.l .act i w) = true ∧ s.bits (.l .operation i w) = true
  | .complete i => s.bits (.u .final i) = true
  | .privateOperation i w => s.bits (.l .act i w) = true ∧
      quorum c (fun v => s.bits (.l .vote i v)) = true
  | .privateFinal i w => s.bits (.l .operation i w) = true ∧
      quorum c (fun v => s.bits (.l .effect i v)) = true
  | .feedbackOperation i w => s.bits (.u .issued i) = true ∧ s.bits (.l .operation i w) = true
  | .feedbackFinal i w => s.bits (.u .issued i) = true ∧ s.bits (.l .final i w) = true ∧
      s.bits (.u .operation i) = true
  | .privateRoot w => rootExists s ∧ quorum c (fun v => s.bits (.p .sealVote v)) = true ∧
      ∃ i, s.bits (.root i) = true ∧ s.bits (.l .metadata i w) = true
  | .feedbackRoot w => rootExists s ∧ s.bits (.p .root w) = true
  | .external i node w => s.bits (.u .income i) = true ∧
      (c.external i).verified node = true ∧
      ∀ dep ∈ (c.external i).dependencies node, s.bits (.external i dep w) = true
  | .deliverIncome i w => s.bits (.u .income i) = true ∧
      ∀ node, s.bits (.external i node w) = true
  | .replay => True

/-- Apply an action's durable facts and any immutable version-book snapshot. -/
def applyAction (c : Config N W R f) (s : State N W R) (a : Action N W) : State N W R :=
  match a with
  | .manifest i => pin c s i
  | .issueBatch i => add s [.u .issued i, .u .batch i]
  | _ => match target a with | some k => add s [k] | none => s

/-- Whether an action's prerequisites hold and its target is still absent. -/
def Enabled (c : Config N W R f) (s : State N W R) (a : Action N W) : Prop :=
  requires c s a ∧ match target a with | none => True | some k => s.bits k = false
instance : Decidable (Enabled c s a) := by
  cases a <;> simp only [Enabled, requires, target, head, batchFits, drained, rootExists, versionKnown, signReady, current, historyCovered] <;> infer_instance

/-- Execute an enabled action; rejected, duplicate or failed attempts stutter. -/
def perform (c : Config N W R f) (s : State N W R) (a : Action N W) : State N W R :=
  if Enabled c s a then applyAction c s a else s

/-- Honest service is per retained job, not aggregate throughput. Admission,
external income, private certificates and Byzantine handlers may stay silent. -/
def honest (c : Config N W R f) : Action N W → Prop
  | .admit _ | .income _ | .privateOperation _ _ | .privateFinal _ _ | .privateRoot _ | .replay => False
  | .seal w | .receiveSeal w | .deliverRoot w | .metadata _ w | .adopt _ w
  | .act _ w | .sign _ w | .receiveVote _ w | .deliverOperation _ w
  | .effect _ w | .receiveEffect _ w | .deliverFinal _ w
  | .feedbackOperation _ w | .feedbackFinal _ w | .feedbackRoot w
  | .external _ _ w | .deliverIncome _ w => w ∈ c.core
  | _ => True

/-- Existence of an accepted request without owner-journaled completion. -/
def Pending (s : State N W R) : Prop :=
  ∃ i, s.bits (.u .accepted i) = true ∧ s.bits (.u .complete i) = false
/-- An issued request whose effects certificate the owner has not yet verified. -/
def Unfinal (s : State N W R) (i : Fin N) : Prop :=
  s.bits (.u .issued i) = true ∧ s.bits (.u .final i) = false
/-- An old request referenced by a later published version's retained history. -/
def HeldDependency (s : State N W R) (i : Fin N) : Prop :=
  ∃ j, s.bits (.u .version j) = true ∧ i < j

/-- Retained work still necessary for pending requests or their selected dependencies. -/
def Needed (s : State N W R) : Action N W → Prop
  | .sign i _ | .receiveVote i _ | .feedbackOperation i _ | .formOperation i =>
      Pending s ∧ Unfinal s i ∧ s.bits (.u .operation i) = false
  | .effect i _ | .receiveEffect i _ | .feedbackFinal i _ | .formFinal i =>
      Pending s ∧ Unfinal s i
  | .seal _ | .receiveSeal _ | .feedbackRoot _ | .formSeal =>
      Pending s ∧ s.bits (.g .seal) = false
  | .act i _ | .deliverOperation i _ | .deliverFinal i _ =>
      Pending s ∧ (Unfinal s i ∨ HeldDependency s i)
  | .metadata i _ | .adopt i _ => Pending s ∧ s.bits (.u .version i) = true
  | .deliverRoot _ => Pending s ∧ rootExists s
  | .external i _ _ | .deliverIncome i _ =>
      Pending s ∧ ∃ j, s.bits (.u .version j) = true ∧ s.bits (.snapshot j i) = true
  | _ => True

/-- Initialized interleaving with fair service only for necessary honest work. -/
structure Execution (c : Config N W R f) where
  /-- Durable product state after each completed service turn. -/
  state : Nat → State N W R
  /-- Owner, validator or network action attempted at each service turn. -/
  action : Nat → Action N W
  starts : state 0 = initial
  step : ∀ n, state (n+1) = perform c (state n) (action n)
  fair : ∀ a, honest c a → ∀ start,
    (∀ n, start ≤ n → Enabled c (state n) a ∧ Needed (state n) a) →
    ∃ n, start ≤ n ∧ action n = a

variable {c : Config N W R f}

@[simp] theorem add_bits (s : State N W R) (ks : List (Flag N W)) (k : Flag N W) :
    (add s ks).bits k = (if k ∈ ks then true else s.bits k) := rfl

theorem apply_mono (c : Config N W R f) (s : State N W R) (a : Action N W)
    (k : Flag N W) (hk : s.bits k = true) : (applyAction c s a).bits k = true := by
  cases a <;> simp only [applyAction, target, add_bits, pin]
  all_goals first | exact hk | split <;> simp_all

theorem step_mono (e : Execution c) (n : Nat) (k : Flag N W)
    (hk : (e.state n).bits k = true) : (e.state (n+1)).bits k = true := by
  rw [e.step]; unfold perform; split
  · exact apply_mono _ _ _ _ hk
  · exact hk

theorem apply_target (c : Config N W R f) (s : State N W R) (a : Action N W)
    (k : Flag N W) (ht : target a = some k) : (applyAction c s a).bits k = true := by
  cases a <;> simp_all [target, applyAction, pin, add_bits]
  split <;> simp_all


@[simp] theorem set_true [DecidableEq α] (fn : α → Bool) (i : α) :
    setAt fn i true = fun j => decide (j = i) || fn j := by
  funext j
  by_cases h : j = i <;> simp [setAt, h]

/-- Financial state is the projection of actual owner admissions, issuance and
verified effects receipts in this same initialized execution. -/
theorem funds_apply (c : Config N W R f) (s : State N W R) (a : Action N W)
    (en : Enabled c s a) :
    OwnerFunding.Step c.costs (funds s) (funds (applyAction c s a)) := by
  cases a <;> simp only [Enabled, requires, target] at en
  case admit i =>
    have st := OwnerFunding.Step.enqueue (c := c.costs) (funds s) i en.2 en.1.2
    simpa [funds, OwnerFunding.enqueue, applyAction, target, add, Function.comp_def, set_true] using st
  case income i =>
    have st := OwnerFunding.Step.income (c := c.costs) (funds s) i en.1 en.2
    simpa [funds, OwnerFunding.income, applyAction, target, add, Function.comp_def, set_true] using st
  case issueBatch i =>
    have st := OwnerFunding.Step.issue (c := c.costs) (funds s) i en.1.1.1
    simpa [funds, OwnerFunding.issue, applyAction, target, add, Function.comp_def, set_true] using st
  case issueOwned i =>
    have st := OwnerFunding.Step.issue (c := c.costs) (funds s) i en.1.1.1
    simpa [funds, OwnerFunding.issue, applyAction, target, add, Function.comp_def, set_true] using st
  case formFinal i =>
    have st := OwnerFunding.Step.finalize (c := c.costs) (funds s) i en.1.1 en.2
    simpa [funds, OwnerFunding.finalize, applyAction, target, add, Function.comp_def, set_true] using st
  case feedbackFinal i w =>
    have st := OwnerFunding.Step.finalize (c := c.costs) (funds s) i en.1.1 en.2
    simpa [funds, OwnerFunding.finalize, applyAction, target, add, Function.comp_def, set_true] using st
  case manifest i =>
    by_cases h : ∃ j, s.bits (.u .version j) = true
    all_goals simpa [funds, applyAction, pin, add, snapshots, Function.comp_def, h] using
      (OwnerFunding.Step.replay (c := c.costs) (funds s))
  all_goals
    simpa [funds, applyAction, target, pin, add, Function.comp_def] using
      (OwnerFunding.Step.replay (c := c.costs) (funds s))

theorem funding_run (e : Execution c) (n : Nat) :
    OwnerFunding.Run c.costs OwnerFunding.initial (funds (e.state n)) := by
  induction n with
  | zero => simpa [e.starts, funds, initial, OwnerFunding.initial] using
      (OwnerFunding.Run.refl (c := c.costs) (OwnerFunding.initial : OwnerFunding.State N R))
  | succ n ih =>
    rw [e.step]; unfold perform; split
    next en => exact .next ih (funds_apply _ _ _ en)
    next disabled => exact ih


/-- Inductive owner-order, root, history and authentication-support invariants. -/
structure Causal (c : Config N W R f) (s : State N W R) : Prop where
  admittedPrefix : ∀ i, s.bits (.u .accepted i) = true → ∀ j, j < i → s.bits (.u .accepted j) = true
  issuedAccepted : ∀ i, s.bits (.u .issued i) = true → s.bits (.u .accepted i) = true
  issuedPrefix : ∀ i, s.bits (.u .issued i) = true → ∀ j, j < i → s.bits (.u .issued j) = true
  completedFinal : ∀ i, s.bits (.u .complete i) = true → s.bits (.u .final i) = true
  batchIssued : ∀ i, s.bits (.u .batch i) = true → s.bits (.u .issued i) = true
  versionFrozen : ∀ i, s.bits (.u .version i) = true → s.bits (.g .frozen) = true
  versionPrior : ∀ i, s.bits (.u .version i) = true → ∀ j, j < i → s.bits (.u .complete j) = true
  activeVersion : ∀ i, s.bits (.u .activated i) = true → s.bits (.u .version i) = true
  activeSeal : ∀ i, s.bits (.u .activated i) = true → s.bits (.g .seal) = true
  metadataVersion : ∀ i w, s.bits (.l .metadata i w) = true → s.bits (.u .version i) = true
  adoptedMetadata : ∀ i w, s.bits (.l .adopted i w) = true → s.bits (.l .metadata i w) = true
  adoptedParents : ∀ i w, s.bits (.l .adopted i w) = true → ∀ j, j < i →
    s.bits (.u .version j) = true → s.bits (.l .adopted j w) = true
  actIssued : ∀ i w, s.bits (.l .act i w) = true → s.bits (.u .issued i) = true
  voteIssued : ∀ i w, s.bits (.l .vote i w) = true → s.bits (.u .issued i) = true
  operationIssued : ∀ i, s.bits (.u .operation i) = true → s.bits (.u .issued i) = true
  rootVersion : ∀ i, s.bits (.root i) = true → s.bits (.u .version i) = true
  snapshotIncome : ∀ i j, s.bits (.snapshot i j) = true → s.bits (.u .income j) = true
  issuedMode : ∀ i, s.bits (.u .issued i) = true →
    s.bits (.u .batch i) = true ∨ s.bits (.u .activated i) = true
  voteMode : ∀ i w, w ∈ c.core → s.bits (.l .vote i w) = true →
    s.bits (.u .batch i) = true ∨ s.bits (.l .adopted i w) = true
  finalOperation : ∀ i, s.bits (.u .final i) = true → s.bits (.u .operation i) = true
  versionRoot : ∀ i, s.bits (.u .version i) = true → ∃ j, s.bits (.root j) = true
  uniqueRoot : ∀ i j, s.bits (.root i) = true → s.bits (.root j) = true → i = j
  rootDrained : ∀ i j, s.bits (.root i) = true → s.bits (.u .batch j) = true → s.bits (.u .complete j) = true
  batchEarlier : ∀ i j, s.bits (.u .version i) = true → s.bits (.u .batch j) = true → j < i
  sealRoot : s.bits (.g .seal) = true → ∃ i, s.bits (.root i) = true
  sealVoteRoot : ∀ w, s.bits (.p .sealVote w) = true → ∃ i, s.bits (.root i) = true
  localRoot : ∀ w, s.bits (.p .root w) = true → ∃ i, s.bits (.root i) = true

@[simp] theorem initial_causal (c : Config N W R f) : Causal c (initial : State N W R) := by
  constructor <;> simp [initial]

set_option maxHeartbeats 8000000 in
 theorem causal_apply (c : Config N W R f) (s : State N W R) (a : Action N W)
    (h : Causal c s) (funding : OwnerFunding.Invariant c.costs (funds s))
    (en : Enabled c s a) : Causal c (applyAction c s a) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩
  have finalIssued := funding.final_issued
  cases a <;> simp only [Enabled, requires, target] at en
  case manifest i =>
    by_cases hv : ∃ j, s.bits (.u .version j) = true
    all_goals constructor <;> simp [applyAction, pin, snapshots, add_bits, hv]
    all_goals simp only [head, drained, funds, Function.comp_def] at en finalIssued
    all_goals grind
  all_goals
    constructor <;> simp [applyAction, target, add_bits]
  all_goals simp only [head, drained, signReady, current, historyCovered, rootExists, funds, Function.comp_def] at en finalIssued
  all_goals grind


theorem causal_run (e : Execution c) (n : Nat) : Causal c (e.state n) := by
  induction n with
  | zero => rw [e.starts]; exact initial_causal c
  | succ n ih =>
    rw [e.step]; unfold perform; split
    next en => exact causal_apply _ _ _ ih (OwnerFunding.run_invariant (funding_run e n)) en
    next disabled => exact ih


/-- Complete finite catalogue of durable evidence coordinates for fixed capacities. -/
def flags (N W : Nat) : List (Flag N W) :=
  [.g .frozen, .g .seal] ++
  (List.finRange N).flatMap (fun i =>
    [.u .accepted i, .u .issued i, .u .final i, .u .income i,
     .u .batch i, .u .version i, .u .activated i, .u .operation i,
     .u .complete i, .root i] ++ (List.finRange N).map (Flag.snapshot i) ++
    (List.finRange W).flatMap (fun w =>
      [.l .act i w, .l .metadata i w, .l .adopted i w, .l .vote i w,
       .l .voteReceived i w, .l .operation i w, .l .effect i w,
       .l .effectReceived i w, .l .final i w, .l .income i w] ++
       (List.finRange N).map (fun node => .external i node w))) ++
  (List.finRange W).flatMap (fun w => [.p .sealVote w, .p .sealReceived w, .p .root w])

theorem flags_complete (k : Flag N W) : k ∈ flags N W := by
  cases k with
  | u kind i => cases kind <;> simp [flags]
  | l kind i w => cases kind <;> simp [flags]
  | g kind => cases kind <;> simp [flags]
  | p kind w => cases kind <;> simp [flags]
  | root i => simp [flags]
  | snapshot i j => simp [flags]
  | external i node w => simp [flags]

private theorem finite_stable (xs : List α) (p : Nat → α → Prop)
    (each : ∀ a ∈ xs, ∃ t, ∀ n, t ≤ n → p n a) :
    ∃ t, ∀ n, t ≤ n → ∀ a ∈ xs, p n a := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨t, ht⟩ := each a (by simp)
    obtain ⟨u, hu⟩ := ih (fun b hb => each b (by simp [hb]))
    exact ⟨max t u, fun n hn b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ht n (by omega)
      · exact hu n (by omega) b hb⟩

theorem bits_eventually_stable (e : Execution c) :
    ∃ t, ∀ n, t ≤ n → ∀ k, (e.state n).bits k = (e.state t).bits k := by
  classical
  have each : ∀ k ∈ flags N W, ∃ t, ∀ n, t ≤ n →
      ∀ m, n ≤ m → (e.state m).bits k = (e.state n).bits k := by
    intro k _
    by_cases occurs : ∃ n, (e.state n).bits k = true
    · obtain ⟨t, ht⟩ := occurs
      have keep := MultiParent.Liveness.persists _ (fun n => step_mono e n k) ht
      exact ⟨t, fun n hn m hm => (keep m (by omega)).trans (keep n hn).symm⟩
    · exact ⟨0, fun n _ m _ => by
        have absent : ∀ n, (e.state n).bits k = false := by
          intro n; cases h : (e.state n).bits k <;> simp_all
        simp [absent]⟩
  obtain ⟨t, ht⟩ := finite_stable (flags N W) _ each
  exact ⟨t, fun n hn k => (ht t (by omega) k (flags_complete k) n hn)⟩

/-- Stabilization concerns structural capacity, never a journal-full failure. -/
theorem eventually_stationary (e : Execution c) :
    ∃ t, ∀ n, t ≤ n → e.state n = e.state t := by
  obtain ⟨t, ht⟩ := bits_eventually_stable e
  have unchanged : ∀ n, t ≤ n → e.state (n+1) = e.state n := by
    intro n hn
    rw [e.step]
    unfold perform
    split
    next en =>
      cases htarget : target (e.action n) with
      | none =>
        have ar : e.action n = .replay := by cases ha : e.action n <;> simp_all [target]
        simp [ar, applyAction, target]
      | some k =>
        have absent : (e.state n).bits k = false := by simpa [Enabled, htarget] using en.2
        have set : (e.state (n+1)).bits k = true := by
          rw [e.step]; simp only [perform, if_pos en]
          exact apply_target _ _ _ _ htarget
        have eq := (ht (n+1) (by omega) k).trans (ht n hn k).symm
        simp [eq, absent] at set
    next disabled => rfl
  refine ⟨t, ?_⟩
  intro n hn
  induction n with
  | zero =>
    have eq : t = 0 := by omega
    subst t; rfl
  | succ n ih =>
    by_cases h : t ≤ n
    · exact (unchanged n h).trans (ih h)
    · have eq : t = n+1 := by omega
      subst t; rfl

/-- A state where every necessary honest action already has its durable target. -/
def Saturated (c : Config N W R f) (s : State N W R) : Prop :=
  ∀ a, honest c a → requires c s a → Needed s a → ∀ k, target a = some k → s.bits k = true

theorem stationary_saturated (e : Execution c) (t : Nat)
    (fixed : ∀ n, t ≤ n → e.state n = e.state t) : Saturated c (e.state t) := by
  intro a ha hr needed k hk
  by_cases done : (e.state t).bits k = true
  · exact done
  · have absent : (e.state t).bits k = false := by cases h : (e.state t).bits k <;> simp_all
    have en : ∀ n, t ≤ n → Enabled c (e.state n) a := by
      intro n hn; rw [fixed n hn]; exact ⟨hr, by simp [hk, absent]⟩
    obtain ⟨n, hn, chosen⟩ := e.fair a ha t (fun n hn => ⟨en n hn, by simpa only [fixed n hn] using needed⟩)
    have set : (e.state (n+1)).bits k = true := by
      rw [e.step]; unfold perform
      rw [if_pos (by simpa [chosen] using en n hn)]
      exact apply_target _ _ _ _ (by simpa [chosen] using hk)
    rw [fixed (n+1) (by omega), absent] at set
    contradiction

end CBCL.ConsensusFree.OwnerProduct
