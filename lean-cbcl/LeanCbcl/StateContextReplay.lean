import LeanCbcl.StateContextEvidence
import LeanCbcl.StateWitnessReplay
import LeanCbcl.StateExecutableFreeze

/-! Replay certificates for installed context guards. Opener checks retain an
explicit receiver-root premise until protocol admission discharges it. -/
set_option autoImplicit false
namespace CBCL.StateContextReplay
open State StateLift StateLVar StateObservation StateWitnessReplay StateContextEvidence

/-- Root guard replay uses the actual immutable root-context reader. -/
theorem root_replays (input : Input) (A B : List Act) :
    Replays (rootSpec input).read A B := context_replays input.root A B

/-- Mixed-thread guards report all accepted identities, including both sides
of the mismatch, so their witness transfers every required comparison input. -/
theorem mixed_replays (input : Input) (A B : List Act) :
    Replays (mixedSpec input).read A B := by
  intro e fault accepted
  change mixedError input A = some e at fault
  unfold mixedError at fault
  split at fault
  · rename_i mismatch
    have same := Option.some.inj fault
    subst e
    apply (mixedSpec input).grow
    · intro act member
      exact accepted act member ⟨act,member,rfl⟩
    · change mixedError input A = some (acceptedEvidence A)
      simp [mixedError,mismatch]
  · contradiction

/-- Opener witnesses reproduce their sole-carrier conflict once the receiver
has the thread root required by this context reader. -/
theorem opener_replays (input : Input) (A B : List Act) (rooted : hasRoot B = true) :
    Replays (openerSpec input).read A B := by
  intro e fault accepted
  change openerError input A = some e at fault
  unfold openerError at fault
  split at fault
  · cases old : lift (openerContribution input) A with
    | bot | one _ _ => simp [soleError,old] at fault
    | top original =>
      have same : original = e := by simpa [soleError,old] using fault
      subst e
      have named : Accepts A (Sole.evidence (lift (openerContribution input) A)) B := by
        simpa only [old,Sole.evidence] using accepted
      have absorbed := sole_carrier_replays (openerContribution input) (by
        intro act nonempty
        unfold openerContribution at nonempty ⊢
        split
        · simp [Sole.evidence]
        · simp_all) named
      obtain ⟨enlarged,current,contains⟩ := sole_top_replays old absorbed
      exact ⟨enlarged,by simp [openerSpec,openerError,rooted,soleError,current],contains⟩
  · contradiction

/-- The factory's exact guard union preserves both replay certificates. -/
theorem join_replays (left right : ErrorSpec) (A B : List Act)
    (hl : Replays left.read A B) (hr : Replays right.read A B) :
    Replays (joinSpec left right).read A B := union_replays _ _ hl hr

/-- Context projections that do not observe openers need no extra root premise;
opener-sensitive projections explicitly require receiver root availability. -/
theorem context_spec_replays (input : Input) (observes : Bool) (A B : List Act)
    (rooted : observes = true → hasRoot B = true) : Replays (spec input observes).read A B := by
  cases observes with
  | false => exact join_replays _ _ A B (root_replays input A B) (mixed_replays input A B)
  | true =>
    exact join_replays _ _ A B (root_replays input A B)
      (join_replays _ _ A B (mixed_replays input A B) (opener_replays input A B (rooted rfl)))

/-- A faulting opener carrier contains a reported opener act. The witness is
not chosen from an unrelated root or an arbitrary accepted message. -/
theorem opener_fault_has_named_act (input : Input) (A : List Act) (e : Evidence)
    (fault : (openerSpec input).read A = some e) :
    ∃ act ∈ A, input.opener = some act.verb ∧ act.addr ∈ e := by
  classical
  change openerError input A = some e at fault
  unfold openerError at fault
  split at fault
  · cases old : lift (openerContribution input) A with
    | bot | one _ _ => simp [soleError,old] at fault
    | top original =>
      have same : original = e := by simpa [soleError,old] using fault
      subst e
      have nonempty : ∃ act ∈ A, openerContribution input act ≠ .bot := by
        apply Classical.byContradiction
        intro absent
        have allBottom : ∀ act ∈ A, openerContribution input act = .bot := by simpa using absent
        have below : lift (openerContribution input) A ⊔ (.bot : Sole) = .bot :=
          lift_join_of_forall _ (fun act member => by rw [allBottom act member]; rfl)
        rw [old] at below
        cases below
      obtain ⟨act,member,contributes⟩ := nonempty
      have selected : input.opener = some act.verb := by
        unfold openerContribution at contributes
        split at contributes
        · rename_i selected
          exact beq_iff_eq.mp selected
        · contradiction
      refine ⟨act,member,selected,?_⟩
      have contributed : act.addr ∈ Sole.evidence (openerContribution input act) := by
        simp [openerContribution,selected,Sole.evidence]
      have present := sole_member_evidence (openerContribution input) member contributed
      simpa only [old,Sole.evidence] using present
  · contradiction

/-- Protocol-level ancestry contract needed by opener-sensitive projections.
This is a structural admission premise, not a consequence of state arithmetic. -/
def RootedOpeners (world : Act → Prop) (input : Input) : Prop :=
  ∀ act, world act → input.opener = some act.verb →
    ∃ root, root.preds = [] ∧ Ancestor world root act

/-- Causal admission supplies the receiver's root by transferring a reported
opener act and its immutable ancestry. No unrelated source act is required. -/
theorem opener_replays_of_ancestry (world : Act → Prop) (input : Input)
    {A B : List Act} (valid : ∀ act ∈ A, world act)
    (closed : CausallyClosed world B) (rooted : RootedOpeners world input) :
    Replays (openerSpec input).read A B := by
  intro e fault accepted
  obtain ⟨act,member,selected,named⟩ := opener_fault_has_named_act input A e fault
  obtain ⟨root,empty,ancestor⟩ := rooted act (valid act member) selected
  have rootAccepted := ancestor_accepted closed ancestor (accepted act member named)
  have rootPresent : hasRoot B = true := (hasRoot_iff B).mpr ⟨root,rootAccepted,empty⟩
  exact opener_replays input A B rootPresent e fault accepted

/-- Every context guard replays under the explicit causal protocol contract,
without a separate assumption that the receiver already has a root. -/
theorem context_spec_replays_of_ancestry (world : Act → Prop) (input : Input)
    (observes : Bool) {A B : List Act} (valid : ∀ act ∈ A, world act)
    (closed : CausallyClosed world B) (rooted : RootedOpeners world input) :
    Replays (spec input observes).read A B := by
  cases observes with
  | false => exact join_replays _ _ A B (root_replays input A B) (mixed_replays input A B)
  | true =>
    exact join_replays _ _ A B (root_replays input A B)
      (join_replays _ _ A B (mixed_replays input A B)
        (opener_replays_of_ancestry world input valid closed rooted))

/-- Actual replica causal admission discharges history closure and validity;
only the protocol's immutable opener ancestry contract remains explicit. -/
theorem replica_context_replays {adm : AdmissionStratification.Admission} {auth : Act → Prop}
    {H : StateKernelDelivery.ValidHistory adm} (left right : StateKernelDelivery.Replica adm auth H)
    (admission : PredecessorAdmission adm H.contains) (input : Input) (observes : Bool)
    (rooted : RootedOpeners H.contains input) (n m : Nat) :
    Replays (spec input observes).read (left.run n).accepted (right.run m).accepted :=
  context_spec_replays_of_ancestry H.contains input observes
    (StateKernelDelivery.accepted_valid left n) (replica_causal_closed right admission m) rooted

/-- A delivery dependency certificate covers every cited causal predecessor.
Rank and dependency closure alone do not imply this coverage property. -/
def CausalDependencies {adm : AdmissionStratification.Admission}
    (H : StateKernelDelivery.ValidHistory adm) : Prop :=
  ∀ act, H.contains act → ∀ id ∈ act.preds,
    ∃ parent ∈ H.dependencies act, parent.addr = id

/-- Well-founded complete causal dependencies construct a predecessor-free
ancestor. This derives root ancestry instead of accepting it as a callback. -/
theorem root_ancestor {adm : AdmissionStratification.Admission}
    (H : StateKernelDelivery.ValidHistory adm) (causal : CausalDependencies H)
    (act : Act) (valid : H.contains act) :
    ∃ root, root.preds = [] ∧ Ancestor H.contains root act := by
  have reaches : ∀ n, ∀ node, H.rank node = n → H.contains node →
      ∃ root, root.preds = [] ∧ Ancestor H.contains root node := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro node equal present
      cases edges : node.preds with
      | nil => exact ⟨node,edges,.self present⟩
      | cons id rest =>
        have edge : id ∈ node.preds := by simp [edges]
        obtain ⟨parent,dependency,identity⟩ := causal node present id edge
        have lower := H.lower node present parent dependency
        obtain ⟨root,empty,path⟩ := ih (H.rank parent) (by omega) parent rfl
          (H.closed node present parent dependency)
        have parentValid := H.closed node present parent dependency
        exact ⟨root,empty,StateExecutableFreeze.ancestor_trans path
          (.step parentValid (by simpa [identity] using edge) (.self present))⟩
  exact reaches (H.rank act) act rfl valid

/-- Complete well-founded causal dependencies discharge the opener ancestry
contract for every installed context input and every opener verb. -/
theorem rooted_openers_of_dependencies {adm : AdmissionStratification.Admission}
    (H : StateKernelDelivery.ValidHistory adm) (causal : CausalDependencies H) (input : Input) :
    RootedOpeners H.contains input := by
  intro act valid selected
  exact root_ancestor H causal act valid

/-- The replica-level context certificate now derives its root premise from
causal dependency coverage and the existing fair-delivery history contract. -/
theorem replica_context_replays_of_dependencies {adm : AdmissionStratification.Admission}
    {auth : Act → Prop} {H : StateKernelDelivery.ValidHistory adm}
    (left right : StateKernelDelivery.Replica adm auth H)
    (admission : PredecessorAdmission adm H.contains) (causal : CausalDependencies H)
    (input : Input) (observes : Bool) (n m : Nat) :
    Replays (spec input observes).read (left.run n).accepted (right.run m).accepted :=
  replica_context_replays left right admission input observes
    (rooted_openers_of_dependencies H causal input) n m

end CBCL.StateContextReplay
