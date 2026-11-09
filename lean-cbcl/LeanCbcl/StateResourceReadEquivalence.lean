import LeanCbcl.StateResourceVerifier
import LeanCbcl.StateResourceCompletion

/-! Full typed resource read equivalence under accepted-fact permutation.
Completion uses dependency closure; successful payloads use exact account
folds, including headroom. Preflight pending is tied to absent metadata rather
than treated as an opaque classifier outcome. -/
namespace CBCL.StateResourceReadEquivalence
open State CheckpointEvidence StateResource StateResourceVerifier StateResourcePreflight
open StateResourceWorklist StateResourceAggregate StateResourceCompletion

theorem accepted_root_prevents_pending (input : Input) (op root : ResourceFact)
    (opAccepted : op ∈ input.facts) (rootAccepted : root ∈ input.facts)
    (selected : initial input.config op) (linked : rootOf op root) (noCause : ¬Cause input.config input.facts) :
    prepare input ≠ .pending noCause := by
  intro pending
  unfold prepare at pending
  dsimp only at pending
  split at pending
  · contradiction
  · try dsimp only at pending
    split at pending
    · rename_i empty
      have inside := (initial_member input.config input.facts op).mpr ⟨opAccepted,selected⟩
      rw [empty] at inside
      contradiction
    · rename_i actual openers
      have inside := (initial_member input.config input.facts op).mpr ⟨opAccepted,selected⟩
      rw [openers] at inside
      have equal : op = actual := List.mem_singleton.mp inside
      subst actual
      have lookup := StateResourceGraph.lookup_known input.facts input.unique root rootAccepted
      change op.data.selected.predecessors = [root.id] at linked
      split at pending
      · contradiction
      · rename_i address predecessors
        have identity : address = root.id := by simpa [predecessors] using linked
        subst address
        split at pending
        · rename_i absent
          rw [lookup] at absent
          contradiction
        · repeat' first | split at pending | contradiction
      · contradiction
    · contradiction

theorem checked_of_root_and_no_cause (input : Input) (op root : ResourceFact)
    (opAccepted : op ∈ input.facts) (rootAccepted : root ∈ input.facts)
    (selected : initial input.config op) (linked : rootOf op root) (noCause : ¬Cause input.config input.facts) :
    ∃ prepared, prepare input = .checked prepared := by
  cases result : prepare input with
  | fault certificate => exact False.elim (noCause certificate)
  | pending absent => exact False.elim (accepted_root_prevents_pending input op root opAccepted rootAccepted selected linked absent result)
  | checked prepared => exact ⟨prepared,rfl⟩

theorem observe_fault_iff_cause (input : Input) : observe input = .fault ↔ Cause input.config input.facts := by
  rw [← native_verifier_certificate_iff]
  cases observe input <;> simp [StateResourceValidated.isFault]

/-- Full typed native read equivalence, not just its fault classifier. Literal
ready values, rights and headroom functions agree; missing metadata and open
cones remain pending on both permutations. -/
theorem native_observe_perm (left right : Input) (config : left.config = right.config)
    (same : left.facts.Perm right.facts) : observe left = observe right := by
  have causeEquiv : Cause left.config left.facts ↔ Cause right.config right.facts := by
    rw [config]
    exact ⟨cause_mono right.config (fun node member => same.mem_iff.mp member),
      cause_mono right.config (fun node member => same.mem_iff.mpr member)⟩
  by_cases cause : Cause left.config left.facts
  · rw [(observe_fault_iff_cause left).mpr cause,(observe_fault_iff_cause right).mpr (causeEquiv.mp cause)]
  · have noRight : ¬Cause right.config right.facts := fun witness => cause (causeEquiv.mpr witness)
    cases lp : prepare left with
    | fault certificate => exact False.elim (cause certificate)
    | pending absent =>
      cases rp : prepare right with
      | fault certificate => exact False.elim (noRight certificate)
      | pending _ => simp [observe,lp,rp]
      | checked q =>
        have selected : initial left.config q.opener := by simpa [config] using q.isOpener
        exact False.elim (accepted_root_prevents_pending left q.opener q.root
          (same.mem_iff.mpr q.openerAccepted) (same.mem_iff.mpr q.rootAccepted) selected q.rootLink absent lp)
    | checked p =>
      have selected : initial right.config p.opener := by simpa [← config] using p.isOpener
      obtain ⟨q,rp⟩ := checked_of_root_and_no_cause right p.opener p.root
        (same.mem_iff.mp p.openerAccepted) (same.mem_iff.mp p.rootAccepted) selected p.rootLink noRight
      obtain ⟨sameOp,_⟩ := q.root_unique right.unique p.opener p.root
        (same.mem_iff.mp p.openerAccepted) (same.mem_iff.mp p.rootAccepted) selected p.rootLink
      have leftProfile := left.installed p.supported
      have rightProfile := right.installed q.supported
      let el := p.environment left.unique (List.nodup_cons.mp leftProfile.2).1 left.sliceBound
      let er := q.environment right.unique (List.nodup_cons.mp rightProfile.2).1 right.sliceBound
      have sameKnown : el.known.Perm er.known := by
        change (StateResourceCycle.nodes left.config left.facts).Perm (StateResourceCycle.nodes right.config right.facts)
        simpa [StateResourceCycle.nodes,config] using same.filter (fun node => StateResourceCycle.operationVerbCheck right.config node.data.selected.verb)
      have equal := validated_observe_perm el er config sameOp sameKnown leftProfile.1 rightProfile.1
        (left.accountSlice p.opener p.openerAccepted) (right.accountSlice q.opener q.openerAccepted)
      simpa [observe,lp,rp,el,er] using equal

end CBCL.StateResourceReadEquivalence
