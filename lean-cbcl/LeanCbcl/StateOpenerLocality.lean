import LeanCbcl.StateCausalCheckComplete
import LeanCbcl.StateCountRefinement

/-! Opener support in causal cuts. An executable local predecessor check and
separate causal rank derive ancestry; callers do not supply opener ancestry.
Literal R5/R6 verdict extraction remains a separate correspondence boundary. -/
namespace CBCL.StateOpenerLocality
open State StateLift StateLVar StateObservation

/-- Every non-opener business act has a present cited business predecessor.
Metadata acts outside the installed protocol verb inventory are exempt. -/
def rootedCheck (history : List Act) (opener : String) (verbs : List String) : Bool :=
  history.all (fun act => !verbs.contains act.verb || act.verb == opener ||
    history.any (fun parent => verbs.contains parent.verb && act.preds.contains parent.addr))

/-- Local recognition constructs the predecessor needed for causal induction. -/
theorem rooted_parent (history : List Act) (opener : String) (verbs : List String) (checked : rootedCheck history opener verbs = true)
    (act : Act) (member : act ∈ history) (known : act.verb ∈ verbs) (notOpener : act.verb ≠ opener) :
    ∃ parent ∈ history, parent.verb ∈ verbs ∧ parent.addr ∈ act.preds := by
  have rowChecked := List.all_eq_true.mp checked act member
  simpa [known,notOpener,List.contains_iff_mem,List.any_eq_true] using rowChecked

/-- Every checked business vertex has an opener ancestor, derived by rank induction. -/
theorem opener_ancestor (history : List Act) (opener : String) (verbs : List String)
    (ranked : StateExecutableFreeze.Ranked history) (checked : rootedCheck history opener verbs = true)
    (act : Act) (member : act ∈ history) (known : act.verb ∈ verbs) :
    ∃ root ∈ history, root.verb = opener ∧ Ancestor (fun node => node ∈ history) root act := by
  obtain ⟨rank,ordered⟩ := ranked
  have reaches : ∀ n, ∀ node ∈ history, node.verb ∈ verbs → rank node = n →
      ∃ root ∈ history, root.verb = opener ∧ Ancestor (fun node => node ∈ history) root node := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro node present nodeKnown equal
      by_cases isOpener : node.verb = opener
      · exact ⟨node,present,isOpener,.self present⟩
      · obtain ⟨parent,parentIn,parentKnown,edge⟩ := rooted_parent history opener verbs checked node present nodeKnown isOpener
        have lower := ordered node present parent parentIn edge
        obtain ⟨root,rootIn,verb,path⟩ := ih (rank parent) (by omega) parent parentIn parentKnown rfl
        exact ⟨root,rootIn,verb,StateExecutableFreeze.ancestor_trans path (.step parentIn edge (.self present))⟩
  exact reaches (rank act) act member known rfl

/-- A clear initializer carrier permits only one content-consistent opener. -/
theorem initializer_unique (history : List Act) (opener field : String)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b)
    (clear : domainError opener field history = none)
    (a : Act) (aIn : a ∈ history) (aVerb : a.verb = opener)
    (b : Act) (bIn : b ∈ history) (bVerb : b.verb = opener) : a = b := by
  have left := join_lift_of_mem (sole field) (List.mem_filter.mpr ⟨aIn,by simpa using aVerb⟩ : a ∈ acts opener history)
  have right := join_lift_of_mem (sole field) (List.mem_filter.mpr ⟨bIn,by simpa using bVerb⟩ : b ∈ acts opener history)
  change Sole.join (.one a.addr (a.get field)) (initialCarrier opener field history) = initialCarrier opener field history at left
  change Sole.join (.one b.addr (b.get field)) (initialCarrier opener field history) = initialCarrier opener field history at right
  cases carrier : initialCarrier opener field history with
  | bot => simp [carrier,Sole.join] at left
  | top evidence => simp [domainError,carrier] at clear
  | one address value =>
    have leftAddress : a.addr = address := by
      by_cases same : a.addr = address ∧ a.get field = value
      · exact same.1
      · simp [carrier,Sole.join,same] at left
    have rightAddress : b.addr = address := by
      by_cases same : b.addr = address ∧ b.get field = value
      · exact same.1
      · simp [carrier,Sole.join,same] at right
    exact consistent a aIn b bIn (leftAddress.trans rightAddress.symm)

/-- Any accepted freezer cut contains all clear opener evidence. -/
theorem opener_cut_setEq (history : List Act) (opener field : String) (verbs : List String)
    (ranked : StateExecutableFreeze.Ranked history) (checked : rootedCheck history opener verbs = true)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b)
    (clear : domainError opener field history = none) (freezer : Act) (present : freezer ∈ history) (freezerKnown : freezer.verb ∈ verbs) :
    SetEq (acts opener (causalCut (fun act => act ∈ history) history freezer)) (acts opener history) := by
  classical
  obtain ⟨root,rootIn,rootVerb,path⟩ := opener_ancestor history opener verbs ranked checked freezer present freezerKnown
  intro act
  constructor
  · intro member
    obtain ⟨cutIn,verb⟩ := List.mem_filter.mp member
    exact List.mem_filter.mpr ⟨(List.mem_filter.mp cutIn).1,verb⟩
  · intro member
    obtain ⟨actIn,verb⟩ := List.mem_filter.mp member
    have actVerb : act.verb = opener := by simpa using verb
    have equal := initializer_unique history opener field consistent clear act actIn actVerb root rootIn rootVerb
    subst act
    exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨rootIn,decide_eq_true path⟩,verb⟩

/-- Domain initialization is exactly the same in full history and freezer cut;
this is derived support locality, not a supplied equality of observations. -/
theorem initializer_cut (history : List Act) (opener field : String) (verbs : List String)
    (ranked : StateExecutableFreeze.Ranked history) (checked : rootedCheck history opener verbs = true)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b)
    (clear : domainError opener field history = none) (freezer : Act) (present : freezer ∈ history) (freezerKnown : freezer.verb ∈ verbs) :
    initialCarrier opener field (causalCut (fun act => act ∈ history) history freezer) = initialCarrier opener field history :=
  lift_setEq _ (opener_cut_setEq history opener field verbs ranked checked consistent clear freezer present freezerKnown)

/-- The causal cut's domain filter is the full domain filter restricted to the
same ancestors. It cannot lose an initializer outside the cut. -/
theorem domain_cut (history : List Act) (verb key opener field : String) (verbs : List String)
    (ranked : StateExecutableFreeze.Ranked history) (checked : rootedCheck history opener verbs = true)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b)
    (clear : domainError opener field history = none) (freezer : Act) (present : freezer ∈ history) (freezerKnown : freezer.verb ∈ verbs) :
    initialDomain verb key opener field (causalCut (fun act => act ∈ history) history freezer) =
      (by classical exact (initialDomain verb key opener field history).filter (fun act => decide (Ancestor (fun node => node ∈ history) act freezer))) := by
  classical
  have allowed : initialAllowed opener field (causalCut (fun act => act ∈ history) history freezer) = initialAllowed opener field history := by
    unfold initialAllowed
    rw [initializer_cut history opener field verbs ranked checked consistent clear freezer present freezerKnown]
  simp only [initialDomain]
  rw [allowed]
  simp only [acts,causalCut,List.filter_filter]
  apply List.filter_congr
  intro act _
  ac_rfl

/-- Healthy fault-freeze reads retain every domain-selected contributor in the
cut, once opener support is derived from local business predecessors. -/
theorem fault_domain_cut (history : List Act) (verb key opener field : String) (verbs : List String)
    (ranked : StateExecutableFreeze.Ranked history) (checked : rootedCheck history opener verbs = true)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b)
    (clear : domainError opener field history = none) (freezeVerb : String) (freezer : Act)
    (first : Earliest (fun act => act ∈ history) freezeVerb history freezer) (freezerKnown : freezer.verb ∈ verbs)
    (healthy : freezeFault (fun act => act ∈ history) freezeVerb
      (fun act => act ∈ initialDomain verb key opener field history) true none history = none) :
    initialDomain verb key opener field (causalCut (fun act => act ∈ history) history freezer) =
      initialDomain verb key opener field history := by
  classical
  rw [domain_cut history verb key opener field verbs ranked checked consistent clear freezer first.1 freezerKnown]
  apply List.filter_eq_self.mpr
  intro act selected
  apply decide_eq_true
  apply Classical.byContradiction
  intro absent
  have present : act ∈ history := (List.mem_filter.mp (List.mem_filter.mp selected).1).1
  have conflict : FreezeConflict (fun act => act ∈ history) freezeVerb
      (fun act => act ∈ initialDomain verb key opener field history) true history freezer act :=
    .late first present selected absent rfl
  have existsConflict : ∃ a b, FreezeConflict (fun act => act ∈ history) freezeVerb
      (fun act => act ∈ initialDomain verb key opener field history) true history a b := ⟨freezer,act,conflict⟩
  simp [freezeFault,existsConflict] at healthy

/-- The raw domain count used by a threshold has the same retained carrier in
a healthy fault freezer cut as in full history under the checked premises. -/
theorem fault_domain_count (history : List Act) (verb key opener field : String) (verbs : List String)
    (ranked : StateExecutableFreeze.Ranked history) (checked : rootedCheck history opener verbs = true)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b)
    (clear : domainError opener field history = none) (freezeVerb : String) (freezer : Act)
    (first : Earliest (fun act => act ∈ history) freezeVerb history freezer) (freezerKnown : freezer.verb ∈ verbs)
    (healthy : freezeFault (fun act => act ∈ history) freezeVerb
      (fun act => act ∈ initialDomain verb key opener field history) true none history = none) :
    FinSet.card (lift address (initialDomain verb key opener field (causalCut (fun act => act ∈ history) history freezer))) =
      FinSet.card (lift address (initialDomain verb key opener field history)) := by
  rw [fault_domain_cut history verb key opener field verbs ranked checked consistent clear freezeVerb freezer first freezerKnown healthy]

/-- A reached domain-count lower bound survives growth and a later healthy
fault freeze: opener support plus contributor locality closes the raw-cut step. -/
theorem count_success_at_fault_cut (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (uniqueA : NodupAddr A) (uniqueB : NodupAddr B) (verb key opener field : String) (verbs : List String)
    (ranked : StateExecutableFreeze.Ranked B) (checked : rootedCheck B opener verbs = true)
    (clear : domainError opener field B = none) (freezeVerb : String) (freezer : Act)
    (first : Earliest (fun act => act ∈ B) freezeVerb B freezer) (freezerKnown : freezer.verb ∈ verbs)
    (healthy : freezeFault (fun act => act ∈ B) freezeVerb
      (fun act => act ∈ initialDomain verb key opener field B) true none B = none)
    (bound : Nat) (reached : bound ≤ FinSet.card (FinSet.mk (initialDomain verb key opener field A))) :
    bound ≤ FinSet.card (FinSet.mk (initialDomain verb key opener field (causalCut (fun act => act ∈ B) B freezer))) := by
  rw [fault_domain_cut B verb key opener field verbs ranked checked
    (fun a memberA b memberB equal => uniqueB.eq_of_addr memberA memberB equal) clear freezeVerb freezer first freezerKnown healthy]
  exact Nat.le_trans reached (StateCountRefinement.count_grows growth uniqueA uniqueB verb key opener field clear)

end CBCL.StateOpenerLocality
