import LeanCbcl.StateResourceLocalBudget

/-! Native budget phase iff an accepted concrete finite witness exists. The
witness cone is independently quantified; it need not be the cone reconstructed
by this traversal. Identity consistency makes both cones agree. -/
namespace CBCL.StateResourceWitness
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceStructure
open StateResourceFrontier StateResourceDependency StateResourceOwnPrefix StateResourceLocalBudget StateResourceBudget

/-- A dependency-closed operation whose causal budget is insufficient. -/
def BudgetWitness (c : ResourceConfig) (op node : ResourceFact) (known : Facts) : Prop :=
  ∃ cone, Included cone known ∧ ExactCone op node cone ∧ budgetFault c op node cone

theorem native_budget_certificate_iff (c : ResourceConfig) (op root node : ResourceFact)
    (known : Facts) (own : Summary) (cache : Cache) (cones : StateResourceCones.ConeCache)
    (tips : Nat → Tips) (prefixes : Nat → Prefixes) (parents : List (ResourceFact × Facts))
    (invariant : ParentInvariant op known cache cones tips prefixes)
    (valid : StateResourceCache.Valid op.id known cache) (ownTips : OwnTips cache cones tips)
    (lookups : StateResourceCones.gather op cones (links node) = some parents)
    (previous : previousSummary op.id cache node = some own)
    (nonforking : Nonforking known) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (unprocessed : ∀ parent ∈ parents, ∀ entry ∈ parent.2, entry.id ≠ node.id)
    (initial : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (excludesOpener : ∀ entry ∈ known, entry.id ≠ op.id)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1) :
    nativeBudgetCheck c op node own cache (mergedTips cache tips parents) = false ↔ BudgetWitness c op node known := by
  let cone := StateResourceCones.unionCone known node parents
  obtain ⟨exactCone,refinement⟩ := dependency_local_budgets_exact c op root node known own cache cones tips prefixes
    parents invariant valid ownTips lookups previous nonforking accepted unique foreignChecked unprocessed initial operations structural sliceBound
  have inside : Included cone known :=
    fun entry member => ((StateResourceCones.unionCone_member known node entry parents).mp member).1
  have uniqueCone : cone.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) exactCone.2.1
  have rejection := native_budget_rejection_iff c op root node known cone own cache (mergedTips cache tips parents)
    uniqueCone inside sliceBound operations refinement
  have identities := unique_ids_consistent known unique
  constructor
  · intro rejected
    exact ⟨cone,inside,exactCone,rejection.mp rejected⟩
  · rintro ⟨other,otherInside,otherExact,bad⟩
    apply rejection.mpr
    exact (budgetFault_cone_unique c op node otherExact exactCone
      (fun entry member => excludesOpener entry (otherInside entry member))
      (fun entry member => excludesOpener entry (inside entry member))
      (fun x hx y hy equal => identities x (otherInside x hx) y (inside y hy) equal)).mp bad

/-- A budget-phase witness is a concrete accepted resource cause, including
its actual opener/root context and validated operation shapes. -/
theorem budget_witness_cause (c : ResourceConfig) (op root node : ResourceFact) (known F : Facts)
    (opAccepted : op ∈ F) (rootAccepted : root ∈ F) (isOpener : initial c op) (parent : rootOf op root)
    (initial : validInitial c op root) (inside : Included known F)
    (operations : ∀ entry ∈ known, operation c entry ∧ validOperation c op root entry)
    (witness : BudgetWitness c op node known) : Cause c F := by
  obtain ⟨cone,coneInside,exactCone,bad⟩ := witness
  exact .budget opAccepted rootAccepted isOpener parent initial
    (fun entry member => inside entry (coneInside entry member)) exactCone
    (fun entry member => operations entry (coneInside entry member)) bad

end CBCL.StateResourceWitness
