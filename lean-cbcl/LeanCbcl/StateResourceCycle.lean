import LeanCbcl.StateResourceKahn

/-! Structural native resource-cycle rejection iff a concrete accepted cycle
certificate exists. Initialization/role/shape checks precede this phase; its
certificate adapter carries those actual opener/root identities explicitly. -/
namespace CBCL.StateResourceCycle
open State CheckpointEvidence StateResource

/-- Recognize a configured resource operation verb. -/
def operationVerbCheck (c : ResourceConfig) (verb : String) : Bool :=
  verb == c.increment.verb || verb == c.decrement.verb ||
    c.transfer.any (fun t => verb == t.verb) || c.transferHeadroom.any (fun t => verb == t.verb)

theorem operationVerbCheck_iff (c : ResourceConfig) (node : ResourceFact) :
    operationVerbCheck c node.data.selected.verb = true ↔ operation c node := by
  simp [operationVerbCheck,operation,Option.any_eq_true,or_assoc]

/-- Select the recognized resource operations from accepted facts. -/
def nodes (c : ResourceConfig) (F : Facts) : Facts := F.filter (fun f => operationVerbCheck c f.data.selected.verb)

/-- The dependency identities used by this module's graph traversal. -/
def parents (known : Facts) (node : ResourceFact) : Facts :=
  known.filter (fun parent => (links node).contains parent.id)

theorem parent_iff (known : Facts) (node parent : ResourceFact) :
    parent ∈ parents known node ↔ parent ∈ known ∧ parent.id ∈ links node := by
  simp [parents]

theorem reaches_mono {C F : Facts} (inside : Included C F) {a b : ResourceFact}
    (path : Reaches C a b) : Reaches F a b := by
  induction path with
  | refl => exact .refl
  | step member edge _ ih => exact .step (inside _ member) edge ih

theorem native_reach_resource {F : Facts} {a b : ResourceFact}
    (path : StateResourceKahn.Reach (parents F) F a b) : Reaches F a b := by
  induction path with
  | edge _ hb link => exact .step hb ((parent_iff F _ _).mp link).2 .refl
  | cons _ link _ ih =>
    have member := (parent_iff F _ _).mp link
    exact .step member.1 member.2 ih

theorem resource_reach_extend {F : Facts} {a b : ResourceFact} (path : Reaches F a b)
    {root : ResourceFact} (initial : StateResourceKahn.Reach (parents F) F root a) :
    StateResourceKahn.Reach (parents F) F root b := by
  induction path with
  | refl => exact initial
  | @step a parent b member link _ ih =>
    exact ih (initial.trans (.edge initial.target member ((parent_iff F a parent).mpr ⟨member,link⟩)))

/-- A finite certificate of a cycle among accepted resource operations. -/
def CycleCertificate (c : ResourceConfig) (F : Facts) : Prop :=
  ∃ C a b, Included C F ∧ (∀ node ∈ C, operation c node) ∧
    a ∈ C ∧ b ∈ C ∧ b.id ∈ links a ∧ Reaches C b a

theorem graph_cycle_iff_certificate (c : ResourceConfig) (F : Facts) :
    StateResourceKahn.HasCycle (parents (nodes c F)) (nodes c F) ↔ CycleCertificate c F := by
  constructor
  · rintro ⟨node,path⟩
    have inside : Included (nodes c F) F := fun _ h => (List.mem_filter.mp h).1
    have operations : ∀ node ∈ nodes c F, operation c node :=
      fun n hn => (operationVerbCheck_iff c n).mp (List.mem_filter.mp hn).2
    cases path with
    | edge source target link =>
      exact ⟨nodes c F,node,node,inside,operations,source,target,((parent_iff _ _ _).mp link).2,.refl⟩
    | @cons _ parent _ source link back =>
      exact ⟨nodes c F,node,parent,inside,operations,source,back.source,
        ((parent_iff _ _ _).mp link).2,native_reach_resource back⟩
  · rintro ⟨C,a,b,inside,operations,ha,hb,link,back⟩
    have subset : Included C (nodes c F) := by
      intro node member
      exact List.mem_filter.mpr ⟨inside node member,(operationVerbCheck_iff c node).mpr (operations node member)⟩
    have first : StateResourceKahn.Reach (parents (nodes c F)) (nodes c F) a b :=
      .edge (subset a ha) (subset b hb) ((parent_iff _ _ _).mpr ⟨subset b hb,link⟩)
    exact ⟨a,resource_reach_extend (reaches_mono subset back) first⟩

/-- The native structural cycle check. -/
def nativeCycleCheck (c : ResourceConfig) (F : Facts) : Bool :=
  (StateResourceKahn.nativeKahn (parents (nodes c F)) (nodes c F)).isEmpty

/-- Complete executable structural phase, not an assumed cycle oracle. -/
theorem native_cycle_certificate_iff (c : ResourceConfig) (F : Facts) :
    nativeCycleCheck c F = false ↔ CycleCertificate c F := by
  rw [← graph_cycle_iff_certificate]
  simpa [nativeCycleCheck] using StateResourceKahn.nativeKahn_cycle_iff (parents (nodes c F)) (nodes c F)

theorem native_cycle_rejection_cause (c : ResourceConfig) (F : Facts) (op root : ResourceFact)
    (opAccepted : op ∈ F) (rootAccepted : root ∈ F) (opener : initial c op) (parent : rootOf op root)
    (rejected : nativeCycleCheck c F = false) : Cause c F := by
  obtain ⟨C,a,b,inside,operations,ha,hb,link,back⟩ := (native_cycle_certificate_iff c F).mp rejected
  exact .cycle opAccepted rootAccepted opener parent inside operations ha hb link back

end CBCL.StateResourceCycle
