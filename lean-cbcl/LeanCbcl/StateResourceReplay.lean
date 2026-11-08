import LeanCbcl.StateResourceVerifier
import LeanCbcl.StateWitnessReplay

/-! Resource certificates replay from relevant facts and cited accepted context.
The transfer is on actual facts, with no hash-to-content inference. -/
set_option autoImplicit false
namespace CBCL.StateResourceReplay
open State CheckpointEvidence StateResource StateObservation StateWitnessReplay

/-- Facts named by a supported resource certificate, before address rendering. -/
def Named (config : ResourceConfig) (facts : Facts) (fact : ResourceFact) : Prop :=
  relevant config fact ∨ ∃ source ∈ facts, relevant config source ∧ cited source fact.id

/-- Every resource cause uses only relevant facts and their cited context. -/
theorem cause_replays (config : ResourceConfig) {F G : Facts}
    (transfer : ∀ fact ∈ F, Named config F fact → fact ∈ G)
    (cause : Cause config F) : Cause config G := by
  have opener : ∀ op ∈ F, initial config op → op ∈ G :=
    fun op member selected => transfer op member (Or.inl (Or.inl selected))
  have operationMem : ∀ act ∈ F, operation config act → act ∈ G :=
    fun act member selected => transfer act member (Or.inl (Or.inr (Or.inl selected)))
  have rootMem : ∀ op ∈ F, ∀ root ∈ F, initial config op → rootOf op root → root ∈ G := by
    intro op ho root hr selected parent
    change op.data.selected.predecessors = [root.id] at parent
    apply transfer root hr
    exact Or.inr ⟨op,ho,Or.inl selected,Or.inl (by simp [parent])⟩
  cases cause with
  | unsupported bad => exact .unsupported bad
  | openers ha hb ia ib different => exact .openers (opener _ ha ia) (opener _ hb ib) ia ib different
  | openerArity member selected bad => exact .openerArity (opener _ member selected) selected bad
  | initialization ho hr selected parent bad =>
    exact .initialization (opener _ ho selected) (rootMem _ ho _ hr selected parent) selected parent bad
  | malformed ho hr ha selected parent op bad =>
    exact .malformed (opener _ ho selected) (rootMem _ ho _ hr selected parent)
      (operationMem _ ha op) selected parent op bad
  | fork ho hr selected parent ha hb oa ob owner previous different =>
    exact .fork (opener _ ho selected) (rootMem _ ho _ hr selected parent) selected parent
      (operationMem _ ha oa) (operationMem _ hb ob) oa ob owner previous different
  | foreign ho hr parent ha hb selected op edge bad =>
    have foreignMem := transfer _ hb (Or.inr ⟨_,ha,Or.inr (Or.inl op),Or.inr edge⟩)
    exact .foreign (opener _ ho selected) (rootMem _ ho _ hr selected parent) parent
      (operationMem _ ha op) foreignMem selected op edge bad
  | cycle ho hr selected parent coneInside ops ha hb edge back =>
    exact .cycle (opener _ ho selected) (rootMem _ ho _ hr selected parent) selected parent
      (fun node member => operationMem node (coneInside node member) (ops node member)) ops ha hb edge back
  | budget ho hr selected parent valid coneInside cone ops bad =>
    exact .budget (opener _ ho selected) (rootMem _ ho _ hr selected parent) selected parent valid
      (fun node member => operationMem node (coneInside node member) (ops node member).1) cone ops bad

/-- Reported resource witnesses reproduce every concrete certificate, including
funding cones, foreign references and history-independent unsupported profiles. -/
theorem resource_replays (config : ResourceConfig) (decode : Act → ResourceData)
    (A B : List Act) : Replays (faultRead config decode) A B := by
  classical
  intro e fault accepted
  unfold faultRead at fault
  split at fault
  · rename_i originalFault
    have same := Option.some.inj fault
    subst e
    by_cases unsupported : config.ownership = .collective ∨ ∃ p, config.certification = .quorum p
    · refine ⟨evidence config decode B,unsupported_fault config decode B unsupported,?_⟩
      intro id member
      exact False.elim (member.1 unsupported)
    · have transfer : ∀ fact ∈ project decode A, Named config (project decode A) fact → fact ∈ project decode B := by
        intro fact member named
        obtain ⟨act,inside,rfl⟩ := List.mem_map.mp member
        have certificate : act.addr ∈ evidence config decode A := by
          refine ⟨unsupported,act,inside,rfl,?_⟩
          rcases named with relevantAct | ⟨source,sourceMember,relevantSource,citation⟩
          · exact Or.inl relevantAct
          · obtain ⟨other,otherMember,rfl⟩ := List.mem_map.mp sourceMember
            exact Or.inr ⟨other,otherMember,relevantSource,citation⟩
        exact List.mem_map.mpr ⟨act,accepted act inside certificate,rfl⟩
      have reproduced := cause_replays config transfer
        ((StateResourceVerifier.fault_iff_complete_cause config decode A).mp originalFault)
      have currentFault := (StateResourceVerifier.fault_iff_complete_cause config decode B).mpr reproduced
      refine ⟨evidence config decode B,by simp [faultRead,currentFault],?_⟩
      intro id member
      obtain ⟨supported,act,inside,identity,selection⟩ := member
      have actAccepted := accepted act inside ⟨supported,act,inside,rfl,by simpa [identity] using selection⟩
      refine ⟨supported,act,actAccepted,identity,?_⟩
      rcases selection with relevantAct | ⟨source,sourceMember,relevantSource,citation⟩
      · exact Or.inl relevantAct
      · have sourceAccepted := accepted source sourceMember
          ⟨supported,source,sourceMember,rfl,Or.inl relevantSource⟩
        exact Or.inr ⟨source,sourceAccepted,relevantSource,citation⟩
  · contradiction

/-- With concrete resource replay established, only certified extension guards
need a caller-supplied replay certificate. -/
def CertifiedReplay (A B : List Act) : Path → Prop
  | .certified spec => Replays spec.read A B
  | .join left right => CertifiedReplay A B left ∧ CertifiedReplay A B right
  | .freeze _ _ _ source => CertifiedReplay A B source
  | _ => True

/-- The concrete resource theorem discharges every resource-path obligation. -/
theorem primitive_replay (path : Path) (A B : List Act)
    (certified : CertifiedReplay A B path) : PrimitiveReplay A B path := by
  induction path with
  | certified spec => exact certified
  | resource config decode => exact resource_replays config decode A B
  | join left right ihLeft ihRight => exact ⟨ihLeft certified.1,ihRight certified.2⟩
  | freeze verb contributes policy source ih => exact ih certified
  | clear | context _ | domain _ _ | threshold _ => trivial

/-- Full closed error-path replay now requires certificates only for explicit
extension guards; built-in resource readers discharge their own obligations. -/
theorem paths_replay (world : Act → Prop) (path : Path) {A B : List Act}
    (closed : StateLVar.CausallyClosed world A) (certified : CertifiedReplay A B path) :
    Replays (errors world path) A B :=
  errors_replay world path closed (primitive_replay path A B certified)

end CBCL.StateResourceReplay
