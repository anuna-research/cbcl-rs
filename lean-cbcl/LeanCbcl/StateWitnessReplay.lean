import LeanCbcl.StateEvidenceSupport

/-! Replay transfers the actual accepted acts selected by reported identities.
Address-to-act binding and admissible context remain explicit at callers. -/
set_option autoImplicit false
namespace CBCL.StateWitnessReplay
open State StateLift StateLVar StateObservation

/-- The receiver accepts every original act named by the reported evidence.
This deliberately uses actual act membership rather than unproved hash equality. -/
def Accepts (A : List Act) (e : Evidence) (B : List Act) : Prop :=
  ∀ act ∈ A, act.addr ∈ e → act ∈ B

/-- A reader's reported evidence suffices to reproduce and retain its fault. -/
def Replays (read : List Act → Error) (A B : List Act) : Prop :=
  ∀ e, read A = some e → Accepts A e B →
    ∃ enlarged, read B = some enlarged ∧ ∀ id ∈ e, id ∈ enlarged

/-- A receiver holding a union certificate holds each component's acts. -/
theorem accepts_union_left {A B : List Act} {left right : Evidence}
    (accepted : Accepts A (left ∪ right) B) : Accepts A left B :=
  fun act member evidence => accepted act member (Or.inl evidence)

/-- The right component is likewise retained by a union certificate. -/
theorem accepts_union_right {A B : List Act} {left right : Evidence}
    (accepted : Accepts A (left ∪ right) B) : Accepts A right B :=
  fun act member evidence => accepted act member (Or.inr evidence)

/-- Every freeze conflict pair reproduces from its reported acts, without
requiring the receiver to accept the rest of the source history. -/
theorem freeze_evidence_replays (world : Act → Prop) (verb : String)
    (contributes : Act → Prop) (policy : Bool) {A B : List Act}
    (closed : CausallyClosed world A)
    (accepted : Accepts A (freezeEvidence world verb contributes policy A) B) :
    ∀ id ∈ freezeEvidence world verb contributes policy A,
      id ∈ freezeEvidence world verb contributes policy B := by
  rintro id ⟨a,b,conflict,which⟩
  have original := freeze_witness_accepted conflict
  have left := accepted a original.1 ⟨a,b,conflict,Or.inl rfl⟩
  have right := accepted b original.2 ⟨a,b,conflict,Or.inr rfl⟩
  exact ⟨a,b,freeze_witness_transfer closed conflict left right,which⟩

/-- Independent replayable guard channels compose without discarding either
certificate. Additional receiver faults may enlarge the union. -/
theorem union_replays (left right : List Act → Error) {A B : List Act}
    (hl : Replays left A B) (hr : Replays right A B) :
    Replays (fun history => unionError (left history) (right history)) A B := by
  intro e fault accepted
  cases la : left A with
  | none =>
    cases ra : right A with
    | none => simp [la,ra,unionError] at fault
    | some old =>
      have same : old = e := by simpa [la,ra,unionError] using fault
      subst e
      obtain ⟨later,current,contains⟩ := hr old ra accepted
      cases lb : left B with
      | none => exact ⟨later,by simp [lb,current,unionError],contains⟩
      | some other => exact ⟨other ∪ later,by simp [lb,current,unionError],fun id member => Or.inr (contains id member)⟩
  | some first =>
    cases ra : right A with
    | none =>
      have same : first = e := by simpa [la,ra,unionError] using fault
      subst e
      obtain ⟨later,current,contains⟩ := hl first la accepted
      cases rb : right B with
      | none => exact ⟨later,by simp [current,rb,unionError],contains⟩
      | some other => exact ⟨later ∪ other,by simp [current,rb,unionError],fun id member => Or.inl (contains id member)⟩
    | some second =>
      have same : first ∪ second = e := by simpa [la,ra,unionError] using fault
      subst e
      obtain ⟨laterLeft,currentLeft,containsLeft⟩ := hl first la (accepts_union_left accepted)
      obtain ⟨laterRight,currentRight,containsRight⟩ := hr second ra (accepts_union_right accepted)
      exact ⟨laterLeft ∪ laterRight,by simp [currentLeft,currentRight,unionError],
        fun id member => member.elim (fun h => Or.inl (containsLeft id h)) (fun h => Or.inr (containsRight id h))⟩

/-- Freeze decoration composes with replayable raw errors. Its own conflict
pairs need only their named accepted acts; the entire source history is absent
from the receiver premise. -/
theorem freeze_replays (world : Act → Prop) (verb : String)
    (contributes : Act → Prop) (policy : Bool) (raw : List Act → Error)
    {A B : List Act} (closed : CausallyClosed world A) (replay : Replays raw A B) :
    Replays (fun history => freezeFault world verb contributes policy (raw history) history) A B := by
  classical
  intro e fault accepted
  dsimp only at fault ⊢
  unfold freezeFault at fault ⊢
  split at fault
  · rename_i reason
    have same := Option.some.inj fault
    subst e
    have rawAccepted := accepts_union_left accepted
    have freezeAccepted := accepts_union_right accepted
    have freezeGrows := freeze_evidence_replays world verb contributes policy closed freezeAccepted
    have rawGrows : ∀ old, raw A = some old → ∃ later, raw B = some later ∧ ∀ id ∈ old, id ∈ later := by
      intro old observed
      apply replay old observed
      simpa [observed] using rawAccepted
    have currentReason : (raw B).isSome ∨ ∃ a b, FreezeConflict world verb contributes policy B a b := by
      rcases reason with rawFault | ⟨a,b,conflict⟩
      · cases observed : raw A with
        | none => simp [observed] at rawFault
        | some old =>
          obtain ⟨later,current,_⟩ := rawGrows old observed
          exact Or.inl (by simp [current])
      · have original := freeze_witness_accepted conflict
        exact Or.inr ⟨a,b,freeze_witness_transfer closed conflict
          (freezeAccepted a original.1 ⟨a,b,conflict,Or.inl rfl⟩)
          (freezeAccepted b original.2 ⟨a,b,conflict,Or.inr rfl⟩)⟩
    refine ⟨(raw B).getD ∅ ∪ freezeEvidence world verb contributes policy B,if_pos currentReason,?_⟩
    intro id member
    rcases member with rawMember | freezeMember
    · cases observed : raw A with
      | none =>
        have impossible : id ∈ (∅ : Evidence) := by simpa [observed] using rawMember
        exact False.elim impossible
      | some old =>
        obtain ⟨later,current,contains⟩ := rawGrows old observed
        exact Or.inl (by simpa [current] using contains id (by simpa [observed] using rawMember))
    · exact Or.inr (freezeGrows id freezeMember)
  · contradiction

/-- Any evidence contributed by an accepted act survives its carrier join. -/
theorem sole_member_evidence (contribution : Act → Sole) {A : List Act}
    {act : Act} (member : act ∈ A) {id : Nat}
    (evidence : id ∈ Sole.evidence (contribution act)) :
    id ∈ Sole.evidence (lift contribution A) := by
  have absorbed := join_lift_of_mem contribution member
  rw [← absorbed,sole_evidence_join]
  exact Or.inl evidence

/-- Named non-bottom contributions suffice to reproduce the entire sole-value
carrier. Unnamed bottom contributions need not be delivered. -/
theorem sole_carrier_replays (contribution : Act → Sole)
    (identity : ∀ act, contribution act ≠ .bot → act.addr ∈ Sole.evidence (contribution act))
    {A B : List Act} (accepted : Accepts A (Sole.evidence (lift contribution A)) B) :
    lift contribution A ⊔ lift contribution B = lift contribution B := by
  apply lift_join_of_forall
  intro act member
  by_cases empty : contribution act = .bot
  · rw [empty]
    exact bot_join _
  · exact join_lift_of_mem contribution (accepted act member
      (sole_member_evidence contribution member (identity act empty)))

/-- A reproduced top carrier retains every original reported identity. -/
theorem sole_top_replays {old current : Sole} {e : Evidence}
    (observed : old = .top e) (absorbed : old ⊔ current = current) :
    ∃ enlarged, current = .top enlarged ∧ ∀ id ∈ e, id ∈ enlarged := by
  rw [observed] at absorbed
  change Sole.join (.top e) current = current at absorbed
  cases current with
  | bot | one _ _ => simp [Sole.join] at absorbed
  | top enlarged =>
    have same : e ∪ enlarged = enlarged := by simpa [Sole.join] using absorbed
    refine ⟨enlarged,rfl,?_⟩
    intro id member
    rw [← same]
    exact Or.inl member

/-- Checked thresholds report every accepted address on conflict, so their
reported witness already transfers the complete required carrier context. -/
theorem threshold_replays (spec : ThresholdSpec) (A B : List Act) :
    Replays (thresholdError spec) A B := by
  classical
  intro e fault accepted
  unfold thresholdError at fault
  split at fault
  · rename_i conflict
    have same := Option.some.inj fault
    subst e
    have includes : ∀ act ∈ A, act ∈ B := by
      intro act member
      exact accepted act member ⟨act,member,rfl⟩
    exact errors_persist (fun _ => False) (.threshold spec)
      (by intro child member parent impossible edge; contradiction) includes _ (by simp [errors,thresholdError,conflict])
  · contradiction

/-- Initializer faults replay from the reported opener acts. Other accepted
verbs contribute nothing and need not be delivered. -/
theorem domain_replays (opener field : String) (A B : List Act) :
    Replays (domainError opener field) A B := by
  intro e fault accepted
  cases old : initialCarrier opener field A with
  | bot | one _ _ => simp [domainError,old] at fault
  | top original =>
    have same : original = e := by simpa [domainError,old] using fault
    subst e
    have includes : ∀ act ∈ acts opener A, act ∈ acts opener B := by
      intro act member
      have source := List.mem_filter.mp member
      have verb : act.verb = opener := by simpa using source.2
      have evidence : act.addr ∈ original := by
        have inside := (opener_evidence opener field A act.addr).mpr ⟨act,source.1,verb,rfl⟩
        simpa [old,Sole.evidence] using inside
      exact List.mem_filter.mpr ⟨accepted act source.1 evidence,source.2⟩
    have absorbed : initialCarrier opener field A ⊔ initialCarrier opener field B = initialCarrier opener field B :=
      lift_join_of_forall (sole field) (fun act member => join_lift_of_mem _ (includes act member))
    obtain ⟨enlarged,current,contains⟩ := sole_top_replays old absorbed
    exact ⟨enlarged,by simp [domainError,current],contains⟩

/-- Root-context faults replay from their reported roots, including the single
malformed-root case. No unrelated application act is required. -/
theorem context_replays (decode : Act → Option Val) (A B : List Act) :
    Replays (fun history => contextError (StateContext.read decode history)) A B := by
  intro e fault accepted
  have observed : StateContext.read decode A = .fault e := by
    cases current : StateContext.read decode A with
    | pending | value _ => simp [current,contextError] at fault
    | fault original =>
      have same : original = e := by simpa [current,contextError] using fault
      simpa [same] using current
  have evidence : e = Sole.evidence (lift (StateContext.contribution decode) A) := StateContext.fault_evidence observed
  have acceptedRoots : Accepts A (Sole.evidence (lift (StateContext.contribution decode) A)) B := by
    rw [← evidence]
    exact accepted
  have absorbed := sole_carrier_replays (StateContext.contribution decode) (by
    intro act nonempty
    unfold StateContext.contribution at nonempty ⊢
    split
    · simp [Sole.evidence]
    · simp_all) acceptedRoots
  obtain ⟨enlarged,current,contains⟩ := StateContext.fault_join
    (b := StateContext.carrier decode B) observed
  change StateContext.display (lift (StateContext.contribution decode) A ⊔
    lift (StateContext.contribution decode) B) = .fault enlarged at current
  rw [absorbed] at current
  exact ⟨enlarged,by simp [StateContext.read,StateContext.carrier,current,contextError],contains⟩

/-- Remaining primitive obligations for a closed observation path. Concrete
certified guards and resource readers must prove replay in admissible context;
all other constructors have structural replay laws. -/
def PrimitiveReplay (A B : List Act) : Path → Prop
  | .certified spec => Replays spec.read A B
  | .resource config decode => Replays (StateResource.faultRead config decode) A B
  | .join left right => PrimitiveReplay A B left ∧ PrimitiveReplay A B right
  | .freeze _ _ _ source => PrimitiveReplay A B source
  | _ => True

/-- All observation paths compose witness replay from their concrete extension
and resource certificates. Source causal closure supports freeze witnesses. -/
theorem errors_replay (world : Act → Prop) (path : Path) {A B : List Act}
    (closed : CausallyClosed world A) (primitive : PrimitiveReplay A B path) :
    Replays (errors world path) A B := by
  induction path with
  | clear => intro e impossible accepted; contradiction
  | certified spec => exact primitive
  | context decode => exact context_replays decode A B
  | domain opener field => exact domain_replays opener field A B
  | resource config decode => exact primitive
  | threshold spec => exact threshold_replays spec A B
  | join left right ihLeft ihRight =>
    exact union_replays _ _ (ihLeft primitive.1) (ihRight primitive.2)
  | freeze verb contributes policy source ih =>
    exact freeze_replays world verb contributes policy _ closed (ih primitive)

end CBCL.StateWitnessReplay
