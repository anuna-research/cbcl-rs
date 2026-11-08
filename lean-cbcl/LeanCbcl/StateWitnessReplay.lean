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

end CBCL.StateWitnessReplay
