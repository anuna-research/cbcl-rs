import LeanCbcl.StateProgressStore
import LeanCbcl.StateNativeDataFreeze

/-! Single-verb causal positions survive restriction to a healthy progress
freeze cut. The immutable decoder must preserve wire verbs: a noncontributor
cannot secretly supply a position for the contributing verb. -/
set_option autoImplicit false
namespace CBCL.StateProgressLocality
open State StateLVar StateProgressStore StateKernelExtensions

/-- Verb-restricted history inclusion preserves exactly the causal evidence
whose decoded verb contributes to this progress source. -/
theorem verb_lookup (decode : Act → Repeat.Evidence) (verb : String) (A B : List Act)
    (coherent : ∀ act, (decode act).verb = act.verb)
    (inside : ∀ act ∈ A, act.verb = verb → act ∈ B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (address : Nat) (evidence : Repeat.Evidence) (verbEq : evidence.verb = verb)
    (found : store decode A address = some evidence) : store decode B address = some evidence := by
  obtain ⟨act,member,addressEq,decoded⟩ := origin decode A address evidence found
  have actVerb : act.verb = verb := (coherent act).symm.trans ((congrArg Repeat.Evidence.verb decoded).trans verbEq)
  rw [← addressEq,lookup decode B consistent act (inside act member actVerb),decoded]

/-- A genuine causal-position witness has an actual retained source act at its
address, with the source verb. This is derived from evidence, not assumed. -/
theorem at_origin (decode : Act → Repeat.Evidence) (verb : String) (A : List Act)
    (coherent : ∀ act, (decode act).verb = act.verb) (thread limit address position : Nat)
    (established : Repeat.At (store decode A) thread verb limit address position) :
    ∃ act, act ∈ A ∧ act.addr = address ∧ act.verb = verb := by
  have evidence : ∃ item, store decode A address = some item ∧ item.verb = verb := by
    cases established with
    | first _ found _ => exact ⟨_,found,rfl⟩
    | next _ _ _ found _ _ => exact ⟨_,found,rfl⟩
  obtain ⟨item,found,verbEq⟩ := evidence
  obtain ⟨act,member,addressEq,decoded⟩ := origin decode A address item found
  exact ⟨act,member,addressEq,(coherent act).symm.trans ((congrArg Repeat.Evidence.verb decoded).trans verbEq)⟩

/-- Transfer every node of an established repeated-verb chain. General store
extension is unnecessary: unrelated metadata may legitimately lie outside a cut. -/
theorem at_transfer (decode : Act → Repeat.Evidence) (verb : String) (A B : List Act)
    (coherent : ∀ act, (decode act).verb = act.verb)
    (inside : ∀ act ∈ A, act.verb = verb → act ∈ B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (thread limit address position : Nat)
    (established : Repeat.At (store decode A) thread verb limit address position) :
    Repeat.At (store decode B) thread verb limit address position := by
  induction established with
  | first address found positive =>
    exact .first address (verb_lookup decode verb A B coherent inside consistent address _ rfl found) positive
  | next address parent rank found previous within ih =>
    exact .next address parent rank (verb_lookup decode verb A B coherent inside consistent address _ rfl found) ih within

/-- Restricting history while retaining all contributing-verb acts cannot lower
progress. The proof transfers actual causal-position witnesses at every step. -/
theorem progress_restricted (decode : Act → Repeat.Evidence) (verb : String) (A B : List Act)
    (coherent : ∀ act, (decode act).verb = act.verb)
    (inside : ∀ act ∈ A, act.verb = verb → act ∈ B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) (thread limit : Nat) :
    protocolProgress (store decode A) thread verb limit A ≤ protocolProgress (store decode B) thread verb limit B := by
  apply (progress_correct (store decode A) thread verb limit A _).mpr
  intro act member position established
  obtain ⟨source,accepted,addressEq,sourceVerb⟩ := at_origin decode verb A coherent thread limit act.addr position established
  have transferred := at_transfer decode verb A B coherent inside consistent thread limit act.addr position established
  have bounds := (progress_correct (store decode B) thread verb limit B _).mp (Nat.le_refl _) source
    (inside source accepted sourceVerb) position
  exact bounds (addressEq ▸ transferred)

end CBCL.StateProgressLocality
