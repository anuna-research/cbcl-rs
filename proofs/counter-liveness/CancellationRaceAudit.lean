import LeanCbcl.ConsensusFree.Liveness

/-! Research witness for CURRENT effects/fence rules. One original actor permits
both execution and cancellation; Byzantine witness 3 stays silent. -/
namespace CBCL.ConsensusFree.MultiParent.CancellationAudit
open CBCL.ValidatorBudget Liveness

private def committee : Committee 1 where
  core := [0, 1, 2]
  others := [3]
  distinct := by decide
  core_size := by decide
  other_size := by decide

def pool : Config 0 1 1 1 where
  graph := ⟨fun _ => []⟩
  committee := committee
  manifest := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => 0, true⟩
  initial := fun _ => 3
  opVersion := fun _ => 0
  cost := fun _ _ => 2
  credit := fun _ _ => 0
  authorized := fun _ => true
  cancelAuthorized := fun _ => true
  disjoint := by intros; exact Or.inr rfl

def script : List (Command 0 1) :=
  [.sign 0 0, .sign 0 1, .sign 0 2, .effect 0 0, .fence 0 1, .fence 0 2]

def stateAt (n : Nat) : State 0 1 :=
  (execute pool initial (script.take (min n 6))).getD initial

def next (n : Nat) : Command 0 1 :=
  if n < 6 then (script[n]?).getD .replay else .replay

def race : Execution pool where
  state := stateAt
  command := next
  starts := rfl
  accepted := by
    intro n
    have casesN : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
    rcases casesN with rfl | rfl | rfl | rfl | rfl | rfl | hn
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [stateAt, next, Nat.min_eq_right hn,
        Nat.min_eq_right (show 6 ≤ n+1 by omega), show ¬n < 6 by omega, perform]

example : operationCert pool (stateAt 6) 0 = true := by decide
example : finalCert pool (stateAt 6) 0 = false ∧ cancelCert pool (stateAt 6) 0 = false := by decide
example : (stateAt 6).effects 0 0 = true ∧ (stateAt 6).fences 0 1 = true ∧ (stateAt 6).fences 0 2 = true := by decide

/-- No final or cancellation certificate appears in this accepted infinite run. -/
theorem neither_outcome (n : Nat) :
    finalCert pool (race.state n) 0 = false ∧ cancelCert pool (race.state n) 0 = false := by
  have casesN : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
  rcases casesN with rfl | rfl | rfl | rfl | rfl | rfl | hn
  all_goals first | decide | simpa [race, stateAt, Nat.min_eq_right hn] using (show finalCert pool (stateAt 6) 0 = false ∧ cancelCert pool (stateAt 6) 0 = false by decide)

/-- The reservation remains charged at every honest validator. -/
example : charge pool (stateAt 6) 0 0 0 = 6 ∧ charge pool (stateAt 6) 0 1 0 = 6 ∧ charge pool (stateAt 6) 0 2 0 = 6 := by decide

/-- No honest witness can add the missing side after the split. -/
example : ∀ w : Fin 3,
    (perform pool (stateAt 6) (.effect 0 w.val)).isSome → (stateAt 6).effects 0 w.val = true := by decide
example : ∀ w : Fin 3,
    (perform pool (stateAt 6) (.fence 0 w.val)).isSome → (stateAt 6).fences 0 w.val = true := by decide
example : ∀ w : Fin 3, (perform pool (stateAt 6) (.release 0 w.val)).isSome = false := by decide

private theorem fair_after_disabled (commands : Nat → Command 0 1)
    (enabled : Nat → Prop) (action : Command 0 1)
    (disabled : ∀ n, 6 ≤ n → ¬ enabled n) : WeakFair commands enabled action := by
  intro start ready
  exact False.elim (disabled (max start 6) (Nat.le_max_right _ _)
    (ready (max start 6) (Nat.le_max_left _ _)))

private theorem honest_bound (w : Nat) (hw : w ∈ pool.committee.core) : w < 3 := by
  have casesW : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
  omega

theorem sign_fair (w : Nat) (hw : w ∈ pool.committee.core) :
    WeakFair race.command (fun n => SignEnabled pool (race.state n) 0 w) (.sign 0 w) := by
  apply fair_after_disabled
  intro n hn
  have checked : ∀ i : Fin 3, ¬ SignEnabled pool (stateAt 6) 0 i.val := by unfold SignEnabled; decide
  simpa [race, stateAt, Nat.min_eq_right hn] using checked ⟨w, honest_bound w hw⟩

theorem effect_fair (w : Nat) (hw : w ∈ pool.committee.core) :
    WeakFair race.command (fun n => EffectEnabled pool (race.state n) 0 w) (.effect 0 w) := by
  apply fair_after_disabled
  intro n hn
  have checked : ∀ i : Fin 3, ¬ EffectEnabled pool (stateAt 6) 0 i.val := by unfold EffectEnabled; decide
  simpa [race, stateAt, Nat.min_eq_right hn] using checked ⟨w, honest_bound w hw⟩

/-- Fairness for new cancellation fences also holds: each honest witness has
already fenced or permanently executed. -/
def FenceEnabled (s : State 0 1) (w : Nat) : Prop :=
  s.fences 0 w = false ∧ s.effects 0 w = false ∧ pool.cancelAuthorized 0 = true

theorem fence_fair (w : Nat) (hw : w ∈ pool.committee.core) :
    WeakFair race.command (fun n => FenceEnabled (race.state n) w) (.fence 0 w) := by
  apply fair_after_disabled
  intro n hn
  have checked : ∀ i : Fin 3, ¬ FenceEnabled (stateAt 6) i.val := by unfold FenceEnabled; decide
  simpa [race, stateAt, Nat.min_eq_right hn] using checked ⟨w, honest_bound w hw⟩

#print axioms race
#print axioms neither_outcome
#print axioms sign_fair
#print axioms effect_fair
#print axioms fence_fair
end CBCL.ConsensusFree.MultiParent.CancellationAudit
