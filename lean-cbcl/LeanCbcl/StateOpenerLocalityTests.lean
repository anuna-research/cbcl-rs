import LeanCbcl.StateOpenerLocality

/-! Structural admission-support fixtures, not literal R5/R6 verdict fixtures. -/
namespace CBCL.StateOpenerLocalityTests
open State StateLift StateLVar StateObservation StateOpenerLocality

/-- Metadata roots need not themselves be business opener acts. -/
def hello : Act := ⟨50,"hello","@a",[],[],[]⟩
/-- The domain initializer follows metadata but precedes every business writer. -/
def opener : Act := ⟨99,"open","@a",[50],[("options",.list [.str "x"])],[]⟩
/-- A writer with a matching domain value and descending numeric address. -/
def write : Act := ⟨2,"mark","@a",[99],[("target",.str "x")],[]⟩
/-- The freezer includes its writer's opener ancestry. -/
def freezerAct : Act := ⟨3,"close","@a",[2],[],[]⟩
/-- A finite, content-consistent causal base. -/
def base : List Act := [hello,opener,write,freezerAct]
/-- Reverse and duplicate delivery does not change the accepted evidence. -/
def history : List Act := base.reverse ++ base
/-- Installed protocol verbs exclude the independent metadata envelope. -/
def verbs : List String := ["open","mark","close"]

/-- The structural check accepts a metadata-rooted business history. -/
theorem metadata_root_permitted : rootedCheck history "open" verbs = true := by decide

/-- The opener carrier is local to the freezer cut by the general proof. -/
theorem initializer_local :
    initialCarrier "open" "options" (causalCut (fun act => act ∈ history) history freezerAct) = initialCarrier "open" "options" history := by
  have ranked : StateExecutableFreeze.Ranked history := StateCausalRank.causalCheck_sound history (by decide)
  have unique : NodupAddr base := by unfold NodupAddr base hello opener write freezerAct; decide
  have inside : ∀ act ∈ history, act ∈ base := by intro act member; simpa [history] using member
  have consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b :=
    fun a memberA b memberB equal => unique.eq_of_addr (inside a memberA) (inside b memberB) equal
  exact initializer_cut history "open" "options" verbs ranked metadata_root_permitted consistent
    (by rfl) freezerAct (by simp [history,base]) (by simp [verbs,freezerAct])

/-- The healthy fault-freeze case constructs its no-conflict evidence and exact
historical count, rather than assuming locality or a healthy observation. -/
theorem healthy_domain_count_local :
    FinSet.card (lift address (initialDomain "mark" "target" "open" "options"
      (causalCut (fun act => act ∈ history) history freezerAct))) = 1 := by
  classical
  have ranked : StateExecutableFreeze.Ranked history := StateCausalRank.causalCheck_sound history (by decide)
  have unique : NodupAddr base := by unfold NodupAddr base hello opener write freezerAct; decide
  have inside : ∀ act ∈ history, act ∈ base := by intro act member; simpa [history] using member
  have consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b :=
    fun a memberA b memberB equal => unique.eq_of_addr (inside a memberA) (inside b memberB) equal
  let contributes := fun act => decide (act ∈ initialDomain "mark" "target" "open" "options" history)
  have empty : (StateExecutableFreeze.conflicts history "close" contributes true).isEmpty = true := by decide
  have noConflict : ¬∃ a b, FreezeConflict (fun act => act ∈ history) "close"
      (fun act => act ∈ initialDomain "mark" "target" "open" "options" history) true history a b := by
    intro bad
    have recognized : ∃ a b, FreezeConflict (fun act => act ∈ history) "close" (fun act => contributes act = true) true history a b := by
      simpa [contributes] using bad
    have nonempty := (StateExecutableFreeze.has_conflict history ranked "close" contributes true).mpr recognized
    simp [empty] at nonempty
  have healthy : freezeFault (fun act => act ∈ history) "close"
      (fun act => act ∈ initialDomain "mark" "target" "open" "options" history) true none history = none := by
    simp [freezeFault,noConflict]
  have first : Earliest (fun act => act ∈ history) "close" history freezerAct :=
    (StateExecutableFreeze.earliest_iff history ranked "close" freezerAct).mp (by decide)
  rw [fault_domain_count history "mark" "target" "open" "options" verbs ranked metadata_root_permitted
    consistent (by rfl) "close" freezerAct first (by simp [verbs,freezerAct]) healthy]
  decide

/-- A concurrent initializer cannot repair a writer missing business ancestry. -/
def unrooted : List Act := [hello,{write with preds := [50]},freezerAct,opener]

/-- Causal rank alone is insufficient for opener locality. -/
theorem unrooted_acyclic : StateCausalRank.causalCheck unrooted = true := by decide

/-- The new local check rejects exactly the missing business-parent case. -/
theorem missing_business_parent_rejected : rootedCheck unrooted "open" verbs = false := by decide

/-- The excluded non-admission case has a full-history count of one. -/
theorem unrooted_full_count :
    FinSet.card (lift address (initialDomain "mark" "target" "open" "options" unrooted)) = 1 := by decide

/-- Its freezer cut misses the initializer, explaining why rank alone cannot
support the locality theorem. The executable cut is separately proved exact. -/
theorem unrooted_cut_count :
    FinSet.card (lift address (initialDomain "mark" "target" "open" "options" (StateExecutableFreeze.cut unrooted freezerAct))) = 0 := by decide

end CBCL.StateOpenerLocalityTests
