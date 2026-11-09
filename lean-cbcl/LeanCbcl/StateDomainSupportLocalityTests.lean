import LeanCbcl.StateDomainSupportLocality
import LeanCbcl.StateCausalRank

/-! Domain-support fixtures cover mixed initializer/roster domains, actual
healthy selection locality, and the admitted-regression graph's missing support. -/
namespace CBCL.StateDomainSupportLocalityTests
open State StateLift StateLVar StateObservation StateInstalledDomains StateDomainSupportLocality

/-- A sealed metadata root. -/
def root : Act := ⟨50,"hello","@a",[],[],[]⟩
/-- Initializer evidence is separate from the selected writer. -/
def opener : Act := ⟨99,"open","@a",[50],[("options",.list [.str "@a"])],[]⟩
/-- A writer depending on the initializer in the healthy case. -/
def writer : Act := ⟨2,"mark","@a",[99],[("target",.str "@a")],[]⟩
/-- The historical observation root. -/
def freezer : Act := ⟨3,"close","@a",[2],[],[]⟩
/-- A profile with actual immutable sealed-role metadata. -/
def profile : StateInstalledContext.Profile := {
  definition := ⟨"review","dialect","body",some "@a",[⟨"reviewer",true⟩],⟨32,64,1000000,2048⟩,some "open"⟩
  metadata := fun address => ⟨some "t",if address == 50 then .value [⟨"reviewer",["@a"]⟩] else .absent,.absent⟩
  address := fun _ => "address" }
/-- The count depends on both an initializer list and a sealed roster. -/
def domains : List Domain := [⟨"mark","target",.initial "open" "options"⟩,⟨"mark","target",.roster profile "reviewer"⟩]
/-- Duplicate reverse delivery of a complete support chain. -/
def history : List Act := [freezer,writer,opener,root,freezer,writer,opener,root]
/-- Fixed source footprint generated from these concrete domains. -/
def footprint : Act → Prop := StateAuthoredBindings.contributes domains history (.verbs ["mark"])

/-- Initializer support is retained independently of writer eligibility. -/
theorem initializer_contributes : footprint opener :=
  Or.inr ⟨⟨"mark","target",.initial "open" "options"⟩,by simp [domains],by simp,opener,by simp [history],rfl,rfl⟩

/-- Sealed roster roots are retained by the same source footprint. -/
theorem roster_root_contributes : footprint root :=
  Or.inr ⟨⟨"mark","target",.roster profile "reviewer"⟩,by simp [domains],by simp,root,by simp [history],rfl,rfl⟩

/-- The healthy mixed-domain fixture constructs freeze health, not its result. -/
theorem healthy : freezeFault (fun act => act ∈ history) "close" footprint true none history = none := by
  classical
  have ranked : StateExecutableFreeze.Ranked history := StateCausalRank.causalCheck_sound history (by decide)
  have empty : (StateExecutableFreeze.conflicts history "close" (fun _ => true) true).isEmpty = true := by decide
  have noConflict : ¬∃ a b, FreezeConflict (fun act => act ∈ history) "close" footprint true history a b := by
    rintro ⟨a,b,bad⟩
    have general : FreezeConflict (fun act => act ∈ history) "close" (fun _ => true = true) true history a b := by
      cases bad with
      | concurrent left right different => exact .concurrent left right different
      | late first present _ absent policy => exact .late first present rfl absent policy
    have nonempty := (StateExecutableFreeze.has_conflict history ranked "close" (fun _ => true) true).mpr ⟨a,b,general⟩
    simp [empty] at nonempty
  simp [freezeFault,noConflict]

/-- The general theorem yields the actual historical count under both domains. -/
theorem mixed_domain_count_local :
    FinSet.card (FinSet.mk (selected domains ["mark"] (causalCut (fun act => act ∈ history) history freezer))) = 1 := by
  have ranked : StateExecutableFreeze.Ranked history := StateCausalRank.causalCheck_sound history (by decide)
  have first := (StateExecutableFreeze.earliest_iff history ranked "close" freezer).mp (by decide)
  rw [selected_cut domains ["mark"] history "close" freezer first healthy]
  decide

/-- The writer can instead reference the metadata root, bypassing the opener. -/
def branch : List Act := [root,opener,{writer with preds := [50]},freezer]

/-- Missing initializer support is now a real fault witness rather than a
healthy historical read that could retract a previously reached threshold. -/
theorem branch_faults : (freezeFault (fun act => act ∈ branch) "close"
    (StateAuthoredBindings.contributes domains branch (.verbs ["mark"])) true none branch).isSome = true := by
  classical
  have ranked : StateExecutableFreeze.Ranked branch := StateCausalRank.causalCheck_sound branch (by decide)
  have first := (StateExecutableFreeze.earliest_iff branch ranked "close" freezer).mp (by decide)
  have contributes : StateAuthoredBindings.contributes domains branch (.verbs ["mark"]) opener :=
    Or.inr ⟨⟨"mark","target",.initial "open" "options"⟩,by simp [domains],by simp,opener,by simp [branch],rfl,rfl⟩
  have absent : ¬Ancestor (fun act => act ∈ branch) opener freezer := by
    intro path
    have computed := (StateExecutableFreeze.ancestor_iff branch ranked opener freezer (by simp [branch])).mpr path
    have missing : StateExecutableFreeze.ancestor branch opener freezer = false := by decide
    simp [missing] at computed
  have conflict : ∃ a b, FreezeConflict (fun act => act ∈ branch) "close"
      (StateAuthoredBindings.contributes domains branch (.verbs ["mark"])) true branch a b :=
    ⟨freezer,opener,.late first (by simp [branch]) contributes absent rfl⟩
  simp [freezeFault,conflict]

end CBCL.StateDomainSupportLocalityTests
