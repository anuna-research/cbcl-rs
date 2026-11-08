import LeanCbcl.StateInstalledClause

namespace CBCL.StateInstalledCompilerTests
open State StateLift StateLVar StateObservation StateObservationPlan
open StateInstalledCompiler StateInstalledClause

def source : Source Nat := .snapshot FinSet.card
def sealing : FreezeSpec := ⟨"close",fun a => a.verb = "vote",false⟩
def clause : Clause Nat := ⟨[("votes",.source source),("next",.derived Nat.succ "votes")],[("votes",sealing)]⟩

/-- The source is decorated before the derived declaration is compiled, even
though the surface freeze declaration is stored separately. -/
theorem late_freeze_attaches_before_dependencies : StateInstalledClause.compile clause = some
    [("votes",.freeze sealing (sourcePlan source)),
     ("next",.map Nat.succ (.freeze sealing (sourcePlan source)))] := by
  simp [StateInstalledClause.compile,clause,ValidMetadata,attach,StateInstalledClause.compileFields,
    compileField,compileRule,List.lookup]

theorem forward_reference_rejected : StateInstalledCompiler.compileClause
    [("next",Rule.derived Nat.succ "votes"),("votes",.source source)] = none := by
  simp [StateInstalledCompiler.compileClause,StateInstalledCompiler.compileFields,compileRule,List.lookup]

theorem duplicate_fields_rejected : StateInstalledCompiler.compileClause
    [("votes",Rule.source source),("votes",.source source)] = none := by
  simp [StateInstalledCompiler.compileClause]

theorem absent_freeze_target_rejected : StateInstalledClause.compile
    (Clause.mk [("votes",Rule.source source)] [("missing",sealing)]) = none := by
  simp [StateInstalledClause.compile,ValidMetadata]

theorem simultaneous_pair_faults (a b : Evidence) :
    nativePair Nat.add (.fault a) (.fault b) = .fault (a ∪ b) := rfl

/-- Derived evaluation sees the historical payload of the globally decorated
source. It cannot replace that payload with a fresh current-history count. -/
theorem compiled_derived_reads_frozen_payload (world : Act → Prop) (A : List Act)
    (freezer value : Nat) (excluded : FinSet Act)
    (frozen : data world (.freeze sealing (sourcePlan source)) A = .frozen freezer value excluded) :
    data world (.map Nat.succ (.freeze sealing (sourcePlan source))) A = .snapshot (value+1) :=
  derived_frozen_payload world _ Nat.succ A freezer value excluded frozen

end CBCL.StateInstalledCompilerTests
