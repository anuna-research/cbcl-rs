import LeanCbcl.StateAuthoredSourceProvenance
import LeanCbcl.StateAuthoredBindingsTests
import LeanCbcl.StateDomainSupportLocalityTests

/-! Actual authored preparation with mixed domains, a forward initializer
reference and late freeze metadata. No source binding/table is supplied. -/
namespace CBCL.StateAuthoredSourceProvenanceTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateAuthoredBindings StateAuthoredSourceProvenance

/-- Fully authored finite table; installation resolves and checks every row. -/
def lattice : StateFiniteTable.Definition := {
  name := "phase-lattice"
  elements := ["empty","ready","conflict"]
  bottom := "empty"
  top := "conflict"
  rows := [("empty","empty","empty"),("empty","ready","ready"),("empty","conflict","conflict"),
    ("ready","empty","ready"),("ready","ready","ready"),("ready","conflict","conflict"),
    ("conflict","empty","conflict"),("conflict","ready","conflict"),("conflict","conflict","conflict")] }

/-- The concrete authored contribution is not an installed-field argument. -/
def finite : StateInstalledFinite.Declaration := ⟨"mark",[⟨"target",.str "@a","ready"⟩],none⟩

/-- Recognized immutable metadata; only the unrelated native context remains abstract. -/
def environment (context : StateKernelSEC.Context) : Environment := {
  StateAuthoredBindingsTests.environment context with
  profile := StateDomainSupportLocalityTests.profile
  schema := ⟨["open","mark","close"],[(("open","options"),.list),(("mark","target"),.string)]⟩
  fromRoles := [("close","reviewer")] }

/-- Domains and freeze metadata surround the finite source and threshold;
the initializer field is deliberately declared last. -/
def entries (fault : Bool) : List Entry := [
  .lattice lattice,
  .domain ⟨"mark","target","options"⟩,
  .field "reviewers" (.context ["thread","roles","reviewer"]),
  .domain ⟨"mark","target","reviewers"⟩,
  .field "phase" (.finite "phase-lattice" finite),
  .threshold "enough" "phase" [.element (.scalar (.str "ready"))],
  .freeze "phase" "close" fault,
  .field "options" (.legacy (.initial "open" "options"))]

/-- Table, domains, source policy, namespace and late freeze checks actually succeed. -/
theorem installation_succeeds (context : StateKernelSEC.Context) :
    (prepareStatic (environment context) (entries true)).isSome = true := by rfl

/-- A revisable superseding source cannot install this threshold. -/
theorem supersede_rejected (context : StateKernelSEC.Context) :
    prepareStatic (environment context) (entries false) = none := by rfl

/-- The actual source compiler constructs the final guarded finite plan from
these authored entries, without assuming a table, field, source lookup or freeze identity. -/
theorem complete_source_lookup (context : StateKernelSEC.Context) (history : List Act) :
    ∃ prepared field freezeDeclaration plans,
      prepareStatic (environment context) (entries true) = some prepared ∧
      StateAuthoredBindings.compile (environment context) (entries true) history = some plans ∧
      plans.lookup "phase" = some (StateFiniteOutputStability.source field history freezeDeclaration) ∧
      (materialize prepared.domains history prepared.freezes).lookup "phase" =
        freezeDeclaration.map (StateFiniteFreezePolicy.freezeSpec field history) ∧
      StateInstalledLowering.Declaration.field "phase" (StateFiniteRead.definition field) ∈ prepared.declarations := by
  cases installed : prepareStatic (environment context) (entries true) with
  | none => have accepted := installation_succeeds context; simp [installed] at accepted
  | some prepared =>
    obtain ⟨field,freezeDeclaration,plans,compiled,lookup,metadata,declared⟩ := authored_finite_plan
      (environment context) (entries true) prepared installed "phase" "phase-lattice" finite
      (by simp [rawFields,entries]) "enough" [.element (.scalar (.str "ready"))]
      (by simp [entries]) history
    exact ⟨prepared,field,freezeDeclaration,plans,rfl,compiled,lookup,metadata,declared⟩

end CBCL.StateAuthoredSourceProvenanceTests
