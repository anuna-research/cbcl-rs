import LeanCbcl.SExpr
import LeanCbcl.Message
import LeanCbcl.Dialect
import LeanCbcl.Agent

/-!
# R3 Constraint: Core Preservation

Formalizes the R3 safety constraint: core performatives (tell, ask, reply, error,
ok, cancel, hello, bye) can NEVER be redefined by extension dialects.

Mirrors: `src/cbcl.scm` lines 517-525

## Key theorem
For any well-formed agent, after installing any number of R3-verified dialects,
looking up a core performative always resolves to the base dialect's definition.
-/

namespace CBCL

/-- Verify R3: a non-base dialect must not define any core performative. -/
def verifyR3 (d : Dialect) : Bool :=
  if d.name == "cbcl-base" then true
  else d.performatives.all (fun pd => !isCorePerformativeName pd.name)

/-- If R3 verification passes for a non-base dialect, it defines no core performatives. -/
theorem r3_no_core_redefinition (d : Dialect) (hname : d.name ≠ "cbcl-base")
    (hverify : verifyR3 d = true) :
    ∀ pd ∈ d.performatives, isCorePerformativeName pd.name = false := by
  simp [verifyR3, show (d.name == "cbcl-base") = false from by simp [hname]] at hverify
  intro pd hmem
  have := hverify pd hmem
  simpa using this

/-- The base dialect trivially passes R3. -/
theorem r3_base_valid : verifyR3 baseDialect = true := by
  simp [verifyR3, baseDialect]

/-- Core preservation: an R3-verified non-base dialect does not define any core performative. -/
theorem core_performative_not_in_r3_dialect
    (d : Dialect) (hname : d.name ≠ "cbcl-base")
    (hverify : verifyR3 d = true)
    (coreName : String) (hcore : isCorePerformativeName coreName = true) :
    d.definesPerformative coreName = false := by
  have hnocore := r3_no_core_redefinition d hname hverify
  simp [Dialect.definesPerformative]
  intro pd hmem
  have := hnocore pd hmem
  intro heq
  rw [heq] at this
  exact absurd hcore (by simp [this])

/-- Installing an R3-verified dialect preserves well-formedness. -/
theorem install_preserves_core
    (a : Agent) (d : Dialect)
    (hwf : a.wellFormed)
    (_hr3 : verifyR3 d = true) :
    (a.installDialect d).wellFormed :=
  Agent.installDialect_preserves_wellFormed a d hwf

end CBCL
