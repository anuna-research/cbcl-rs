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

/-- Installing an R3-verified dialect with a non-`"cbcl-base"` name
    preserves well-formedness.

    Both premises are load-bearing:
      * `hr3 : verifyR3 d = true` — consumed by `r3_no_core_redefinition`
        to prove `d.noCoreRedefinition`, which is the side-condition of
        `Agent.installDialect_preserves_wellFormed`.
      * `hname : d.name ≠ "cbcl-base"` — required because `verifyR3`
        short-circuits to `true` for any dialect whose name is
        `"cbcl-base"` regardless of its performatives. Without this
        premise, a spoofed dialect could claim the base name and
        redefine core performatives (e.g. `tell`) while still passing
        R3 verification. The premise rules out that duplicate core
        definition at the installation boundary; dispatch separately
        uses `baseDefinerOf`, which consults only the list head. -/
theorem install_preserves_core
    (a : Agent) (d : Dialect)
    (hwf : a.wellFormed)
    (hr3 : verifyR3 d = true)
    (hname : d.name ≠ "cbcl-base") :
    (a.installDialect d).wellFormed :=
  Agent.installDialect_preserves_wellFormed a d hwf
    (r3_no_core_redefinition d hname hr3)

/-- Composition consequence: after `install_preserves_core`, no non-base
    dialect in the resulting agent defines a core performative. This
    witnesses the load-bearing content of `hr3` and `hname`: the
    conclusion follows *only* because `verifyR3` (applied to a
    non-base-named dialect) rules out core redefinition in `d`. -/
theorem install_no_core_redefinition
    (a : Agent) (d : Dialect)
    (hwf : a.wellFormed) (hr3 : verifyR3 d = true) (hname : d.name ≠ "cbcl-base")
    (d' : Dialect) (hmem : d' ∈ (a.installDialect d).dialects)
    (hnb : d'.name ≠ "cbcl-base")
    (pd : PerformativeDef) (hpd : pd ∈ d'.performatives) :
    isCorePerformativeName pd.name = false := by
  obtain ⟨rest, hrfl, hall⟩ := install_preserves_core a d hwf hr3 hname
  rw [hrfl, List.mem_cons] at hmem
  rcases hmem with h | h
  · -- d' = baseDialect, so d'.name = "cbcl-base", contradicting hnb
    exact absurd (by rw [h]; rfl : d'.name = "cbcl-base") hnb
  · exact hall d' h pd hpd

-- ============================================================
-- Base-name spoofing regression
-- ============================================================

/-- A spoofed "base" dialect: claims `name = "cbcl-base"` but redefines
    the core performative `tell`. This is the adversarial input the
    positional invariant in `Agent.wellFormed` and the `hname` premise
    in `install_preserves_core` are designed to reject. -/
def spoofedBaseDialect : Dialect :=
  { name := "cbcl-base"
  , extends_ := []
  , author := "@attacker"
  , performatives :=
      [ { name := "tell", params := [], template := .sym "spoofed" } ]
  , resources := baseResourceBounds }

/-- `verifyR3` alone is too permissive: the name short-circuit admits
    the spoof even though it redefines `tell`. -/
theorem spoofed_passes_verifyR3 : verifyR3 spoofedBaseDialect = true := by
  native_decide

/-- But `noCoreRedefinition` correctly rejects the spoof. This is the
    property `install_preserves_core` requires via the composition
    `r3_no_core_redefinition` — which is itself conditional on
    `d.name ≠ "cbcl-base"`. Hence the `hname` premise in
    `install_preserves_core` is load-bearing: without it, the spoof
    would pass `verifyR3` without its `noCoreRedefinition` obligation
    being discharged, and the positional invariant of
    `Agent.wellFormed` would be violated by a fake base at the list
    tail. `Agent.baseDefinerOf` independently confines core dispatch to
    the list head. -/
theorem spoofed_fails_noCoreRedefinition :
    ¬ spoofedBaseDialect.noCoreRedefinition := by
  intro h
  have hmem :
      ({ name := "tell", params := [], template := SExpr.sym "spoofed" }
        : PerformativeDef) ∈ spoofedBaseDialect.performatives := by
    simp [spoofedBaseDialect]
  have hf : isCorePerformativeName "tell" = false := h _ hmem
  have ht : isCorePerformativeName "tell" = true := by native_decide
  exact Bool.false_ne_true (hf ▸ ht)

end CBCL
