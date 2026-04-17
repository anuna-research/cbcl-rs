import LeanCbcl.Dialect
import LeanCbcl.Message

/-!
# CBCL Agent

Formalizes agent state and the dialect installation operation.
An agent maintains a list of installed dialects, starting with the base dialect.

Mirrors: `src/cbcl.scm` lines 103-119
-/

namespace CBCL

/-- Agent state. Mirrors `<cbcl-agent>` record. -/
structure Agent where
  id            : String
  dialects      : List Dialect
  deriving Inhabited

/-- Create a fresh agent with only the base dialect installed. -/
def Agent.new (id : String) : Agent :=
  { id := id, dialects := [baseDialect] }

/-- The well-formedness invariant:
    (i) the base dialect is the first element, AND
    (ii) every installed dialect is core-safe (no non-base dialect
    defines a core performative).

    Clause (ii) is what R3-verification enforces at the installation
    boundary; it is what makes `install_preserves_core` a genuinely
    load-bearing composition rather than a structural list-cons result. -/
def Agent.wellFormed (a : Agent) : Prop :=
  (∃ rest, a.dialects = baseDialect :: rest) ∧
  (∀ d ∈ a.dialects, d.coreSafe)

/-- A freshly created agent is well-formed. -/
theorem Agent.new_wellFormed (id : String) : (Agent.new id).wellFormed := by
  refine ⟨⟨[], rfl⟩, ?_⟩
  intro d hd
  simp [Agent.new] at hd
  subst hd
  exact baseDialect_coreSafe

/-- Look up which dialect provides a performative. -/
def Agent.findPerformativeDialect (a : Agent) (name : String) : Option Dialect :=
  a.dialects.reverse.find? (·.definesPerformative name)

/-- Install a dialect into the agent's dialect list. -/
def Agent.installDialect (a : Agent) (d : Dialect) : Agent :=
  { a with dialects := a.dialects ++ [d] }

/-- Installing a core-safe dialect preserves well-formedness. The
    `hCore` premise is discharged by `r3_no_core_redefinition` for
    R3-verified dialects — see `install_preserves_core`. -/
theorem Agent.installDialect_preserves_wellFormed
    (a : Agent) (d : Dialect) (hwf : a.wellFormed) (hCore : d.coreSafe) :
    (a.installDialect d).wellFormed := by
  obtain ⟨⟨rest, hrfl⟩, hall⟩ := hwf
  refine ⟨⟨rest ++ [d], ?_⟩, ?_⟩
  · simp [Agent.installDialect, hrfl]
  · intro d' hd'
    simp only [Agent.installDialect, List.mem_append, List.mem_singleton] at hd'
    rcases hd' with h | h
    · exact hall d' h
    · subst h; exact hCore

/-- An agent always has the base dialect after any number of installations. -/
theorem Agent.always_has_base_dialect
    (a : Agent) (hwf : a.wellFormed) :
    baseDialect ∈ a.dialects := by
  obtain ⟨⟨rest, hrfl⟩, _⟩ := hwf
  rw [hrfl]
  exact List.mem_cons_self ..

end CBCL
