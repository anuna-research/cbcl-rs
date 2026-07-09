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
  /-- The agent's unique identifier string. -/
  id            : String
  /-- The dialects installed on this agent; `baseDialect` is the first element. -/
  dialects      : List Dialect
  deriving Inhabited

/-- Create a fresh agent with only the base dialect installed. -/
def Agent.new (id : String) : Agent :=
  { id := id, dialects := [baseDialect] }

/-- The well-formedness invariant:
    (i) the literal `baseDialect` constant is the first element of
        `dialects`, AND
    (ii) every *non-first* (installed) dialect satisfies
        `Dialect.noCoreRedefinition` (defines no core performatives).

    Clause (ii) ranges over `rest` (the tail after the base), not over
    all of `dialects`. This is a deliberate positional guarantee: the
    head is known to be the real `baseDialect` by clause (i), so we do
    not need a name-based exemption for it. A name-based exemption
    would be unsound — it would admit a spoofed dialect whose `name`
    equals `"cbcl-base"` but whose `performatives` redefine `tell` or
    other core names.

    Clause (ii) is what makes `install_preserves_core` a genuinely
    load-bearing composition — see the `hname` premise there. -/
def Agent.wellFormed (a : Agent) : Prop :=
  ∃ rest, a.dialects = baseDialect :: rest ∧
    (∀ d ∈ rest, d.noCoreRedefinition)

/-- A freshly created agent is well-formed. -/
theorem Agent.new_wellFormed (id : String) : (Agent.new id).wellFormed := by
  refine ⟨[], rfl, ?_⟩
  intro d hd
  exact absurd hd (List.not_mem_nil)

/-- Look up which dialect provides a performative. -/
def Agent.findPerformativeDialect (a : Agent) (name : String) : Option Dialect :=
  a.dialects.reverse.find? (·.definesPerformative name)

/-- Install a dialect into the agent's dialect list. -/
def Agent.installDialect (a : Agent) (d : Dialect) : Agent :=
  { a with dialects := a.dialects ++ [d] }

/-- Installing a dialect that redefines no core performatives preserves
    well-formedness. The `hNoCore` premise is discharged by
    `r3_no_core_redefinition` for R3-verified dialects whose name is
    not `"cbcl-base"` — see `install_preserves_core`. -/
theorem Agent.installDialect_preserves_wellFormed
    (a : Agent) (d : Dialect) (hwf : a.wellFormed)
    (hNoCore : d.noCoreRedefinition) :
    (a.installDialect d).wellFormed := by
  obtain ⟨rest, hrfl, hall⟩ := hwf
  refine ⟨rest ++ [d], ?_, ?_⟩
  · simp [Agent.installDialect, hrfl]
  · intro d' hd'
    simp only [List.mem_append, List.mem_singleton] at hd'
    rcases hd' with h | h
    · exact hall d' h
    · subst h; exact hNoCore

/-- An agent always has the base dialect after any number of installations. -/
theorem Agent.always_has_base_dialect
    (a : Agent) (hwf : a.wellFormed) :
    baseDialect ∈ a.dialects := by
  obtain ⟨rest, hrfl, _⟩ := hwf
  rw [hrfl]
  exact List.mem_cons_self ..

end CBCL
