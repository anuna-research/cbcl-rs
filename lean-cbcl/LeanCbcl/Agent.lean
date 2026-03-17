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

/-- The well-formedness invariant: base dialect is the first element. -/
def Agent.wellFormed (a : Agent) : Prop :=
  ∃ rest, a.dialects = baseDialect :: rest

/-- A freshly created agent is well-formed. -/
theorem Agent.new_wellFormed (id : String) : (Agent.new id).wellFormed :=
  ⟨[], rfl⟩

/-- Look up which dialect provides a performative. -/
def Agent.findPerformativeDialect (a : Agent) (name : String) : Option Dialect :=
  a.dialects.reverse.find? (·.definesPerformative name)

/-- Install a dialect into the agent's dialect list. -/
def Agent.installDialect (a : Agent) (d : Dialect) : Agent :=
  { a with dialects := a.dialects ++ [d] }

/-- Installing a dialect preserves well-formedness. -/
theorem Agent.installDialect_preserves_wellFormed
    (a : Agent) (d : Dialect) (hwf : a.wellFormed) :
    (a.installDialect d).wellFormed := by
  obtain ⟨rest, hrfl⟩ := hwf
  exact ⟨rest ++ [d], by simp [Agent.installDialect, hrfl]⟩

/-- An agent always has the base dialect after any number of installations. -/
theorem Agent.always_has_base_dialect
    (a : Agent) (hwf : a.wellFormed) :
    baseDialect ∈ a.dialects := by
  obtain ⟨rest, hrfl⟩ := hwf
  rw [hrfl]
  exact List.mem_cons_self ..

end CBCL
