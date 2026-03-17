import LeanCbcl.SExpr

/-!
# CBCL Message Types

Formalizes the CBCL message grammar from Section 3.2 of the paper.
Messages are typed S-expressions with four variants: Simple, Meta, Dialect, Wrapped.

Mirrors: `src/cbcl.scm` lines 138-157, 198-282
-/

namespace CBCL

/-- The 8 core performatives that form the bootstrap vocabulary.
    These are immutable across all dialects (enforced by R3). -/
inductive CorePerformative where
  | tell | ask | reply | error | ok | cancel | hello | bye
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A performative is either a core one or a custom dialect extension. -/
inductive Performative where
  | core   : CorePerformative → Performative
  | custom : String → Performative
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Check if a performative is a core one. Mirrors `core-performative?`. -/
def Performative.isCore : Performative → Bool
  | .core _ => true
  | .custom _ => false

/-- The four CBCL message types from the grammar.
    Mirrors `message-type` field of `<cbcl-message>`. -/
inductive MessageType where
  | simple   : MessageType  -- (performative recipient content . params)
  | metaMsg  : MessageType  -- (meta (define dialect-name ...))
  | dialect  : MessageType  -- (lang dialect-name inner-message)
  | wrapped  : MessageType  -- (envelope|signed|with-limits . content)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A CBCL message. Mirrors `<cbcl-message>` record type. -/
structure Message where
  type         : MessageType
  performative : Performative
  params       : List SExpr
  thread       : Option String := none
  sender       : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- All core performative names as strings. -/
def corePerformativeNames : List String :=
  ["tell", "ask", "reply", "error", "ok", "cancel", "hello", "bye"]

/-- Decision procedure: is this string a core performative name? -/
def isCorePerformativeName (s : String) : Bool :=
  corePerformativeNames.contains s

/-- The list of core performatives is exactly 8 elements. -/
theorem corePerformativeNames_length : corePerformativeNames.length = 8 := by rfl

/-- Core performatives enumeration is exhaustive. -/
theorem CorePerformative.exhaustive (p : CorePerformative) :
    p = .tell ∨ p = .ask ∨ p = .reply ∨ p = .error ∨
    p = .ok ∨ p = .cancel ∨ p = .hello ∨ p = .bye := by
  cases p <;> simp

end CBCL
