import LeanCbcl.SExpr
import LeanCbcl.Message
import Batteries.Tactic.Lint  -- provides the `@[nolint …]` attribute

/-!
# CBCL Dialect System

Formalizes dialect definitions: named collections of performative expansions
with declared resource bounds. Dialects are the extension mechanism of CBCL.

Mirrors: `src/cbcl.scm` lines 121-192 (record type + base dialect)
-/

namespace CBCL

/-- Resource bound declaration for a dialect.
    Mirrors the resource alist: max-depth, max-expansion-size, verification-time.
    All three fields are REQUIRED by R2 verification. -/
structure ResourceBounds where
  /-- Maximum template-expansion nesting depth permitted (R2). -/
  maxDepth         : Nat
  /-- Maximum total expansion size permitted (R2). -/
  maxExpansionSize : Nat
  /-- Maximum verification time budget, in milliseconds (R2). -/
  verificationTime : Nat  -- milliseconds
  deriving Repr, BEq, DecidableEq, Inhabited

-- The `deriving Repr` handler emits a `reprPrec` that ignores its precedence
-- argument (records are never parenthesised), so `unusedArguments` flags the
-- auto-generated `.repr`. This is a false positive on generated code, suppressed
-- on the derived instance rather than altering it.
attribute [nolint unusedArguments] instReprResourceBounds.repr

/-- A performative definition maps a name to a template expansion.
    In the Scheme implementation, core performatives use lambdas while
    extension performatives use declarative templates (literal, cond, sequence). -/
structure PerformativeDef where
  /-- The performative's name (its head symbol). -/
  name     : String
  /-- Formal parameters bound in the template. -/
  params   : List SExpr
  /-- The expansion template this performative rewrites to. -/
  template : SExpr
  deriving Repr, BEq, Inhabited

-- Derived-`Repr` precedence argument unused (see note above). False positive.
attribute [nolint unusedArguments] instReprPerformativeDef.repr

/-- A CBCL dialect. Mirrors `<cbcl-dialect>` record. -/
structure Dialect where
  /-- The dialect's unique name. -/
  name           : String
  /-- Names of parent dialects this one extends. -/
  extends_       : List String  -- parent dialect names
  /-- The dialect's author/owner. -/
  author         : String
  /-- Performative definitions introduced by this dialect. -/
  performatives  : List PerformativeDef
  /-- Resource bounds enforced for this dialect (R2). -/
  resources      : ResourceBounds
  /-- Example messages illustrating the dialect. -/
  examples       : List SExpr    := []
  /-- Optional cryptographic signature over the dialect definition. -/
  signature      : Option String := none
  /-- Optional content hash of the dialect definition. -/
  hash           : Option String := none
  /-- Optional protocol name/identifier the dialect follows. -/
  protocol       : Option String := none
  deriving Repr, Inhabited

-- Derived-`Repr` precedence argument unused (see note above). False positive.
attribute [nolint unusedArguments] instReprDialect.repr

/-- The base dialect's resource bounds: max-depth=8, max-expansion=512, verification-time=10ms -/
def baseResourceBounds : ResourceBounds :=
  { maxDepth := 8, maxExpansionSize := 512, verificationTime := 10 }

/-- The base dialect. Mirrors `*cbcl-base-dialect*`.
    Core performatives are represented as symbolic templates since Lean
    can't embed Scheme lambdas — instead we use a symbolic representation. -/
def baseDialect : Dialect :=
  { name := "cbcl-base"
  , extends_ := []
  , author := "@cbcl-system"
  , performatives :=
      [ { name := "tell",   params := [], template := SExpr.list [.sym "effect", .sym "send-message"] }
      , { name := "ask",    params := [], template := SExpr.list [.sym "effect", .sym "send-query"] }
      , { name := "reply",  params := [], template := SExpr.list [.sym "effect", .sym "send-reply"] }
      , { name := "error",  params := [], template := SExpr.list [.sym "effect", .sym "signal-error"] }
      , { name := "ok",     params := [], template := SExpr.list [.sym "effect", .sym "acknowledge"] }
      , { name := "cancel", params := [], template := SExpr.list [.sym "effect", .sym "cancel-conversation"] }
      , { name := "hello",  params := [], template := SExpr.list [.sym "effect", .sym "announce-presence"] }
      , { name := "bye",    params := [], template := SExpr.list [.sym "effect", .sym "announce-departure"] }
      ]
  , resources := baseResourceBounds
  }

/-- The base dialect defines exactly the 8 core performatives. -/
theorem baseDialect_has_8_performatives :
    baseDialect.performatives.length = 8 := by rfl

/-- Get the names of all performatives in a dialect. -/
def Dialect.performativeNames (d : Dialect) : List String :=
  d.performatives.map (·.name)

/-- Check if a dialect defines a given performative name. -/
def Dialect.definesPerformative (d : Dialect) (name : String) : Bool :=
  d.performatives.any (·.name == name)

/-- A dialect redefines no core performatives: none of its defined
    performatives shares a name with a core performative.

    Note: this is *not* disjuncted with a name-based base-dialect
    exemption. A name-based exemption would admit spoofed dialects
    whose `name` equals `"cbcl-base"` but whose `performatives` contain
    core names. Callers that need to admit the real base dialect use
    positional reasoning (via `Agent.wellFormed`, which pins the base
    dialect as the literal first element of `dialects`). -/
def Dialect.noCoreRedefinition (d : Dialect) : Prop :=
  ∀ pd ∈ d.performatives, isCorePerformativeName pd.name = false

/-- Look up a performative definition by name. -/
def Dialect.findPerformative (d : Dialect) (name : String) : Option PerformativeDef :=
  d.performatives.find? (·.name == name)

/-- The base dialect defines all core performatives. -/
theorem baseDialect_defines_all_core :
    ∀ name ∈ corePerformativeNames, baseDialect.definesPerformative name = true := by
  intro name hmem
  simp [corePerformativeNames] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;>
    (subst h; native_decide)

/-- R2 static upper bound on expansion depth: the system-wide maximum
    `max-depth` any dialect may declare. -/
def maxAllowedDepth : Nat := 64
/-- R2 static upper bound on total expansion size, system-wide. -/
def maxAllowedExpansionSize : Nat := 8192
/-- R2 static upper bound on verification time (ms), system-wide. -/
def maxAllowedVerificationTime : Nat := 1000

/-- A resource bounds declaration is valid if all fields are within system limits. -/
def ResourceBounds.isValid (rb : ResourceBounds) : Prop :=
  0 < rb.maxDepth ∧ rb.maxDepth ≤ maxAllowedDepth ∧
  0 < rb.maxExpansionSize ∧ rb.maxExpansionSize ≤ maxAllowedExpansionSize ∧
  0 < rb.verificationTime ∧ rb.verificationTime ≤ maxAllowedVerificationTime

/-- Decidable instance for ResourceBounds.isValid -/
instance (rb : ResourceBounds) : Decidable (rb.isValid) := by
  unfold ResourceBounds.isValid
  exact inferInstance

/-- The base dialect's resource bounds are valid. -/
theorem baseResourceBounds_valid : baseResourceBounds.isValid := by
  unfold ResourceBounds.isValid
  simp [baseResourceBounds, maxAllowedDepth, maxAllowedExpansionSize, maxAllowedVerificationTime]

end CBCL
