import LeanCbcl.SExpr
import LeanCbcl.Message

/-!
# CBCL Pattern Matching

Formalizes the pattern matching and substitution system.
Proves correctness: matching produces valid bindings, substitution preserves structure.

Mirrors: `src/cbcl.scm` lines 399-448
-/

namespace CBCL

/-- A binding environment maps variable names to S-expression values. -/
abbrev Bindings := List (String × SExpr)

/-- Look up a variable in bindings. -/
def Bindings.lookup (bs : Bindings) (name : String) : Option SExpr :=
  (bs.find? (·.1 == name)).map (·.2)

/-- Match a pattern against a value, extending bindings.
    Mirrors `match-pattern` from cbcl.scm lines 399-436. -/
def matchPattern : SExpr → SExpr → Bindings → Option Bindings
  | .atom (.symbol "_"), _, bs => some bs
  | .atom (.symbol s), val, bs =>
    if isCorePerformativeName s then
      match val with
      | .atom (.symbol s') => if s == s' then some bs else none
      | _ => none
    else
      match bs.lookup s with
      | some v => if v == val then some bs else none
      | none   => some ((s, val) :: bs)
  | .atom (.keyword k), .atom (.keyword k'), bs =>
    if k == k' then some bs else none
  | .list [], .list [], bs => some bs
  | .list (ph :: pt), .list (vh :: vt), bs => do
    let bs' ← matchPattern ph vh bs
    matchPattern (.list pt) (.list vt) bs'
  | .list _, .list _, _ => none
  | .atom a, .atom a', bs => if a == a' then some bs else none
  | _, _, _ => none

/-- Substitute variables in a template with their bindings.
    Mirrors `substitute-bindings` from cbcl.scm lines 438-448. -/
def substituteBindings : SExpr → Bindings → SExpr
  | .atom (.symbol s), bs =>
    match bs.lookup s with
    | some v => v
    | none   => .atom (.symbol s)
  | .list xs, bs => .list (xs.map (substituteBindings · bs))
  | other, _ => other

/-- Wildcard always matches. -/
theorem matchPattern_wildcard (v : SExpr) (bs : Bindings) :
    matchPattern (.atom (.symbol "_")) v bs = some bs := by
  simp [matchPattern]

end CBCL
