import LeanCbcl.InstalledDCFL

/-! SPEC-018 TEST-1801 / TEST-1802: concrete grammar and installation evidence. -/
namespace CBCL.InstalledSyntax.Tests

def dialect (name perf : String) : Dialect :=
  { baseDialect with name := name, performatives := [⟨perf, [], .list [.sym "tell"]⟩] }

def env := [baseDialect, dialect "d" "ship", dialect "e" "stop", dialect "f" "ship"]
def msg (h : String) (args : List SExpr := []) : SExpr := .list (.sym h :: args)
def lang (d : String) (e : SExpr) : SExpr := msg "lang" [.sym d, e]
def signed (e : SExpr) : SExpr := msg "signed" [.sym "signature", e]
def kw (k : String) : SExpr := .atom (.keyword k)

example : admitted env (msg "tell") := by decide
example : admitted env (lang "d" (signed (msg "ship" [.sym "parcel"]))) := by decide
example : ¬ admitted env (signed (msg "ship")) := by decide
example : ¬ admitted env (lang "absent" (msg "tell")) := by decide
example : ¬ admitted env (lang "d" (msg "stop")) := by decide
example : ¬ admitted env (lang "d" (lang "e" (msg "ship"))) := by decide
example : admitted env (lang "d" (lang "e" (msg "stop"))) := by decide
example : admitted env (lang "f" (msg "ship")) := by decide
example : admitted env (lang "d" (msg "tell")) := by decide
example : admitted env (msg "meta" [.list []]) := by decide
example : ¬ admitted env (msg "meta") := by decide
example : ¬ admitted env (msg "signed" [.sym "signature"]) := by decide
example : ¬ admitted env (msg "signed" [msg "tell", .list []]) := by decide
example : admitted env (msg "signed" [.list [], msg "tell", .sym "tail"]) := by decide
example : admitted env (msg "with-roles" [.list [], msg "hello"]) := by decide
example : ¬ admitted env (msg "tell" [kw "x"]) := by decide
example : ¬ admitted env (msg "tell" [kw "thread", .atom (.num 1)]) := by decide
example : ¬ admitted env (msg "tell" [kw "sender", .list []]) := by decide
example : admitted env (msg "tell" [kw "thread", .sym "t"]) := by decide
example : ¬ admitted env (msg "tell" [kw "caused-by", .list []]) := by decide
example : ¬ admitted env (msg "tell" [kw "caused-by", .list [.atom (.num 1)]]) := by decide
example : admitted env (msg "tell" [kw "caused-by", .list [.sym "hash"]]) := by decide
example : admitted env (msg "tell" [.sym "@alice", .sym "payload"]) := by decide
example : ¬ admitted env (msg "tell" [.sym "payload", .sym "@alice"]) := by decide
example : admitted env (msg "tell" [.sym "payload", .sym "@"]) := by decide
example : admitted env (msg "tell" [.list [.sym "@alice", .sym "@bob"], .sym "data"]) := by decide
example : ¬ admitted env (msg "tell" [.sym "data", .list [.sym "@alice"]]) := by decide
example : admitted env (msg "tell" [.list [.sym "introduce", .sym "@alice"]]) := by decide

/-- Wrapper scope preservation is universal, not a bounded-depth test. -/
theorem signed_scope (ds : List Dialect) (scope : Fin (ds.length+1)) (xs : List SExpr) :
    admittedAt ds scope (.list [.sym "signed", .list xs]) ↔ admittedAt ds scope (.list xs) := by
  rfl

def nest : Nat → List SExpr → List SExpr
  | 0, xs => xs
  | n+1, xs => [.sym "signed", .list (nest n xs)]

theorem arbitrary_nesting (ds : List Dialect) (scope : Fin (ds.length+1))
    (n : Nat) (xs : List SExpr) :
    admittedAt ds scope (.list (nest n xs)) ↔ admittedAt ds scope (.list xs) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (signed_scope ds scope (nest n xs)).trans ih

example : ((Agent.new "agent").dialects.map Dialect.name).Nodup := by decide
example : (dialect "d" "ship").name ∉ (Agent.new "agent").dialects.map Dialect.name := by decide
example : ¬ (baseDialect.name ∉ (Agent.new "agent").dialects.map Dialect.name) := by decide

def installed_certificate := dcfl_preserved_many (Agent.new "agent")
  [dialect "d" "ship", dialect "f" "ship"]

example : VerifiedFresh (Agent.new "agent") (dialect "d" "ship") := by
  constructor
  · decide
  · decide

example : ¬ VerifiedFresh (Agent.new "agent") baseDialect := by
  apply duplicate_not_verified_fresh
  decide

example : (environmentDCFL env).machine.accepts
    (FormalLanguage.SyntaxTree.encode (classifyTree env (lang "d" (signed (msg "ship"))))) = true :=
  (recognizes_expression env _).mpr (by decide)

example : (environmentDCFL []).machine.accepts [] = false := by decide
example : (environmentDCFL []).machine.accepts [1] = false := by decide

end CBCL.InstalledSyntax.Tests
