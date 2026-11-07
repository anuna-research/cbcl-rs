import LeanCbcl.StateKernelClause

/-! SPEC-036 executable counterexamples and composed observation checks. -/
namespace CBCL.StateKernelTests
open CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries
open CBCL.StateKernelAggregates CBCL.StateKernelExtensions CBCL.StateKernel CBCL.StateKernelClause

private def act (address : Nat) (verb signer : String) (fields : List (String × Val))
    (replaces : List Nat := []) : Act := ⟨address, verb, signer, [], fields, replaces⟩
private def history : List Act :=
  [act 1 "open" "owner" [("options", .list [.str "yes"])],
   act 50 "vote" "alice" [("choice", .str "yes"), ("amount", .int 7)],
   act 20 "vote" "alice" [("choice", .str "yes"), ("amount", .int 3)] [50],
   act 30 "vote" "bob" [("choice", .str "yes"), ("amount", .int 4)],
   act 80 "vote" "alice" [("choice", .str "excluded"), ("amount", .int 99)] [20]]
private def input : Input :=
  ⟨history, "open", fun _ a => some (a.addr, 0), fun _ => 0,
    fun _ => none, 0, fun _ => 0, fun _ => .pending [100]⟩
private def domains : List Domain := [⟨"vote", "choice", "open", "options"⟩]
private def plan : MapPlan := ⟨.own "vote", .signer, .address, "amount", false⟩
private def map := evalMap input.clock input.signerRank (admitted domains history) plan

-- The observed lower-address edit survives, while the excluded replacer does not count.
example : map.read (.str "alice") = .value (.int 3) := by decide
example : map.read (.str "bob") = .value (.int 4) := by decide
example : mapSum map = 7 := by decide
example : histogram map (.int 3) = 1 := by decide
example : histogram map (.int 7) = 0 := by decide

-- Scalar-map support and event support differ when the selected payload is absent.
private def missing : List Act := [act 2 "write" "alice" []]
example : (evalMap input.clock input.signerRank missing
    ⟨.verb "write", .signer, .address, "amount", false⟩).keys = [.str "alice"] := by decide
example : (evalMap input.clock input.signerRank missing
    ⟨.withField (.verb "write") "amount", .address, .address, "amount", true⟩).keys = [] := by decide
example : cellNumber (.event "alice" (.int (-4))) = -4 := by decide
example : resourceObserve (.pending [100]) = .pending [100] := rfl
example : ResourceView.balance (resourceObserve (.fault "fork" [10, 20])) = none := rfl

private def fields : List (String × Rule) :=
  [("options", .initial "open" "options"), ("ballots", .lwwPerSigner "vote" "amount" "clock"),
   ("tally", .histogram "ballots"), ("total", .sum "ballots")]
private def clause : Clause := ⟨fields, [⟨"vote", "choice", "options"⟩]⟩

example : (compileClause input clause).isSome = true := by decide
example : compileRule [] (.histogram "future") = none := by decide
example : compileRule [("tally", .histogram "ballots")] (.sum "tally") = none := by decide
example : compileClause input ⟨[("x", .count "vote"), ("x", .existsRule "vote")], []⟩ = none := by decide
example : compileDomain input [("options", .initial "vote" "choice")]
    ⟨"vote", "choice", "options"⟩ = none := by decide
example : normalizeHead "multi-value-register" = "values" := rfl
example : normalizeHead "multi-value-map" = "values-per-key" := rfl

end CBCL.StateKernelTests
