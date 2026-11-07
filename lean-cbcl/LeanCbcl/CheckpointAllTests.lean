import LeanCbcl.CheckpointAll

/-! Closed kernel-reduced all-head examples and dependency audits. Toy ports
exercise transport, not soundness of production crypto/resource classification. -/
namespace CBCL.CheckpointAll.Tests
open State StateKernelSemantics StateKernelQueries StateKernel
open StateKernelClause CheckpointSummary CheckpointEvidence

private def act (id : Nat) (verb : String) (value stamp : Int := 0)
    (refs : List Nat := []) (preds : List Nat := []) : Act :=
  ⟨id, verb, "@a", preds,
    [("value", .int value), ("item", .str "x"), ("stamp", .int stamp),
     ("irrelevant", .str "full body is not retained by event projections")], refs⟩

private def clock : Clock := fun field a => match a.get field with
  | some (.int stamp) => if 0 ≤ stamp then some (stamp.toNat, 0) else none
  | _ => none

private def input : Input :=
  ⟨[], "open", clock, fun _ => 0, fun _ => none, 0, fun _ => 5, fun _ => .pending []⟩

private def causal (a : Act) : Repeat.Evidence :=
  ⟨0, a.verb, match a.preds with | [] => .begin | p :: _ => .previous p⟩

private def resourceData (a : Act) : ResourceData :=
  ⟨a.signer, if a.verb = "native-fault" then .checkpoint else .other,
    0, a.preds.head?, a.preds, {resource := "budget"}⟩

private def fault (fs : List ResourceFact) : Bool := fs.any (fun f => f.data.kind == .checkpoint)

private theorem fault_ext (xs ys : List ResourceFact) (same : FactSetEq xs ys) :
    fault xs = fault ys := by
  apply Bool.eq_iff_iff.mpr
  simp only [fault, List.any_eq_true]
  constructor
  · rintro ⟨f, hf, eq⟩; exact ⟨f, (same f).mp hf, eq⟩
  · rintro ⟨f, hf, eq⟩; exact ⟨f, (same f).mpr hf, eq⟩

private def port : ResourcePort where
  extract := resourceData
  classify := fun fs _ => if fault fs then .fault "native authority fault" [7] else .pending [9]
  classify_ext := by
    intro xs ys same
    funext name
    simp only [fault_ext xs ys same]

private def ports : Ports := ⟨causal, port⟩

/-- Each native head occurs; aggregate references point to valid earlier sources. -/
private def raw : List (String × StateKernelClause.Rule) :=
  [("initial", .initial "open" "value"), ("exists", .existsRule "put"),
   ("count", .count "put"), ("progress", .progress "tick"),
   ("events", .events "put" "value"), ("union", .setUnion "put" "value"),
   ("values", .values "put" "value"),
   ("valuesBy", .valuesPerKey "put" "item" "value" (some "drop")),
   ("observed", .observedSet "put" "drop" "item"),
   ("counter", .counter "put" "down" "value"),
   ("latest", .lwwRegister "put" "value" "stamp"),
   ("signers", .lwwPerSigner "put" "value" "stamp"),
   ("map", .lwwMap "put" "item" "value" "stamp" (some "drop")),
   ("histogram", .histogram "map"), ("sum", .sum "events"),
   ("resource", .boundedCounter "budget")]

private def fields : List (String × CheckpointAll.Rule) := (resolveFields [] raw).getD []

example : raw.length = 16 ∧ fields.length = 16 := by decide
example : resolveFields [] raw = some fields := by decide
example : (raw.map Prod.fst).Nodup := by decide

/-- Invalid forward references and incompatible histogram sources reject. -/
example : resolveFields [] [("sum", .sum "events"), ("events", .events "put" "value")] = none := by decide
example : resolveFields [] [("events", .events "put" "value"), ("hist", .histogram "events")] = none := by decide
example : resolveFields [] [("count", .count "put"), ("sum", .sum "count")] = none := by decide
example : resolveFields [] [("sum", .sum "missing")] = none := by decide

private def older := act 2 "put" 7 1
private def newer := act 3 "put" 11 2
private def removeNewer := act 4 "drop" 0 3 [3]
private def history := [act 1 "open" 42, older, newer, act 21 "tick" 0 0 [] [20]]
private def tail := [removeNewer, newer, act 20 "tick", act 5 "down" 2, act 7 "native-fault"]
private def saved := Snapshot.checkpoint ports input fields history
private def resumed := saved.advance ports input tail

/-- Arbitrary histories/tails instantiate the all-head law, not just this fixture. -/
example (H D : List Act) :
    ((Snapshot.checkpoint ports input fields H).advance ports input D).render ports input =
      fullFold ports input fields (H ++ D) := render_advance_checkpoint ports input fields H D

/-- Native compilation is explicitly linked, including ordered derived fields. -/
example : compileClause input ⟨raw, []⟩ =
    some ⟨[], fields.map (fun (name, rule) => (name, rule.expression))⟩ :=
  native_compile_clause input raw fields (by decide) (by decide)

private def integer (s : Snapshot) (name : String) : Option Int :=
  match (s.render ports input).lookup name with
  | some (.integer value) => some value
  | _ => none

private def mapRead (s : Snapshot) (name : String) (key : Val) : Option Cell :=
  match (s.render ports input).lookup name with
  | some (.mapped read) => read key
  | _ => none

private def histogramRead (s : Snapshot) (name : String) (value : Val) : Option Nat :=
  match (s.render ports input).lookup name with
  | some (.histogram support counts) => if support value then some (counts value) else none
  | _ => none

example : integer resumed "count" = some 2 := by decide
example : integer resumed "counter" = some 16 := by decide
example : integer resumed "sum" = some 18 := by decide
example : integer saved "progress" = some 0 := by decide
example : integer resumed "progress" = some 2 := by decide
example : mapRead resumed "map" (.str "x") = some (.value (.int 7)) := by decide
example : mapRead resumed "events" (.int 2) = some (.event "@a" (.int 7)) := by decide
example : mapRead resumed "events" (.int 3) = some (.event "@a" (.int 11)) := by decide
example : histogramRead resumed "histogram" (.int 7) = some 1 := by decide
example : histogramRead resumed "histogram" (.int 11) = none := by decide

/-- Dropping selected causal evidence changes an actual observation. -/
private def lostProtocol : Snapshot := {resumed with protocol := []}
example : integer lostProtocol "progress" = some 0 ∧ integer resumed "progress" = some 2 := by decide

/-- Checkpoint endorsements cannot erase a native resource fault. -/
private def resourceView (s : Snapshot) : Option StateKernelExtensions.ResourceView :=
  match (s.render ports input).lookup "resource" with
  | some (.resource value) => some value
  | _ => none
example : resourceView resumed = some (.fault "native authority fault" [7]) := by decide
example : resourceView (resumed.advance ports input [act 30 "endorse", act 31 "endorse", act 32 "endorse"]) =
    some (.fault "native authority fault" [7]) := by decide
private def lostResource : Snapshot := {resumed with resource := []}
example : resourceView lostResource = some (.pending [9]) := by decide

/-- Duplicate accepted IDs preserve all finite rows and both evidence tables. -/
example : (resumed.advance ports input [newer, newer]).protocol = resumed.protocol := by decide
example : (resumed.advance ports input [newer, newer]).resource = resumed.resource := by decide
example : (resumed.advance ports input [newer, newer]).rows.length = 16 := by decide

example : resumed.position 6 0 "tick" 5 21 = .position 2 := by decide
example : lostProtocol.position 6 0 "tick" 5 21 = .unknown := by decide

#print axioms position_valid
#print axioms position_advance_checkpoint
#print axioms resource_facts_advance_checkpoint
#print axioms map_step_valid
#print axioms map_render_eq
#print axioms rule_step_valid
#print axioms rule_render_eq
#print axioms snapshot_step_valid
#print axioms snapshot_advance_valid
#print axioms render_valid
#print axioms resume_valid_snapshot
#print axioms render_advance_checkpoint
#print axioms native_expression
#print axioms native_compile_fields
#print axioms native_compile_clause
#print axioms render_advance_native_clause
#print axioms resolve_complete
#print axioms resolve_fields_complete
#print axioms render_advance_wellformed_clause

end CBCL.CheckpointAll.Tests
