import LeanCbcl.CheckpointData

/-! Kernel-reduced hostile examples and theorem dependency audit. -/
namespace CBCL.CheckpointData.Tests
open State StateKernelSemantics StateKernelQueries StateKernel CheckpointSummary
open CheckpointData

private def event (id : Nat) (verb signer : String) (value : Option Val)
    (amount : Option Val := none) : Act :=
  ⟨id, verb, signer, [],
    (value.toList.map (fun v => ("value", v))) ++
      (amount.toList.map (fun v => ("amount", v))) ++
      [("unrelated", .str "not retained by events")], []⟩

private def a := event 1 "put" "@a" (some (.str "red")) (some (.int 7))
private def b := event 2 "put" "@b" (some (.str "blue")) (some (.int (-3)))
private def missing := event 3 "put" "@a" none (some (.str "not an integer"))
private def down := event 4 "drop" "@a" none (some (.int 11))
private def other := event 5 "noise" "@a" (some (.str "ignored")) (some (.int 999))
private def all := [a, b, missing, down, other, a, down]

example : (Machine.checkpoint Exists.empty (Exists.step "put") []).data = false := by decide
example : (Machine.checkpoint Exists.empty (Exists.step "put") [other]).data = false := by decide
example : (Machine.checkpoint Exists.empty (Exists.step "put") all).data = true := by decide
example : (Machine.checkpoint Count.empty (Count.step "put") all).data = 3 := by decide
example : (Machine.checkpoint Counter.empty (Counter.step "put" "drop" "amount") all).data = -7 := by decide
-- The two predicates are independent: equal increment/decrement verbs cancel.
example : (Machine.checkpoint Counter.empty (Counter.step "put" "put" "amount") all).data = 0 := by decide

private def huge := event 6 "put" "@a" none (some (.int (10^40)))
example : (Machine.checkpoint Counter.empty (Counter.step "put" "drop" "amount")
    [huge, huge]).data = 10^40 := by decide

private def union := Machine.checkpoint SetUnion.empty (SetUnion.step "put" "value") all
example : SetUnion.render union.data (.str "red") = true := by decide
example : SetUnion.render union.data (.str "blue") = true := by decide
example : SetUnion.render union.data (.str "ignored") = false := by decide
example : union.data.length = 2 := by decide

private def events := Machine.checkpoint Events.empty (Events.step "put" "value") all
example : events.data.length = 2 := by decide
example : Events.read events.data 1 = some ("@a", .str "red") := by decide
example : Events.read events.data 2 = some ("@b", .str "blue") := by decide
example : Events.read events.data 3 = none := by decide
example : Events.read events.data 5 = none := by decide
example : events.coverage 3 = true := by decide
-- Even an output-ineligible arrival enters the common identity coverage set.
example : events.coverage 5 = true := by decide
example : (Events.map events.data).keys.Nodup := Events.map_keys_nodup _
example : (Events.map events.data).read (.int 1) = .event "@a" (.str "red") := by decide
example : (Events.map events.data).read (.int (-1)) = .absent := by decide
example : (.int 3 : Val) ∉ (Events.map events.data).keys := by decide

private def money := event 8 "put" "@a" (some (.int 23))
private def refund := event 9 "put" "@b" (some (.int (-5)))
private def numericEvents := Machine.checkpoint Events.empty (Events.step "put" "value")
  [money, refund, money, missing, other]
example : numericEvents.data.length = 2 := by decide
example : StateKernelAggregates.mapSum (Events.map numericEvents.data) = 18 := by decide

private def first := [a, missing, other]
private def tail := [a, b, down, down]
example :
    Machine.Valid (Count.Invariant "put") (normalize (first ++ tail))
      (Machine.advance (Count.step "put")
        (Machine.checkpoint Count.empty (Count.step "put") first) tail) :=
  count_continuation "put" first tail
example :
    Machine.Valid (Events.Invariant "put" "value") (normalize (first ++ tail))
      (Machine.advance (Events.step "put" "value")
        (Machine.checkpoint Events.empty (Events.step "put" "value") first) tail) :=
  events_continuation "put" "value" first tail

-- Explicit rejection of tempting lossy/broken updates.
example : (Count.step "put" (fun _ => false) 1 a) ≠ 1 := by decide
example : (Events.step "put" "value" (fun _ => false) [] missing).length = 0 := by decide
example : (Events.step "put" "value" (fun _ => true) [] a) = [] := by decide

example (v : String) (H D : List Act) :
    Exists.Invariant v (normalize (H ++ D))
      (Machine.advance (Exists.step v) (Machine.checkpoint Exists.empty (Exists.step v) H) D).data :=
  (exists_continuation v H D).2
example (v f : String) (H D : List Act) :
    SetUnion.render
        (Machine.advance (SetUnion.step v f)
          (Machine.checkpoint SetUnion.empty (SetUnion.step v f) H) D).data =
      State.setUnion v f (normalize (H ++ D)) :=
  SetUnion.render_native (setUnion_continuation v f H D).2
example (v f : String) (H D : List Act) :
    Events.read
        (Machine.advance (Events.step v f)
          (Machine.checkpoint Events.empty (Events.step v f) H) D).data =
      StateKernelSemantics.events f (acts v (normalize (H ++ D))) :=
  Events.read_native (events_continuation v f H D).2 (normalize_unique _)
example (input : Input) (v f : String) (H D : List Act) :
    MapEquivalent
      (Events.map (Machine.advance (Events.step v f)
        (Machine.checkpoint Events.empty (Events.step v f) H) D).data)
      (evalMap input.clock input.signerRank (normalize (H ++ D))
        ⟨.withField (.verb v) f, .address, .address, f, true⟩) :=
  Events.map_native input (events_continuation v f H D).2 (normalize_unique _)

#print axioms Exists.step_preserves
#print axioms Count.step_preserves
#print axioms Counter.step_preserves
#print axioms SetUnion.step_preserves
#print axioms Events.step_preserves
#print axioms Events.read_native
#print axioms Events.map_keys_nodup
#print axioms Events.map_meaning
#print axioms Events.map_native
#print axioms exists_continuation
#print axioms count_continuation
#print axioms counter_continuation
#print axioms setUnion_continuation
#print axioms events_continuation

end CBCL.CheckpointData.Tests
