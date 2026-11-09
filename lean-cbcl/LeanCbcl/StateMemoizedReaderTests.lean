import LeanCbcl.StateMemoizedReader

/-! Executable cache-machine witnesses for distinct scopes, distinct fields,
dynamic terminal faults and cut redirection. Values intentionally keep frozen
wrappers so forgetting to unwrap a dependency is observable. -/
namespace CBCL.StateMemoizedReaderTests
open StateMemoizedReader

/-- Small presentation carrier for operational cache regression witnesses. -/
inductive Value where
  | snapshot (amount : Nat)
  | frozen (amount : Nat)
  | fault (evidence : List Nat)
  deriving BEq, DecidableEq

/-- The native payload boundary preserves faults and strips frozen metadata. -/
def unwrap : Value → Value
  | .frozen amount => .snapshot amount
  | value => value

/-- Two fields freeze at incomparable cuts: whole events expose 2 while the
sum's own cut reads 7. This reproduces the native live-oracle cache witness. -/
def ops : Operations Value := {
  dependency := fun field => if field = "sum" then some "events" else none
  cut := fun field => if field = "events" then some 1 else if field = "sum" then some 2 else none
  active := fun key => key.1 = 0 || (key.2 = "events" && key.1 = 1) || (key.2 = "sum" && key.1 = 2)
  unfrozen := unwrap
  normal := fun key dependency => if key.2 = "events" then .snapshot (if key.1 = 2 then 7 else 2)
    else match dependency with | some (.snapshot amount) => .snapshot amount | _ => .fault [99]
  fault := fun _ value => match value with | .fault evidence => some (.fault evidence) | _ => none
  frozen := fun _ value => match value with | .snapshot amount | .frozen amount => .frozen amount | .fault evidence => .fault evidence }

/-- Field order is distinct from scope order: dependencies are earlier fields. -/
def index (field : String) : Nat := if field = "sum" then 1 else 0

/-- A cached source frozen at one cut cannot determine a derived field frozen
at an incomparable cut. -/
theorem incomparable_cut_values : (match reads ops.body (requestRank index ops.cut) [(0,"events"),(0,"sum")] [] with
  | some (values,_) => values == [.frozen 2,.frozen 7]
  | none => false) = true := by decide

/-- Field request order preserves the meaning of each complete scope/field key. -/
theorem different_request_order : (match reads ops.body (requestRank index ops.cut) [(0,"sum"),(0,"events"),(2,"events")] [] with
  | some (values,_) => values == [.frozen 7,.frozen 2,.snapshot 7]
  | none => false) = true := by decide

#guard read ops.body 0 (0,"sum") [] == none
#guard read ops.body 0 (2,"events") [((2,"events"),.snapshot 7)] == some (.snapshot 7,[((2,"events"),.snapshot 7)])

/-- A terminal fault retains its complete witnesses and avoids its own cut
request after normal dependencies have been evaluated. -/
def faulting : Operations Value := { ops with
  fault := fun key value => if key.2 = "sum" then some (.fault [11,12]) else ops.fault key value }

/-- Complete terminal witnesses return without requesting the faulted field's cut. -/
theorem fault_shortcircuit : (match reads faulting.body (requestRank index faulting.cut) [(0,"sum")] [] with
  | some (values,cache) => values == [.fault [11,12]] && cache.lookup (2,"sum") == none
  | none => false) = true := by decide

end CBCL.StateMemoizedReaderTests
