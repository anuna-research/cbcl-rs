/-
  Executable oracle for dialect enactability.

  Reads one JSON request per line and answers with the definitions that
  `LeanCbcl/DialectEnactability.lean` proves theorems about. It receives `then` edges and
  questions, never Rust verdicts. The Rust side is
  `crates/cbcl-parser/tests/enactability_oracle.rs`.

  Request:
    { "edges":   [[node, node], …],            -- (predecessor, successor) per `then` edge
      "words":   [[name, …], …],               -- candidate arrival-order traces
      "queries": [{ "seen": [name, …], "step": name }, …] }
  where a node is ["single", n], ["any", n, …] or ["all", n, …].

  Response:
    { "steps":       [{ "name", "preds": [node, …], "succs": [name, …],
                        "neighbors": [name, …] }, …],
      "acyclic":     bool,                      -- `(graphOf es).checkAcyclicity = []`
      "unenactable": [name, …],                 -- `unenactableSteps (roleOf ann es)`
      "traces":      [bool, …],                 -- `CausalTrace (roleOf ann es) w`
      "enabled":     [bool, …] }                -- `enabled (roleOf ann es) seen step`

  `preds` is read through the same first-declaration lookup the theorems use, `succs` is
  `succsOf` (successor names in edge order, with repetitions), and `neighbors` is
  `graphNeighbors` on the successor graph of `graphOf` (no repetitions).
-/
import Lean
import LeanCbcl.DialectEnactability

open Lean CBCL CBCL.R6DCFLPreservation CBCL.DialectEnactability

namespace EnactabilityOracle

abbrev Check := Except String

def strs (js : List Json) : Check (List String) := js.mapM (fun j => j.getStr?)

def node (j : Json) : Check PredClause := do
  match (← j.getArr?).toList with
  | [.str "single", .str n] => pure (.single n)
  | .str "any" :: ns => return .anyOf (← strs ns)
  | .str "all" :: ns => return .allOf (← strs ns)
  | _ => throw "invalid node"

def edge (j : Json) : Check Edge := do
  match (← j.getArr?).toList with
  | [p, s] => return (← node p, ← node s)
  | _ => throw "invalid edge"

def nodeJson : PredClause → Json
  | .single n => Json.arr #[.str "single", .str n]
  | .anyOf ns => Json.arr (#[Json.str "any"] ++ (ns.map Json.str).toArray)
  | .allOf ns => Json.arr (#[Json.str "all"] ++ (ns.map Json.str).toArray)

/-- Role annotations do not affect any answer; a fixed one is used. -/
def ann : String → String × List String := fun _ => ("", [])

def items (j : Json) (key : String) : Check (List Json) := do
  return (← (← j.getObjVal? key).getArr?).toList

def run (j : Json) : Check Json := do
  let es ← (← items j "edges").mapM edge
  let words ← (← items j "words").mapM (fun w => do strs (← w.getArr?).toList)
  let queries ← (← items j "queries").mapM (fun q => do
    let seen ← strs (← items q "seen")
    let step ← (← q.getObjVal? "step").getStr?
    pure (seen, step))
  let P := roleOf ann es
  let g := graphOf es
  let steps := (edgeNames es).map (fun n =>
    let preds := match P.find? (fun st => st.name == n) with
      | some st => st.preds
      | none => []
    Json.mkObj [
      ("name", .str n),
      ("preds", Json.arr (preds.map nodeJson).toArray),
      ("succs", Json.arr ((succsOf es n).map Json.str).toArray),
      ("neighbors", Json.arr ((graphNeighbors g.successorGraph n).map Json.str).toArray)])
  return Json.mkObj [
    ("steps", Json.arr steps.toArray),
    ("acyclic", .bool g.checkAcyclicity.isEmpty),
    ("unenactable", Json.arr ((unenactableSteps P).map Json.str).toArray),
    ("traces", Json.arr (words.map (fun w => Json.bool (decide (CausalTrace P w)))).toArray),
    ("enabled", Json.arr (queries.map (fun (seen, t) =>
      Json.bool (enabled P (fun x => seen.contains x) t))).toArray)]

end EnactabilityOracle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let answer := match Json.parse line >>= EnactabilityOracle.run with
      | .error error => Json.mkObj [("error", .str error)]
      | .ok response => response
    stdout.putStrLn answer.compress
    stdout.flush
