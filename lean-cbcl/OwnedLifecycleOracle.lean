import Lean
import LeanCbcl.ConsensusFree.OwnedLifecycle
open Lean CBCL.ConsensusFree.OwnedLifecycle

def actionJson : Action K N → Json
  | .close k w => Json.mkObj [("kind", toJson "seal"), ("operation", toJson k.val), ("validator", toJson w)]
  | .sign x w => Json.mkObj [("kind", toJson "sign"), ("operation", toJson x.val), ("validator", toJson w)]
  | .effect x w => Json.mkObj [("kind", toJson "effect"), ("operation", toJson x.val), ("validator", toJson w)]
  | .other => Json.mkObj [("kind", toJson "other")]
def snapshot (c : Config V O K N R f) (s : State V O K N) (d : Fin R) : Json :=
  Json.mkObj [
    ("sealed", toJson ((List.range 4).map s.closed)),
    ("signed", toJson ((List.finRange N).map (fun x => (List.range 4).map (s.votes x)))),
    ("effects", toJson ((List.finRange N).map (fun x => (List.range 4).map (s.effects x)))),
    ("operation_qc", toJson ((List.finRange N).map (opCert c s))),
    ("effects_qc", toJson ((List.finRange N).map (finalCert c s))),
    ("balance", toJson (CBCL.ConsensusFree.MultiParent.balance c.old s.old d + newCredit c s d + receivedCredit c s d - newDebit c s d))]
def trace (c : Config V O K N R f) (s : State V O K N) (d : Fin R) : List (Action K N) → List Json
  | [] => []
  | a :: rest =>
    let result := perform c s a
    let next := result.getD s
    Json.mkObj [("action", actionJson a), ("accepted", toJson result.isSome), ("state", snapshot c next d)] :: trace c next d rest

def main : IO Unit := do
  IO.println <| (Json.mkObj [("cases", toJson ([
    Json.mkObj [("name", toJson "initial-unit"), ("initial", toJson (1 : Nat)), ("amounts", toJson ([1] : List Nat)),
      ("trace", toJson (trace Witness.unit initial 0 (Witness.handoff ++ Witness.spend 0)))],
    Json.mkObj [("name", toJson "spend-down"), ("initial", toJson (5 : Nat)), ("amounts", toJson ([4,1] : List Nat)),
      ("trace", toJson (trace Witness.spendDown initial 0 (Witness.handoff ++ Witness.spend 0 ++ Witness.spend 1)))]] : List Json))]).compress
