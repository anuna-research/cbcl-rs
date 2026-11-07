import Lean
import LeanCbcl.CheckpointEvidence

/-!
Two legacy configuration-policy constants only. This independent port does not
implement account arithmetic, quorum certification, wire extraction, signatures,
or native admission. No expected Rust outcomes enter this oracle.
-/
open Lean CBCL.State CBCL.StateKernelExtensions CBCL.CheckpointEvidence
namespace CheckpointResourcePolicyOracle
inductive Policy where | collective | quorum

def classify : Policy → List ResourceFact → String → ResourceInput
  | .collective, _, _ => .fault "collective counter requires the certificate runtime" []
  | .quorum, _, _ => .fault "quorum-budget requires an explicit certificate runtime; legacy fold cannot prove finality" []

def extract (a : Act) : ResourceData :=
  ⟨a.signer, .other, 0, none, [], { resource := "resource" }⟩

def port (p : Policy) : ResourcePort where
  extract := extract
  classify := classify p
  classify_ext := by intro _ _ _; cases p <;> rfl

def act (id : Nat) : Act := ⟨id, "tell", "@typed", [], [], []⟩

def viewJson : ResourceView → Json
  | .fault reason evidence => Json.mkObj [("status", .str "fault"),
      ("reason", .str reason), ("evidence", toJson evidence)]
  | .pending evidence => Json.mkObj [("status", .str "pending"), ("evidence", toJson evidence)]
  | .ready .. => Json.mkObj [("status", .str "unexpected-ready")]

def rows (p : Policy) (name : String) : List Json := Id.run do
  let history := [act 1, act 2, act 1]
  let mut out := []
  for n in List.range (history.length + 1) do
    let accepted := history.take n
    for cut in List.range (n + 1) do
      let result := (port p).observe
        (advance (checkpoint extract (accepted.take cut)) (project extract (accepted.drop cut))) "resource"
      out := out ++ [Json.mkObj [("policy", .str name), ("prefix", toJson n),
        ("cut", toJson cut), ("observation", viewJson result)]]
  return out
end CheckpointResourcePolicyOracle

def main : IO Unit :=
  IO.println ((Lean.toJson ((CheckpointResourcePolicyOracle.rows .collective "collective") ++
    (CheckpointResourcePolicyOracle.rows .quorum "quorum"))).compress)
