import LeanCbcl.ConsensusFree.Tests
open CBCL.ConsensusFree.Tests

def main : IO Unit := do
  let mut passed := 0
  let mut failed : List String := []
  for (name, result) in checks do
    if result then passed := passed + 1 else failed := name :: failed
  if !failed.isEmpty then
    for name in failed.reverse do IO.eprintln ("FAIL: " ++ name)
    throw (IO.userError "consensus-free executable regression failed")
  IO.println ("{\"passed\":" ++ toString passed ++
    ",\"result\":\"pass\",\"scope\":\"consensus-free independent budget and checkpoint regressions\"}")
