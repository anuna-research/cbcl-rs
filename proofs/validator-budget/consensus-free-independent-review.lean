import LeanCbcl.ConsensusFree.Tests

namespace CBCL.ConsensusFree.IndependentReview
open CBCL.ConsensusFree.Tests
open CBCL.ConsensusFree.Currency

def incomingBeforeProof := after (signs 2 ++ finish 2 ++ seals (.root 1) ++
  endorseWith 7 ++ [.record 7 0])

def unsignedContext : Context 2 14 10 := { context with ownerSigned := fun _ => false }
def unsignedCfg := Currency.config unsignedContext committee

def checks : List (String × Bool) := [
  ("credited checkpoint rejects installation without local final proof",
    (perform cfg incomingBeforeProof (.install 7 0)).isNone),
  ("same checkpoint installs after receiving its final proof",
    decide ((run cfg incomingBeforeProof [.receiveFinal 2 0, .install 7 0]).2.active 0 1 = .checkpoint 7)),
  ("operation certificate alone cannot fund manifested incoming credit",
    (perform cfg (after (signs 2 ++ seals (.root 1))) (.endorse 7 0)).isNone),
  ("descendant refund rejects absent cancellation evidence",
    (perform cfg (after (closedTriangle ++ seals (.checkpoint 0))) (.endorse 1 0)).isNone),
  ("missing owner authentication rejects otherwise funded payment",
    (perform unsignedCfg (initial unsignedCfg) (.sign 2 0)).isNone),
  ("Byzantine signature cannot finalize unauthorized issuance",
    !(finalCert cfg (after ([.sign 11 3] ++ finish 11 ++ [.effect 11 3])) 11)),
  ("repeated effects emit exactly one business label",
    decide (currentLabel (signs 7 ++ finish 7 ++ finish 7 ++ [.effect 7 3]) = [7])),
  ("preemptive cancellation permits late operation certificate but prevents finality",
    operationCert cfg (after (cancel 5 ++ signs 5 ++ finish 5)) 5 &&
      !(finalCert cfg (after (cancel 5 ++ signs 5 ++ finish 5)) 5))
]

def main : IO Unit := do
  let mut passed := 0
  for (name, result) in checks do
    if result then passed := passed + 1
    else throw (IO.userError ("FAIL: " ++ name))
  IO.println ("Independent review checks passed: " ++ toString passed)

end CBCL.ConsensusFree.IndependentReview

def main := CBCL.ConsensusFree.IndependentReview.main
