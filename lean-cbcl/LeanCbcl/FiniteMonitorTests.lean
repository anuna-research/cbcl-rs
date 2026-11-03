import LeanCbcl.FiniteMonitor
import LeanCbcl.FiniteForestTests
import LeanCbcl.MonitoredDCFL

namespace CBCL.FormalLanguage.MonitorTests
open ForestTests

/-- Reject any word containing an atom. Structural tokens leave control alone. -/
def noAtoms : Monitor 3 2 where
  initial := 0
  transition s t := if t == 2 then 1 else s
  finalState s := s == 0

example : (Monitor.product oneList.machine noAtoms).accepts [0, 1] = true := by decide
-- The parser accepts this word; the monitor must reject it.
example : oneList.machine.accepts [0, 2, 1] = true := by decide
example : (Monitor.product oneList.machine noAtoms).accepts [0, 2, 1] = false := by decide
-- The monitor accepts these malformed words; the parser must reject them.
example : noAtoms.accepts [1] = true := by decide
example : (Monitor.product oneList.machine noAtoms).accepts [1] = false := by decide
example : (Monitor.product oneList.machine noAtoms).accepts [0, 0, 1] = false := by decide
example : (Monitor.product oneList.machine noAtoms).accepts [0, 1, 1] = false := by decide
example : (Monitor.product oneList.machine noAtoms).accepts [] = false := by decide
-- Failure remains failure even if later input could finish a valid list.
example : (Monitor.product oneList.machine noAtoms).accepts [1, 0, 1] = false := by decide

/-- The generic closure theorem supplies the full language certificate. -/
def certificate := ForestTests.certificate.restrict noAtoms

end CBCL.FormalLanguage.MonitorTests

namespace CBCL.InstalledSyntax.Raw.MonitorTests
open FormalLanguage

/-- A raw input restriction whose finite state remembers a line feed. -/
def singleLine : Monitor 0x10f800 2 where
  initial := 0
  transition s t := if t.val == 10 then 1 else s
  finalState s := s == 0

-- Exercise the installed raw syntax and monitor together through the proved
-- reference equality, avoiding execution of enormous encoded control states.
example : (monitoredDCFL [] singleLine).machine.accepts (encode "(tell)") = true := by
  rw [monitored_check_correct]
  decide

example : check [] "(tell\n)" = true := by decide
example : (monitoredDCFL [] singleLine).machine.accepts (encode "(tell\n)") = false := by
  rw [monitored_check_correct]
  decide

example : singleLine.accepts (encode "(tell") = true := by decide
example : (monitoredDCFL [] singleLine).machine.accepts (encode "(tell") = false := by
  rw [monitored_check_correct]
  decide

end CBCL.InstalledSyntax.Raw.MonitorTests
