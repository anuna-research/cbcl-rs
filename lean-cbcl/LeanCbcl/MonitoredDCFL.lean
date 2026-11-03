import LeanCbcl.FiniteMonitor
import LeanCbcl.InstalledLexer

/-!
# Installation preserves DCFL under finite-state input restrictions

These certificates combine the installed recursive raw-character language
with any finite monitor over Unicode scalar codes. The monitor's state count
is fixed for a certificate, independently of word length. This does not
claim that arbitrary state-rule predicates or Rust validation are regular.
-/
namespace CBCL.InstalledSyntax.Raw
open FormalLanguage

/-- Both the installed grammar and the monitor must accept the complete word. -/
def monitoredLanguage (ds : List Dialect) (D : Monitor 0x10f800 m)
    (w : List ScalarCode) : Prop := language ds w ∧ D.accepts w = true

/-- Finite-state restrictions preserve the raw-language certificate. -/
def monitoredDCFL (ds : List Dialect) (D : Monitor 0x10f800 m) :
    IsRealtimeDCFL (monitoredLanguage ds D) :=
  (environmentDCFL ds).restrict D

/-- A fresh concrete product witness exists after every finite installation
sequence, without a bound on the number of installations. -/
def monitored_dcfl_preserved_many (a : Agent) (ds : List Dialect)
    (D : Monitor 0x10f800 m) :
    IsRealtimeDCFL (monitoredLanguage (installMany a ds).dialects D) :=
  monitoredDCFL (installMany a ds).dialects D

/-- The certificate also holds for sequences selected by any admission policy. -/
def monitored_accepted_installations_dcfl {accept : Agent → Dialect → Prop}
    {a b : Agent} {ds : List Dialect} (h : AcceptedInstalls accept a ds b)
    (D : Monitor 0x10f800 m) : IsRealtimeDCFL (monitoredLanguage b.dialects D) :=
  (accepted_installations_dcfl h).restrict D

/-- Executable equivalence with the existing lexer and reference checker;
this theorem quantifies over every source string, not a test corpus. -/
theorem monitored_check_correct (ds : List Dialect) (D : Monitor 0x10f800 m)
    (source : String) :
    (monitoredDCFL ds D).machine.accepts (encode source) =
      (check ds source && D.accepts (encode source)) := by
  change (Monitor.product (environmentDCFL ds).machine D).accepts (encode source) = _
  rw [Monitor.product_accepts, check_correct]

end CBCL.InstalledSyntax.Raw
