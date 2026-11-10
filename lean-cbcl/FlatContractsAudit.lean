import FlatContractsOracle
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open CBCL.FlatContracts

#print axioms comparison_correct
#print axioms checker_correct
#print axioms bounded_acceptance
#print axioms bounded_violation
#print axioms preserves_value
#print axioms reservation_permutation
#print axioms resolve_iff_expansion
#print axioms resolution_semantics
#print axioms resolve_permutation
#print axioms resolved_descendant_no_cycle
#print axioms unused_cycle_rejected
#print axioms FlatContractsOracle.backend_correct

/-- Rational equality does not merge enumeration representations. -/
example : Atom.integer 1 ≠ Atom.float 4607182418800017408 := integer_not_float _ _
example : Atom.integer 1 ≠ Atom.decimal 1 0 := integer_not_decimal _ _ _
example : (Atom.float 4607182418800017408).numeric = (Atom.integer 1).numeric := by decide
example : (Atom.decimal 1 0).numeric = (Atom.integer 1).numeric := by decide
example : (Atom.float 1).numeric = some (Rat.normalize 1 (2^1074) (by decide)) := by decide
example : (Atom.float 4591870180066957722).numeric ≠ (Atom.decimal 1 1).numeric := by decide
example : (Atom.integer (-9223372036854775808)).Valid := by decide
example : ¬(Atom.integer 9223372036854775808).Valid := by decide
example : (Value.atom (.string "😀")).length = some 1 := by decide
example : (Value.atom (.string "é")).length = some 2 := by decide

example : Cmp.gt.Denotes (binary64 4591870180066957722) (Rat.normalize 1 10 (by decide)) := by
  apply (comparison_correct _ _ _).mp
  decide
