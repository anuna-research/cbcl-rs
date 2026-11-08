import LeanCbcl.StateContextWrapperSyntax
import LeanCbcl.StateContextCastSyntaxTests

/-! Pin grammar and exact wrapper positions precede installed role semantics. -/
namespace CBCL.StateContextWrapperSyntaxTests
open StateContextWrapperSyntax
open StateContextCastSyntax (encode)

/-- Fixed valid digest, independent of cryptographic computation. -/
def digest : String := "sha256:" ++ String.ofList (List.replicate 64 'a')

/-- Exact native prefix/length/alphabet is recognized. -/
theorem valid_digest : pinCheck digest = true := by decide

/-- The wire string form and typed-symbol compatibility agree. -/
theorem pin_kinds : pin (.atom (.str digest)) = some digest ∧ pin (.atom (.symbol digest)) = some digest := by decide

/-- Prefix spelling is exact. -/
theorem wrong_prefix : pinCheck ("sha512:" ++ String.ofList (List.replicate 64 'a')) = false := by decide

/-- Digest length is exact in both directions. -/
theorem wrong_length : pinCheck ("sha256:" ++ String.ofList (List.replicate 63 'a')) = false ∧
    pinCheck ("sha256:" ++ String.ofList (List.replicate 65 'a')) = false := by decide

set_option maxRecDepth 2048 in
/-- Uppercase and Unicode lookalikes are outside the ASCII digest grammar. -/
theorem invalid_alphabet : pinCheck ("sha256:" ++ String.ofList (List.replicate 64 'A')) = false ∧
    pinCheck ("sha256:" ++ String.ofList (List.replicate 64 '𝟘')) = false := by decide

/-- Nontext atoms never become digest strings. -/
theorem bool_pin_rejected : pin (.atom (.bool true)) = none := rfl

/-- Valid pinned casts produce the same role rows. -/
theorem wrapper_accepted : recognize {StateContextCastSyntaxTests.definition with address := digest}
    [encode [⟨"chair",["@chair"]⟩,⟨"reviewer",["@a"]⟩],.atom (.keyword "dialect"),.atom (.str digest)] =
      some [⟨"chair",["@chair"]⟩,⟨"reviewer",["@a"]⟩] := by decide

/-- Unknown parameter keywords are not repaired into dialect pins. -/
theorem unknown_keyword : decode [encode [],.atom (.keyword "other"),.atom (.str digest)] = none := by decide

/-- Wrong wrapper shape remains malformed context metadata. -/
theorem malformed_wrapper : (metadata none []).cast = .malformed .malformedBinding := rfl

end CBCL.StateContextWrapperSyntaxTests
