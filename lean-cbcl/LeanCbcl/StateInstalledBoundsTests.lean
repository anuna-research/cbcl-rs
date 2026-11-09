import LeanCbcl.StateFiniteIndexBounds
import LeanCbcl.StateAuthoredBindingsTests

/-! R7 bounds precede typed authored construction. Machine-index fixtures cover
both native word sizes and their exact row-major table reads. -/
namespace CBCL.StateInstalledBoundsTests
open State StateInstalledBounds StateAuthoredBindings

/-- Fixed native defaults pass the recognized gate. -/
theorem defaults_accepted : check defaults = true := by decide

/-- Positive tightenings of all four bounds remain supported. -/
theorem tightening_accepted : check ⟨3,4,5,6⟩ = true := by decide

/-- The list default is an installation ceiling, not just a table fallback. -/
theorem larger_list_rejected : check ⟨32,65,1000000000000,2048⟩ = false := by decide

/-- Zero is rejected before any table or source construction. -/
theorem zero_list_rejected : check ⟨32,0,1000000000000,2048⟩ = false := by decide

/-- Other state-bound defaults are checked independently. -/
theorem larger_fields_rejected : check ⟨33,64,1000000000000,2048⟩ = false := by decide

/-- Signed numeric bounds must also remain positive. -/
theorem negative_number_rejected : check ⟨32,64,-1,2048⟩ = false := by decide

/-- A string bound cannot exceed its default. -/
theorem larger_string_rejected : check ⟨32,64,1000000000000,2049⟩ = false := by decide

/-- The last slot of the maximum installed square table is representable on 32 bits. -/
theorem maximum_offset32 : (UInt32.ofNat 63 * UInt32.ofNat 64 + UInt32.ofNat 63).toNat = 4095 := by decide

/-- The identical slot has the same value on 64 bits. -/
theorem maximum_offset64 : (UInt64.ofNat 63 * UInt64.ofNat 64 + UInt64.ofNat 63).toNat = 4095 := by decide

/-- The final physical-slice loop start does not wrap at the 32-bit boundary. -/
theorem final_next32 : (UInt32.ofNat (2^32-2) + 1).toNat = 2^32-1 := by decide

/-- The final physical-slice loop start also does not wrap on 64 bits. -/
theorem final_next64 : (UInt64.ofNat (2^64-2) + 1).toNat = 2^64-1 := by decide

end CBCL.StateInstalledBoundsTests
