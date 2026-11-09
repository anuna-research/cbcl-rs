import LeanCbcl.StateFiniteReadCache
import LeanCbcl.StateFiniteReadTests

/-! Once-decoded finite read caches preserve original scalar identity and
row-major failure diagnostics. Raw-stage tests do not bypass admission. -/
set_option autoImplicit false
namespace CBCL.StateFiniteReadCacheTests
open State StateFiniteUpperCache StateFinitePairLoop StateFiniteReadCache

/-- Existing checked numeric source, with a non-top zero projection. -/
def field : StateInstalledFinite.Field := StateFiniteReadTests.field

/-- Both scalar kinds can decode to numeric one; they remain distinct originals.
This raw cache stage does not assert that both kinds are admitted together. -/
theorem scalar_identity_retained : compileReads field [.bool true,.int 1] =
    some [(.bool true,.numeric 1),(.int 1,.numeric 1)] := by rfl

/-- Equal decoded values do not invent a duplicate scalar diagnostic. -/
theorem decoded_equality_not_duplicate : diagnostic field [.bool true,.int 1] = some none := by decide

/-- Actual source-owned admission still rejects the heterogeneous pair. -/
theorem mixed_kinds_rejected : StateFiniteReadCache.check field [.bool true,.int 1] = false := by decide

/-- False is not a native finite boolean threshold alternative. -/
theorem false_not_decoded : compileReads field [.bool false] = none := by rfl

/-- Unknown names fail the cache stage rather than producing an unchecked index. -/
theorem unknown_not_decoded : compileReads field [.str "unknown"] = none := by rfl

/-- Duplicate takes precedence when the same pair is also compatible. -/
theorem duplicate_first : diagnostic field [.int 0,.int 0] = some (some (0,1,.duplicate)) := by decide

/-- Named/numeric compatibility reports the actual original indices. -/
theorem mixed_pair_compatible : diagnostic field [.str "empty",.int 0] = some (some (0,1,.compatible)) := by decide

/-- The scanner skips clear earlier rows and reports the first later duplicate. -/
theorem later_duplicate : diagnostic field [.int 1,.int 0,.int 0] = some (some (1,2,.duplicate)) := by decide

/-- Negative numeric thresholds use the non-top maximum without clamping to zero. -/
theorem negative_compatible : diagnostic field [.int (-1),.int (-2)] = some (some (0,1,.compatible)) := by decide

/-- Empty alternatives fail despite an empty cache being constructible. -/
theorem empty_rejected : StateFiniteReadCache.check field [] = false := by decide

/-- The conflict-top name is rejected before the pair stage. -/
theorem top_rejected : StateFiniteReadCache.check field [.str "conflict"] = false := by decide

/-- Native signed bound checking remains part of admission before decoding use. -/
theorem oversized_rejected : StateFiniteReadCache.check field [.int (2^63)] = false := by decide

/-- Cached validation is actually used by the scalar wrapper for installed code. -/
theorem wrapped_policy_rejects : policyCheck field [.element (.scalar (.str "empty")),.element (.scalar (.int 0))] = false := by decide

end CBCL.StateFiniteReadCacheTests
