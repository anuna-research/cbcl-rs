import LeanCbcl.StateFiniteDenseCache
import LeanCbcl.StateFiniteReadCacheTests

/-! Both word widths exercise the complete dense cache pipeline. -/
namespace CBCL.StateFiniteDenseCacheTests
open State StateFiniteDenseCache StateFiniteReadCache

/-- Validated numeric fixture used by the differential oracle proof family. -/
def field := StateFiniteReadCacheTests.field

/-- A named/numeric overlapping pair is rejected on both backends. -/
theorem mixed_rejected : check .bits32 field [.str "empty",.int 0] = false ∧
    check .bits64 field [.str "empty",.int 0] = false := by decide

/-- Original indices and duplicate precedence survive both dense caches. -/
theorem later_duplicate :
    (compileReads field [.int 1,.int 0,.int 0]).map (densePairs .bits32 field (denseMaxima .bits32 field) 0) = some (some (1,2,.duplicate)) ∧
    (compileReads field [.int 1,.int 0,.int 0]).map (densePairs .bits64 field (denseMaxima .bits64 field) 0) = some (some (1,2,.duplicate)) := by decide

/-- The absent non-top numeric witness must reject neither scalar singleton. -/
theorem singleton_accepted : check .bits32 field [.int 1] = true ∧ check .bits64 field [.int 1] = true := by decide

/-- Empty alternatives remain invalid after backend substitution. -/
theorem empty_rejected : check .bits32 field [] = false ∧ check .bits64 field [] = false := by decide

end CBCL.StateFiniteDenseCacheTests
