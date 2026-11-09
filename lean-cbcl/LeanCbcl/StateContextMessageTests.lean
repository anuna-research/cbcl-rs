import LeanCbcl.StateContextMessage
import LeanCbcl.StateContextCastSyntaxTests

/-! Typed message traversal and outer nomination precedence. -/
namespace CBCL.StateContextMessageTests
open StateContextMessage StateContextCastSyntax

/-- A valid role wrapper nested below independent message envelopes. -/
def inner : StateContextMessage.Message := .wrapped .withRoles
  [encode [⟨"chair",["@chair"]⟩,⟨"reviewer",["@a","@b"]⟩]] (.simple (some "thread"))

/-- All transparent native categories preserve cast nomination. -/
theorem transparent_wrappers : nativeCast StateContextCastSyntaxTests.definition
    (.wrapped .envelope [] (.dialect "demo" (.wrapped .signed [] (.wrapped .withLimits [] inner)))) =
      some [⟨"chair",["@chair"]⟩,⟨"reviewer",["@a","@b"]⟩] := by decide

/-- An invalid outer sealed cast cannot fall back to a valid inner one. -/
theorem malformed_outer_shadows : nativeCast StateContextCastSyntaxTests.definition
    (.wrapped .withRoles [] inner) = none := by decide

/-- Shadowing does not conceal the underlying simple thread. -/
theorem shadowed_thread : (metadata (.wrapped .withRoles [] inner)).thread = some "thread" := rfl

/-- Missing casts on role-bearing definitions fail. -/
theorem missing_cast_rejected : nativeCast StateContextCastSyntaxTests.definition (.simple none) = none := by decide

/-- Role-free definitions need no cast but still reject malformed nominations. -/
theorem role_free : nativeCast {StateContextCastSyntaxTests.definition with roles := []} (.simple none) = some [] ∧
    nativeCast {StateContextCastSyntaxTests.definition with roles := []} (.wrapped .withRoles [] (.simple none)) = none := by decide

end CBCL.StateContextMessageTests
