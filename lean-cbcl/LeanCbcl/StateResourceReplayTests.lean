import LeanCbcl.StateResourceReplay
import LeanCbcl.StateResourceTests

/-! Cited context must remain part of replay even when it is not itself a
resource operation or a recognized role-binding root. -/
set_option autoImplicit false
namespace CBCL.StateResourceReplayTests
open State CheckpointEvidence StateResource StateResourceReplay StateResourceTests

/-- An accepted but malformed root still participates in initialization blame. -/
def malformedRoot : ResourceFact := {root with data := {root.data with
  selected := {root.data.selected with bindings := .absent}}}

/-- Context without a cast is not independently selected as a resource fact. -/
theorem malformed_root_not_relevant : ¬relevant config malformedRoot := by
  simp [relevant,initial,operation,config,malformedRoot,root]

/-- Its opener's citation still places that context inside the certificate. -/
theorem malformed_root_is_named : Named config [malformedRoot,opener,burn] malformedRoot := by
  simp [Named,relevant,initial,operation,cited,config,malformedRoot,root,opener,burn]

/-- A foreign non-resource fact can be referenced by an otherwise valid burn. -/
def foreignFact : ResourceFact := ⟨9,{burn.data with selected := {burn.data.selected with verb := "tell"}}⟩

/-- The foreign verb and absent bindings cannot satisfy direct relevance. -/
theorem foreign_not_relevant : ¬relevant config foreignFact := by
  simp [relevant,initial,operation,config,foreignFact,burn]

/-- A funding dependency cites the foreign fact by identity. -/
def citingBurn : ResourceFact := {burn with data := {burn.data with deps := [9]}}

/-- Foreign evidence is retained through dependency links, not merely protocol
predecessor edges or direct resource-verb selection. -/
theorem foreign_dependency_is_named : Named config [opener,citingBurn,foreignFact] foreignFact := by
  simp [Named,relevant,initial,operation,cited,links,config,foreignFact,citingBurn,burn,opener]

end CBCL.StateResourceReplayTests
