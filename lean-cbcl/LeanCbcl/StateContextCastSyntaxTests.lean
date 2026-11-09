import LeanCbcl.StateContextCastSyntax

/-! Raw grammar recognition precedes installed cast semantics. -/
namespace CBCL.StateContextCastSyntaxTests
open CheckpointEvidence StateInstalledContext StateContextCastSyntax

/-- Representative installed singleton and indexed roles. -/
def definition : Definition := ⟨"demo","digest","body",none,[⟨"chair",false⟩,⟨"reviewer",true⟩],⟨32,64,1000000000000,2048⟩,none⟩

/-- Well-formed complete binding data remains accepted. -/
theorem valid_cast : recognize definition (encode [⟨"chair",["@chair"]⟩,⟨"reviewer",["@a","@b"]⟩]) =
    some [⟨"chair",["@chair"]⟩,⟨"reviewer",["@a","@b"]⟩] := by decide

/-- Syntax recognition retains duplicates so the semantic gate can reject them. -/
theorem duplicate_rejected : recognize definition (encode [⟨"chair",["@chair"]⟩,⟨"reviewer",["@a","@a"]⟩]) = none := by decide

/-- Syntax success does not conceal a missing installed role. -/
theorem missing_rejected : recognize definition (encode [⟨"chair",["@chair"]⟩]) = none := by decide

/-- Empty indexed rosters are rejected by semantics, not normalized to absence. -/
theorem empty_rejected : recognize definition (encode [⟨"chair",["@chair"]⟩,⟨"reviewer",[]⟩]) = none := by decide

/-- Malformed grammar retains an explicit fault-bearing metadata field. -/
theorem malformed_not_absent : field (.atom (.bool true)) = .malformed .malformedBinding := rfl

end CBCL.StateContextCastSyntaxTests
