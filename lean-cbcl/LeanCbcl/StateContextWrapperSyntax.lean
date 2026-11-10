import LeanCbcl.StateContextCastSyntax

/-! Recognition of with-roles parameters before context casting:
params := bindings | bindings :dialect pin;
pin := string(f1220 [0-9a-f]{64}), or the same typed symbol for in-process
compatibility. This does not recognize whole messages or authenticate wrappers. -/
set_option autoImplicit false
namespace CBCL.StateContextWrapperSyntax
open CheckpointEvidence StateInstalledContext StateContextCastSyntax

/-- The literal digest algorithm prefix accepted by native role parsing. -/
def pinPrefix : List Char := "f1220".toList

/-- Exact lowercase ASCII hex; Unicode digits and uppercase letters reject. -/
def hex (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9' ∨ 'a' ≤ c ∧ c ≤ 'f')

/-- Recognize the exact algorithm, digest length and alphabet. -/
def pinCheck (text : String) : Bool :=
  decide (text.toList.take 5 = pinPrefix) && decide ((text.toList.drop 5).length = 64) && (text.toList.drop 5).all hex

/-- Declarative grammar for the native digest spelling. -/
def Pin (text : String) : Prop := text.toList.take 5 = pinPrefix ∧
  (text.toList.drop 5).length = 64 ∧ ∀ c ∈ text.toList.drop 5, hex c = true

/-- The executable recognizer accepts exactly the specified digest grammar. -/
theorem pinCheck_iff (text : String) : pinCheck text = true ↔ Pin text := by
  simp [pinCheck,Pin,List.all_eq_true,and_assoc]

/-- Accepted digests have exactly the prefix and 64 ASCII-hex positions. -/
theorem pin_length (text : String) (valid : Pin text) : text.toList.length = 69 := by
  have prefixLength : (text.toList.take 5).length = 5 := by rw [valid.1]; decide
  have suffixLength := valid.2.1
  have total := congrArg List.length (List.take_append_drop 5 text.toList)
  simp only [List.length_append] at total
  omega

/-- Native pins accept strings and legacy typed symbols, never other atoms. -/
def pin : SExpr → Option String
  | .atom (.str text) | .atom (.symbol text) => if pinCheck text then some text else none
  | _ => none

/-- Pin success retains the original text without repair or normalization. -/
theorem pin_string_iff (text value : String) : pin (.atom (.str text)) = some value ↔ text = value ∧ Pin text := by
  by_cases checked : pinCheck text = true
  · have valid := (pinCheck_iff text).mp checked
    simp [pin,checked,valid]
  · have invalid : ¬Pin text := fun valid => checked ((pinCheck_iff text).mpr valid)
    simp [pin,checked,invalid]

/-- Existing typed-symbol callers have exactly the same checked pin semantics. -/
theorem pin_symbol (text : String) : pin (.atom (.symbol text)) = pin (.atom (.str text)) := rfl

/-- Decode the entire parameter list before semantic context use. -/
def decode : List SExpr → Option (List ResourceRoleBinding × Option String)
  | [raw] => do return (← bindings raw,none)
  | [raw,.atom (.keyword "dialect"),value] => do
      let digest ← pin value
      return (← bindings raw,some digest)
  | _ => none

/-- Convert decoded wrapper syntax to the existing fault-bearing metadata. -/
def metadata (thread : Option String) (params : List SExpr) : MessageMetadata :=
  match decode params with
  | none => ⟨thread,.malformed .malformedBinding,.absent⟩
  | some (rows,digest) => ⟨thread,.value rows,match digest with | none => .absent | some text => .value text⟩

/-- Complete context cast recognition: syntax, optional pin identity, role gate. -/
def recognize (definition : Definition) (params : List SExpr) : Option (List ResourceRoleBinding) := do
  let (rows,digest) ← decode params
  if digest.any (fun text => text != definition.address) then none else
    if bindingsCheck definition rows then some rows else none

/-- Raw wrapper recognition composes with the actual installed context cast
including malformed syntax, absent pins, wrong pins and semantic role errors. -/
theorem installed_cast (definition : Definition) (params : List SExpr) (address : Nat) (thread : Option String) :
    StateInstalledContext.cast ⟨definition,(fun _ => metadata thread params),(fun _ => "")⟩ address = recognize definition params := by
  cases parsed : decode params with
  | none => simp [StateInstalledContext.cast,metadata,parsed,recognize]
  | some result =>
    obtain ⟨rows,digest⟩ := result
    cases digest with
    | none => simp [StateInstalledContext.cast,metadata,parsed,recognize]
    | some text =>
      by_cases same : text = definition.address <;> simp [StateInstalledContext.cast,metadata,parsed,recognize,same]

/-- Without a pin the complete wrapper gate reduces to the existing raw cast gate. -/
theorem unpinned (definition : Definition) (raw : SExpr) :
    recognize definition [raw] = StateContextCastSyntax.recognize definition raw := by
  cases parsed : bindings raw <;> simp [recognize,decode,parsed,StateContextCastSyntax.recognize]

/-- A valid pin is retained in the decoded result; its identity is checked later. -/
theorem pinned_decode (rows : List ResourceRoleBinding) (text : String) (valid : pinCheck text = true) :
    decode [encode rows,.atom (.keyword "dialect"),.atom (.str text)] = some (rows,some text) := by
  simp [decode,pin,valid,bindings_roundtrip]

/-- A syntactically valid pin for another dialect is rejected before use. -/
theorem wrong_pin (definition : Definition) (rows : List ResourceRoleBinding) (text : String)
    (valid : pinCheck text = true) (different : text ≠ definition.address) :
    recognize definition [encode rows,.atom (.keyword "dialect"),.atom (.str text)] = none := by
  simp [recognize,pinned_decode rows text valid,different]

/-- A matching pin retains exactly the unpinned semantic role obligations. -/
theorem matching_pin (definition : Definition) (rows : List ResourceRoleBinding)
    (valid : pinCheck definition.address = true) :
    recognize definition [encode rows,.atom (.keyword "dialect"),.atom (.str definition.address)] =
      if bindingsCheck definition rows then some rows else none := by
  simp [recognize,pinned_decode rows definition.address valid]

/-- A quoted keyword cannot change the fixed wrapper parameter grammar. -/
theorem quoted_keyword_rejected (raw value : SExpr) : decode [raw,.atom (.str "dialect"),value] = none := rfl

/-- Extra parameters reject instead of being ignored. -/
theorem extra_parameter_rejected (raw value extra : SExpr) :
    decode [raw,.atom (.keyword "dialect"),value,extra] = none := rfl

end CBCL.StateContextWrapperSyntax
