import LeanCbcl.StateJsonString

/-! Declarative state JSON and an operational append-buffer emitter. Containers
retain their stored order; sorting/deduplication belongs to their constructors.
The model covers every native Value variant, including non-string map keys.
Rust extraction, integer formatting and constructor ordering remain boundaries. -/
set_option autoImplicit false
namespace CBCL.StateJsonValue

/-- Native state value representation, independent of semantic field carriers. -/
inductive Value where
  | absent
  | str (text : String)
  | int (number : Int)
  | bool (flag : Bool)
  | list (items : List Value)
  | set (items : List Value)
  | map (entries : List (Value × Value))
  | event (signer : String) (value : Value)

mutual
/-- Declarative compact JSON spelling of one native value. -/
def render : Value → String
  | .absent => "null"
  | .str text => StateJsonString.quote text
  | .int number => toString number
  | .bool flag => if flag then "true" else "false"
  | .list items | .set items => "[" ++ sequence true items ++ "]"
  | .map entries => "{" ++ members true entries ++ "}"
  | .event signer value => "{\"by\":" ++ StateJsonString.quote signer ++ ",\"value\":" ++ render value ++ "}"
termination_by value => sizeOf value

/-- Item sequence with exactly the native comma placement. -/
def sequence (first : Bool) : List Value → String
  | [] => ""
  | value::rest => (if first then "" else ",") ++ render value ++ sequence false rest
termination_by items => sizeOf items

/-- String keys contribute their text; other keys contribute their rendered text. -/
def keyText : Value → String
  | .str text => text
  | value => render value
termination_by value => sizeOf value + 1

/-- Ordered map members, with escaped textual keys and compact values. -/
def members (first : Bool) : List (Value × Value) → String
  | [] => ""
  | (key,value)::rest => (if first then "" else ",") ++ StateJsonString.quote (keyText key) ++ ":" ++ render value ++ members false rest
termination_by entries => sizeOf entries
end

mutual
/-- Operational native append sequence with an explicit existing output buffer. -/
def emit : Value → String → String
  | .absent, buffer => buffer ++ "null"
  | .str text, buffer => StateJsonString.emit buffer text
  | .int number, buffer => buffer ++ toString number
  | .bool flag, buffer => buffer ++ if flag then "true" else "false"
  | .list items, buffer | .set items, buffer => emitSequence true items (buffer ++ "[") ++ "]"
  | .map entries, buffer => emitMembers true entries (buffer ++ "{") ++ "}"
  | .event signer value, buffer =>
      emit value (StateJsonString.emit (buffer ++ "{\"by\":") signer ++ ",\"value\":") ++ "}"
termination_by value => sizeOf value

/-- The native item loop inserts a comma before every item except the first. -/
def emitSequence (first : Bool) : List Value → String → String
  | [], buffer => buffer
  | value::rest, buffer => emitSequence false rest (emit value (if first then buffer else buffer ++ ","))
termination_by items => sizeOf items

/-- Native non-string key text is rendered into a fresh buffer. -/
def emitKey : Value → String
  | .str text => text
  | value => emit value ""
termination_by value => sizeOf value + 1

/-- The native map loop retains every stored key/value pair in original order. -/
def emitMembers (first : Bool) : List (Value × Value) → String → String
  | [], buffer => buffer
  | (key,value)::rest, buffer =>
      let named := StateJsonString.emit (if first then buffer else buffer ++ ",") (emitKey key)
      emitMembers false rest (emit value (named ++ ":"))
termination_by entries => sizeOf entries
end

mutual
/-- Every native value appends exactly its declarative JSON to any buffer. -/
theorem emit_refinement (value : Value) (buffer : String) : emit value buffer = buffer ++ render value := by
  cases value with
  | absent | str _ | int _ | bool _ => simp [emit,render,StateJsonString.emit_refinement]
  | list items | set items => simp [emit,render,sequence_refinement true items (buffer ++ "["),String.append_assoc]
  | map entries => simp [emit,render,members_refinement true entries (buffer ++ "{"),String.append_assoc]
  | event signer value => simp [emit,render,StateJsonString.emit_refinement,emit_refinement value,String.append_assoc]
termination_by sizeOf value

/-- The complete operational item loop preserves comma placement and item order. -/
theorem sequence_refinement (first : Bool) (items : List Value) (buffer : String) :
    emitSequence first items buffer = buffer ++ sequence first items := by
  cases items with
  | nil => simp [emitSequence,sequence]
  | cons value rest =>
    cases first <;> simp [emitSequence,sequence,emit_refinement value,sequence_refinement false rest,String.append_assoc]
termination_by sizeOf items

/-- Textual-key conversion is identical in operational and declarative emitters. -/
theorem key_refinement (value : Value) : emitKey value = keyText value := by
  cases value with
  | absent | str _ | int _ | bool _ => simp [emitKey,keyText,emit,render]
  | list items => simpa [emitKey,keyText] using emit_refinement (.list items) ""
  | set items => simpa [emitKey,keyText] using emit_refinement (.set items) ""
  | map entries => simpa [emitKey,keyText] using emit_refinement (.map entries) ""
  | event signer payload => simpa [emitKey,keyText] using emit_refinement (.event signer payload) ""
termination_by sizeOf value + 1

/-- Every map key is quoted once and followed by its own exact value; duplicate
or non-string keys are preserved here, rather than normalized by the renderer. -/
theorem members_refinement (first : Bool) (entries : List (Value × Value)) (buffer : String) :
    emitMembers first entries buffer = buffer ++ members first entries := by
  cases entries with
  | nil => simp [emitMembers,members]
  | cons entry rest =>
    obtain ⟨key,value⟩ := entry
    cases first <;> simp [emitMembers,members,StateJsonString.emit_refinement,key_refinement key,
      emit_refinement value,members_refinement false rest,String.append_assoc]
termination_by sizeOf entries
end

/-- Public native value rendering starts with an empty output buffer. -/
theorem empty_buffer (value : Value) : emit value "" = render value := by simp [emit_refinement]

/-- State field order is clause order, represented by string map keys. -/
def renderState (fields : List (String × Value)) : String :=
  render (.map (fields.map (fun (name,value) => (.str name,value))))

/-- Operational whole-state rendering uses the identical field-emission path. -/
def emitState (fields : List (String × Value)) (buffer : String) : String :=
  emit (.map (fields.map (fun (name,value) => (.str name,value)))) buffer

/-- Complete state emission preserves the caller's prefix and original clause order. -/
theorem state_refinement (fields : List (String × Value)) (buffer : String) :
    emitState fields buffer = buffer ++ renderState fields := emit_refinement _ _

end CBCL.StateJsonValue
