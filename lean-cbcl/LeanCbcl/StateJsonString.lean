import Lean

/-! Canonical state JSON string emission and independent fragment decoding.
The native encoder uses short escapes where available, lowercase u00xx for
other C0 controls and raw Unicode scalar values otherwise. This module proves
lossless encoding; it does not identify the native Rust string implementation. -/
set_option autoImplicit false
namespace CBCL.StateJsonString

/-- Lowercase hexadecimal digit used by canonical control escapes. -/
def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48+n else 87+n)

/-- The six-character spelling of a C0 control without a short escape. -/
def control (n : Nat) : List Char := ['\\','u','0','0',digit (n/16),digit (n%16)]

/-- Canonical spelling of one source Unicode scalar value. -/
def escape (c : Char) : List Char :=
  if c = '"' then ['\\','"'] else
  if c = '\\' then ['\\','\\'] else
  if c = '\n' then ['\\','n'] else
  if c = '\r' then ['\\','r'] else
  if c = '\t' then ['\\','t'] else
  if c = Char.ofNat 8 then ['\\','b'] else
  if c = Char.ofNat 12 then ['\\','f'] else
  if c.toNat < 32 then control c.toNat else [c]

/-- Recognize exactly one lowercase ASCII hex digit. -/
def hex (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat-48) else
  if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat-87) else none

/-- Independent decoder for a single emitted fragment. Raw quote/backslash and
C0 characters reject; six-character escapes retain their exact scalar value. -/
def fragment : List Char → Option Char
  | ['\\','"'] => some '"'
  | ['\\','\\'] => some '\\'
  | ['\\','n'] => some '\n'
  | ['\\','r'] => some '\r'
  | ['\\','t'] => some '\t'
  | ['\\','b'] => some (Char.ofNat 8)
  | ['\\','f'] => some (Char.ofNat 12)
  | ['\\','u','0','0',high,low] => do
      let a ← hex high
      let b ← hex low
      let n := 16*a+b
      if n < 32 then some (Char.ofNat n) else none
  | [c] => if 32 ≤ c.toNat ∧ c ≠ '"' ∧ c ≠ '\\' then some c else none
  | _ => none

/-- Exhaustive kernel-checked digit arithmetic for all C0 controls. -/
theorem control_roundtrip : ∀ n : Fin 32, fragment (control n.val) = some (Char.ofNat n.val) := by decide

/-- Every source scalar is retained exactly by canonical fragment encoding. -/
theorem escape_roundtrip (c : Char) : fragment (escape c) = some c := by
  unfold escape
  split <;> rename_i quote
  · subst c; rfl
  · split <;> rename_i slash
    · subst c; rfl
    · split <;> rename_i newline
      · subst c; rfl
      · split <;> rename_i carriage
        · subst c; rfl
        · split <;> rename_i tab
          · subst c; rfl
          · split <;> rename_i backspace
            · subst c; rfl
            · split <;> rename_i formfeed
              · subst c; rfl
              · split <;> rename_i small
                · simpa using control_roundtrip ⟨c.toNat,small⟩
                · simp [fragment,quote,slash,show 32 ≤ c.toNat by omega]

/-- Different scalars cannot share one canonical emitted fragment. -/
theorem escape_injective : Function.Injective escape := by
  intro left right same
  have decoded := congrArg fragment same
  simpa only [escape_roundtrip,Option.some.injEq] using decoded

/-- Stream decoder consumes one complete escape at a time. -/
def decode : List Char → Option (List Char)
  | [] => some []
  | '\\'::'u'::'0'::'0'::high::low::rest => do
      let c ← fragment ['\\','u','0','0',high,low]
      return c::(← decode rest)
  | '\\'::code::rest => do
      let c ← fragment ['\\',code]
      return c::(← decode rest)
  | c::rest => do
      let raw ← fragment [c]
      return raw::(← decode rest)

/-- The emitted control prefix is decoded without consuming the next fragment. -/
theorem control_prefix (n : Fin 32) (rest : List Char) :
    decode (control n.val ++ rest) = (decode rest).map (Char.ofNat n.val :: ·) := by
  change (do let c ← fragment (control n.val); return c::(← decode rest)) = _
  rw [control_roundtrip]
  cases decode rest <;> rfl

/-- Scalar encoding is prefix-decodable in any stream, including adjacent
backslashes and control escapes. No unproved delimiter assumption is needed. -/
theorem escape_prefix (c : Char) (rest : List Char) :
    decode (escape c ++ rest) = (decode rest).map (c :: ·) := by
  unfold escape
  split <;> rename_i quote
  · subst c; simp [decode,fragment,Option.map_eq_bind,Function.comp_def]
  · split <;> rename_i slash
    · subst c; simp [decode,fragment,Option.map_eq_bind,Function.comp_def]
    · split <;> rename_i newline
      · subst c; simp [decode,fragment,Option.map_eq_bind,Function.comp_def]
      · split <;> rename_i carriage
        · subst c; simp [decode,fragment,Option.map_eq_bind,Function.comp_def]
        · split <;> rename_i tab
          · subst c; simp [decode,fragment,Option.map_eq_bind,Function.comp_def]
          · split <;> rename_i backspace
            · subst c; simp [decode,fragment,Option.map_eq_bind,Function.comp_def]
            · split <;> rename_i formfeed
              · subst c; simp [decode,fragment,Option.map_eq_bind,Function.comp_def]
              · split <;> rename_i small
                · simpa using control_prefix ⟨c.toNat,small⟩ rest
                · have raw : fragment [c] = some c := by simp [fragment,quote,slash,show 32 ≤ c.toNat by omega]
                  simp only [List.singleton_append]
                  simp [decode,slash,raw,Option.map_eq_bind,Function.comp_def]

/-- Canonical escaped contents without opening/closing quotes. -/
def contents (chars : List Char) : List Char := chars.flatMap escape

/-- Complete string contents are decoded without losing Unicode or controls. -/
theorem contents_roundtrip (chars : List Char) : decode (contents chars) = some chars := by
  induction chars with
  | nil => rfl
  | cons c rest ih =>
    change decode (escape c ++ contents rest) = some (c::rest)
    rw [escape_prefix,ih]
    rfl

/-- The native canonical quoted string spelling. -/
def quote (text : String) : String := String.ofList ('"'::(contents text.toList ++ ['"']))

/-- Decode a complete quoted canonical string, preserving its scalar sequence. -/
def unquote (text : String) : Option String := do
  let '"'::rest := text.toList | none
  let '"'::body := rest.reverse | none
  (decode body.reverse).map String.ofList

/-- Complete quoting is lossless, including empty strings and every Unicode scalar. -/
theorem quote_roundtrip (text : String) : unquote (quote text) = some text := by
  simp [quote,unquote,contents_roundtrip]

/-- Canonical quoted strings cannot conflate different source text. -/
theorem quote_injective : Function.Injective quote := by
  intro left right same
  have decoded := congrArg unquote same
  simpa only [quote_roundtrip,Option.some.injEq] using decoded

/-- Mutable-emitter character loop expressed with explicit accumulator state. -/
def appendContents (buffer chars : List Char) : List Char :=
  chars.foldl (fun output c => output ++ escape c) buffer

/-- Appending escaped contents preserves the exact pre-existing output buffer. -/
theorem append_contents (buffer chars : List Char) : appendContents buffer chars = buffer ++ contents chars := by
  induction chars generalizing buffer with
  | nil => simp [appendContents,contents]
  | cons c rest ih =>
    simpa [appendContents,contents,List.append_assoc] using ih (buffer ++ escape c)

/-- Native quote-open, character loop, quote-close sequence over a buffer. -/
def emit (buffer text : String) : String :=
  String.ofList (appendContents (buffer.toList ++ ['"']) text.toList ++ ['"'])

/-- String emission into any existing buffer equals canonical quote append. -/
theorem emit_refinement (buffer text : String) : emit buffer text = buffer ++ quote text := by
  simp [emit,append_contents,quote,List.append_assoc,String.ofList_append]

end CBCL.StateJsonString
