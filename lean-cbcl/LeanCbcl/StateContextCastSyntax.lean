import LeanCbcl.StateInstalledContext
import LeanCbcl.SExpr

/-! Context cast raw before semantic role validation. The accepted grammar is
bindings := (binding*), binding := (symbol symbol*). Cardinality, completeness,
unknown roles and duplicates are checked by the installed context gate. Quoted
strings and keywords never become role/account symbols. -/
set_option autoImplicit false
namespace CBCL.StateContextCastSyntax
open CheckpointEvidence StateInstalledContext

/-- Recognize a native role/account symbol without coercing other atom kinds. -/
def symbol : SExpr → Option String
  | .atom (.symbol name) => some name
  | _ => none

/-- Recognize one raw cast row, retaining empty/duplicate keys for validation. -/
def binding : SExpr → Option ResourceRoleBinding
  | .list (.atom (.symbol role)::keys) => do return ⟨role,← keys.mapM symbol⟩
  | _ => none

/-- Recognize the whole cast before any cardinality or membership action. -/
def bindings : SExpr → Option (List ResourceRoleBinding)
  | .list rows => rows.mapM binding
  | _ => none

/-- Preserve malformed raw as a fault-bearing field, never absence. -/
def field (raw : SExpr) : ResourceField (List ResourceRoleBinding) :=
  match bindings raw with
  | some rows => .value rows
  | none => .malformed .malformedBinding

/-- The complete cast recognizer composes grammar recognition and role checks. -/
def recognize (definition : Definition) (raw : SExpr) : Option (List ResourceRoleBinding) := do
  let rows ← bindings raw
  if bindingsCheck definition rows then some rows else none

/-- Reconstruct a native cast row with exactly its original symbol identities. -/
def encodeBinding (row : ResourceRoleBinding) : SExpr :=
  .list (.atom (.symbol row.role)::row.accounts.map (fun account => .atom (.symbol account)))

/-- Reconstruct a raw binding list without silently sorting/deduplicating it. -/
def encode (rows : List ResourceRoleBinding) : SExpr := .list (rows.map encodeBinding)

/-- Symbol key recognition preserves order, cardinality and duplicates. -/
theorem symbols_roundtrip (keys : List String) :
    (keys.map (fun key => SExpr.atom (.symbol key))).mapM symbol = some keys := by
  induction keys with
  | nil => rfl
  | cons key rest ih => simp [symbol,ih]

/-- Grammar recognition does not pre-validate or normalize a binding. -/
theorem binding_roundtrip (row : ResourceRoleBinding) : binding (encodeBinding row) = some row := by
  cases row
  simp only [encodeBinding,binding,symbols_roundtrip]
  rfl

/-- Whole-cast recognition retains the exact supplied typed rows. -/
theorem bindings_roundtrip (rows : List ResourceRoleBinding) : bindings (encode rows) = some rows := by
  have sequence : ∀ rows : List ResourceRoleBinding, (rows.map encodeBinding).mapM binding = some rows := by
    intro rows
    induction rows with
    | nil => rfl
    | cons row rest ih => simp [binding_roundtrip,ih]
  exact sequence rows

/-- The new raw raw path preserves every existing typed semantic gate. -/
theorem recognize_encoded (definition : Definition) (rows : List ResourceRoleBinding) :
    recognize definition (encode rows) = if bindingsCheck definition rows then some rows else none := by
  simp [recognize,bindings_roundtrip]

/-- Successful recognition constructs both the raw and semantic evidence. -/
theorem recognize_iff (definition : Definition) (raw : SExpr) (rows : List ResourceRoleBinding) :
    recognize definition raw = some rows ↔ bindings raw = some rows ∧ bindingsCheck definition rows = true := by
  cases parsed : bindings raw with
  | none => simp [recognize,parsed]
  | some found =>
    cases checked : bindingsCheck definition found <;> simp [recognize,parsed,checked] <;>
      rintro rfl <;> exact checked

/-- The source-owned context decoder consumes raw cast raw directly. With
no pin, raw plus semantic recognition is exactly the installed cast result. -/
theorem installed_cast (definition : Definition) (raw : SExpr) (address : Nat) (thread : Option String) :
    cast ⟨definition,(fun _ => ⟨thread,field raw,.absent⟩),(fun _ => "")⟩ address = recognize definition raw := by
  cases parsed : bindings raw with
  | none => simp [StateInstalledContext.cast,field,parsed,recognize]
  | some rows => simp [StateInstalledContext.cast,field,parsed,recognize]

/-- A quoted role cannot masquerade as the same-spelling role symbol. -/
theorem quoted_role_rejected (role : String) (keys : List SExpr) :
    binding (.list (.atom (.str role)::keys)) = none := rfl

/-- A quoted key cannot masquerade as an authenticated account symbol. -/
theorem quoted_key_rejected (role key : String) :
    binding (.list [.atom (.symbol role),.atom (.str key)]) = none := rfl

end CBCL.StateContextCastSyntax
