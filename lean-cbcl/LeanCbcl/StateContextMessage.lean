import LeanCbcl.StateContextWrapperSyntax

/-! Context extraction from the native message categories. This is a typed
projection of Message, not a replacement for the full wire/message recognizer.
Outer sealed casts stop nomination search, while thread lookup independently
reaches the underlying simple message. Authentication is not performed here. -/
set_option autoImplicit false
namespace CBCL.StateContextMessage
open CheckpointEvidence StateInstalledContext

/-- The four wrapper categories recognized by native Message. -/
inductive Wrapper where
  | envelope | signed | withLimits | withRoles
  deriving DecidableEq

/-- Native message categories retaining only context-relevant data. Other simple
fields, dialect names and meta payloads cannot affect cast/thread traversal. -/
inductive Message where
  | simple (thread : Option String)
  | metaMsg
  | dialect (name : String) (inner : Message)
  | wrapped (kind : Wrapper) (params : List SExpr) (inner : Message)

/-- Innermost simple thread lookup, independent of cast nomination precedence. -/
def thread : Message → Option String
  | .simple value => value
  | .metaMsg => none
  | .dialect _ inner | .wrapped _ _ inner => thread inner

/-- Find the outermost sealed nomination. An invalid nomination must remain
present so it cannot be skipped in favor of a valid inner cast. -/
def nomination : Message → Option (List SExpr)
  | .wrapped .withRoles params _ => some params
  | .wrapped _ _ inner | .dialect _ inner => nomination inner
  | .simple _ | .metaMsg => none

/-- Extract fault-bearing metadata with no supplied cast/pin decoder callback. -/
def metadata (message : Message) : MessageMetadata :=
  match nomination message with
  | none => ⟨thread message,.absent,.absent⟩
  | some params => StateContextWrapperSyntax.metadata (thread message) params

/-- Independently describe native Definition::cast's category traversal. -/
def nativeCast (definition : Definition) : Message → Option (List ResourceRoleBinding)
  | .wrapped .withRoles params _ => StateContextWrapperSyntax.recognize definition params
  | .wrapped _ _ inner | .dialect _ inner => nativeCast definition inner
  | .simple _ | .metaMsg => if definition.roles.isEmpty then some [] else none

/-- Sealed nomination selection is independent of the discarded inner cast. -/
theorem outermost (params : List SExpr) (inner : Message) :
    nomination (.wrapped .withRoles params inner) = some params := rfl

/-- Thread extraction continues below the outermost sealed nomination. -/
theorem sealed_thread (params : List SExpr) (inner : Message) :
    thread (.wrapped .withRoles params inner) = thread inner := rfl

/-- Cast/thread metadata extraction composes with installed casting for every
message category and nesting, including malformed outer casts and absent casts. -/
theorem cast_refinement (definition : Definition) (message : Message) (address : Nat) :
    StateInstalledContext.cast ⟨definition,(fun _ => metadata message),(fun _ => "")⟩ address =
      nativeCast definition message := by
  induction message with
  | simple value | metaMsg => simp [metadata,nomination,StateInstalledContext.cast,nativeCast]
  | dialect name inner ih =>
    simpa [metadata,nomination,thread,nativeCast] using ih
  | wrapped kind params inner ih =>
    cases kind with
    | withRoles => exact StateContextWrapperSyntax.installed_cast definition params address (thread inner)
    | envelope | signed | withLimits => simpa [metadata,nomination,thread,nativeCast] using ih

/-- Metadata always retains the actual underlying thread, even when nomination
syntax or semantic role validation fails. -/
theorem metadata_thread (message : Message) : (metadata message).thread = thread message := by
  cases selected : nomination message with
  | none => simp [metadata,selected]
  | some params =>
    cases parsed : StateContextWrapperSyntax.decode params with
    | none => simp [metadata,selected,StateContextWrapperSyntax.metadata,parsed]
    | some result =>
      obtain ⟨rows,digest⟩ := result
      simp [metadata,selected,StateContextWrapperSyntax.metadata,parsed]

/-- Construct the installed profile directly from immutable native message
projections; only actual messages and their address representations are inputs. -/
def profile (definition : Definition) (messages : Nat → Message) (address : Nat → String) : Profile :=
  ⟨definition,(fun id => metadata (messages id)),address⟩

/-- The profile's cast result is the independently traversed native cast. -/
theorem profile_cast (definition : Definition) (messages : Nat → Message) (address : Nat → String) (id : Nat) :
    StateInstalledContext.cast (profile definition messages address) id = nativeCast definition (messages id) :=
  cast_refinement definition (messages id) id

/-- Root decoding now derives cast validity from the actual message projection. -/
theorem root_decoder (definition : Definition) (messages : Nat → Message) (address : Nat → String) (act : State.Act) :
    rootDecoder (profile definition messages address) act =
      (nativeCast definition (messages act.addr)).map (fun _ => State.Val.list [.int (Int.ofNat act.addr),.str act.signer]) := by
  simp only [rootDecoder,profile_cast]

end CBCL.StateContextMessage
