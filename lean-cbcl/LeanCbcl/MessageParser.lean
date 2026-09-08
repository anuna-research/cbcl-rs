import LeanCbcl.SExpr
import LeanCbcl.Message
import LeanCbcl.Dialect
import LeanCbcl.Parser

/-!
# CBCL Message Parser

Validates parsed S-expressions against the CBCL message grammar.
Mirrors `validate-cbcl-message` and `parse-cbcl-message` from cbcl.scm.

```
message  ::= simple | meta-msg | dialect-msg | wrapped-msg
simple   ::= '(' performative recipient content param* ')'
meta-msg ::= '(' 'meta' '(' operation ... ')' ')'
dialect  ::= '(' 'lang' dialect-name message ')'
wrapped  ::= '(' wrapper-type content ')'
```
-/

namespace CBCL

/-- Convert a string to a Performative. -/
def toPerformative (s : String) : Performative :=
  if isCorePerformativeName s then
    match s with
    | "tell"   => .core .tell
    | "ask"    => .core .ask
    | "reply"  => .core .reply
    | "error"  => .core .error
    | "ok"     => .core .ok
    | "cancel" => .core .cancel
    | "hello"  => .core .hello
    | "bye"    => .core .bye
    | _        => .custom s  -- unreachable
  else .custom s

/-- Classify and parse a CBCL message from an S-expression.
    Mirrors `parse-cbcl-message` from cbcl.scm lines 288-330. -/
def parseMessageShape : SExpr → Option Message
  -- Simple message: (performative args...)
  | .list (.atom (.symbol perf) :: args) =>
    if perf == "meta" then
      some { type := .metaMsg
           , performative := .core .tell  -- meta messages don't have a performative per se
           , params := args }
    else if perf == "lang" then
      match args with
      | dialectName :: rest =>
        some { type := .dialect
             , performative := .custom "lang"
             , params := dialectName :: rest }
      | _ => none
    else if perf == "envelope" || perf == "signed" || perf == "with-limits" then
      some { type := .wrapped
           , performative := .custom perf
           , params := args }
    else
      some { type := .simple
           , performative := toPerformative perf
           , params := args }
  | _ => none

/-- Validate a CBCL message: check structural constraints.
    Mirrors `validate-cbcl-message` from cbcl.scm lines 198-282.

    Returns a list of validation errors (empty = valid). -/
def validateMessage (msg : Message) : List String :=
  let errors := []
  let errors := match msg.type with
    | .simple =>
      -- Simple messages: performative is already validated by parser.
      -- Zero-arg performatives (ok, hello, bye) are valid.
      -- Mirrors validate-simple-message: only checks recipient format if present.
      errors
    | .metaMsg =>
      -- Meta messages need an operation
      if msg.params.length < 1 then
        errors ++ ["meta message requires an operation"]
      else errors
    | .dialect =>
      -- Dialect messages need a dialect name and inner message
      if msg.params.length < 2 then
        errors ++ ["dialect message requires dialect name and inner message"]
      else errors
    | .wrapped => errors  -- wrappers have flexible content
  errors

/-- A message is valid if validation produces no errors. -/
def Message.isValid (msg : Message) : Bool :=
  (validateMessage msg).isEmpty

-- ============================================================
-- Message grammar specification
-- ============================================================

/-- The CBCL message grammar as a relation between S-expressions and Messages.
    An SExpr matches the grammar if parseMessageShape would produce the corresponding Message. -/
inductive ValidMessageShape : SExpr → Message → Prop where
  | simple : ∀ perf args,
      perf ≠ "meta" → perf ≠ "lang" →
      perf ≠ "envelope" → perf ≠ "signed" → perf ≠ "with-limits" →
      ValidMessageShape
        (.list (.atom (.symbol perf) :: args))
        { type := .simple, performative := toPerformative perf, params := args }
  | metaMsg : ∀ args,
      ValidMessageShape
        (.list (.atom (.symbol "meta") :: args))
        { type := .metaMsg, performative := .core .tell, params := args }
  | dialect : ∀ dialectName rest,
      ValidMessageShape
        (.list (.atom (.symbol "lang") :: dialectName :: rest))
        { type := .dialect, performative := .custom "lang", params := dialectName :: rest }
  | wrapped : ∀ perf args,
      (perf = "envelope" ∨ perf = "signed" ∨ perf = "with-limits") →
      ValidMessageShape
        (.list (.atom (.symbol perf) :: args))
        { type := .wrapped, performative := .custom perf, params := args }

-- ============================================================
-- Completeness: grammar-valid SExprs are always accepted
-- ============================================================

/-- Completeness: if an SExpr satisfies the grammar, parseMessageShape accepts it. -/
theorem parseMessageShape_complete (sexpr : SExpr) (msg : Message) :
    ValidMessageShape sexpr msg → parseMessageShape sexpr = some msg := by
  intro h
  cases h with
  | simple perf args hne_meta hne_lang hne_env hne_signed hne_wl =>
    simp only [parseMessageShape]
    have h1 : (perf == "meta") = false := by simp [hne_meta]
    have h2 : (perf == "lang") = false := by simp [hne_lang]
    have h3 : (perf == "envelope") = false := by simp [hne_env]
    have h4 : (perf == "signed") = false := by simp [hne_signed]
    have h5 : (perf == "with-limits") = false := by simp [hne_wl]
    simp [h1, h2, h3, h4, h5]
  | metaMsg args =>
    simp [parseMessageShape]
  | dialect dialectName rest =>
    simp [parseMessageShape]
  | wrapped perf args hwrap =>
    simp only [parseMessageShape]
    rcases hwrap with rfl | rfl | rfl <;> simp

-- ============================================================
-- Soundness: parseMessageShape output always satisfies the grammar
-- ============================================================

/-- Soundness: if parseMessageShape succeeds, the result satisfies the grammar. -/
theorem parseMessageShape_sound (sexpr : SExpr) (msg : Message) :
    parseMessageShape sexpr = some msg → ValidMessageShape sexpr msg := by
  intro h
  match sexpr with
  | .atom _ => simp [parseMessageShape] at h
  | .list [] => simp [parseMessageShape] at h
  | .list (.atom (.num _) :: _) => simp [parseMessageShape] at h
  | .list (.atom (.str _) :: _) => simp [parseMessageShape] at h
  | .list (.atom (.bool _) :: _) => simp [parseMessageShape] at h
  | .list (.atom (.keyword _) :: _) => simp [parseMessageShape] at h
  | .list (.list _ :: _) => simp [parseMessageShape] at h
  | .list (.atom (.symbol perf) :: args) =>
    simp only [parseMessageShape] at h
    by_cases hmeta : perf = "meta"
    · subst hmeta; simp at h; exact h ▸ .metaMsg args
    · by_cases hlang : perf = "lang"
      · subst hlang; simp at h
        match args with
        | [] => simp at h
        | dialectName :: rest => simp at h; exact h ▸ .dialect dialectName rest
      · by_cases henv : perf = "envelope"
        · subst henv; simp at h; exact h ▸ .wrapped "envelope" args (.inl rfl)
        · by_cases hsig : perf = "signed"
          · subst hsig; simp at h; exact h ▸ .wrapped "signed" args (.inr (.inl rfl))
          · by_cases hwl : perf = "with-limits"
            · subst hwl; simp at h; exact h ▸ .wrapped "with-limits" args (.inr (.inr rfl))
            · have h1 : (perf == "meta") = false := by simp [hmeta]
              have h2 : (perf == "lang") = false := by simp [hlang]
              have h3 : (perf == "envelope" || perf == "signed" || perf == "with-limits") = false := by
                simp [henv, hsig, hwl]
              simp [h1, h2, h3] at h
              exact h ▸ .simple perf args hmeta hlang henv hsig hwl

-- ============================================================
-- Correctness properties
-- ============================================================

/-- Core performative strings map to core performatives. -/
theorem toPerformative_core_is_core :
    ∀ s ∈ corePerformativeNames, (toPerformative s).isCore = true := by
  intro s hmem
  simp [corePerformativeNames] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [toPerformative, isCorePerformativeName, corePerformativeNames,
          List.contains, List.elem, Performative.isCore]

/-- Non-core strings map to custom performatives. -/
theorem toPerformative_custom_is_custom (s : String) (h : isCorePerformativeName s = false) :
    (toPerformative s).isCore = false := by
  simp [toPerformative, h, Performative.isCore]

/-- parseMessageShape returns none for non-list SExprs. -/
theorem parseMessageShape_atom_none (a : Atom) : parseMessageShape (.atom a) = none := by
  simp [parseMessageShape]

/-- parseMessageShape returns none for empty lists. -/
theorem parseMessageShape_empty_none : parseMessageShape (.list []) = none := by
  simp [parseMessageShape]

/-- Parsing a tell message produces a simple message. -/
theorem parse_tell_is_simple :
    parseMessageShape (.list [.atom (.symbol "tell"), .atom (.symbol "alice"), .atom (.symbol "hi")])
    = some { type := .simple
           , performative := .core .tell
           , params := [.atom (.symbol "alice"), .atom (.symbol "hi")]
           , thread := none
           , sender := none } := by
  simp [parseMessageShape, toPerformative, isCorePerformativeName, corePerformativeNames, List.contains, List.elem]

/-- Parsing a meta message produces a meta message type. -/
theorem parse_meta_is_meta :
    (parseMessageShape (.list [.atom (.symbol "meta"), .list [.atom (.symbol "define"), .atom (.symbol "my-dialect")]])).isSome = true := by
  native_decide

/-- parseMessageShape preserves the message type invariant: simple messages have simple type. -/
theorem parseMessageShape_simple_type (perf : String) (args : List SExpr) (msg : Message)
    (hne_meta : perf ≠ "meta") (hne_lang : perf ≠ "lang")
    (hne_env : perf ≠ "envelope") (hne_signed : perf ≠ "signed") (hne_wl : perf ≠ "with-limits")
    (h : parseMessageShape (.list (.atom (.symbol perf) :: args)) = some msg) :
    msg.type = .simple := by
  have hg := parseMessageShape_sound _ _ h
  cases hg with
  | simple _ _ _ _ _ _ _ => rfl
  | metaMsg _ => exact absurd rfl hne_meta
  | dialect _ _ => exact absurd rfl hne_lang
  | wrapped _ _ hwrap =>
    rcases hwrap with rfl | rfl | rfl
    · exact absurd rfl hne_env
    · exact absurd rfl hne_signed
    · exact absurd rfl hne_wl

/-- Check lang scope along the message path. Meta payloads are data, and
    ordinary wrappers preserve scope while lang establishes a new scope.
    Fuel bounds traversal; the caller supplies more than the tree's size. -/
def langScoped : Nat → Bool → SExpr → Bool
  | 0, _, _ => false
  | fuel + 1, inScope, .list (.atom (.symbol head) :: args) =>
    if head == "meta" then true
    else if head == "lang" then
      match args with
      | .atom (.symbol _) :: inner :: _ => langScoped fuel true inner
      | _ => false
    else if head == "envelope" || head == "signed" ||
            head == "with-limits" || head == "with-roles" then
      match args.reverse.find? (fun e => match e with | .list _ => true | _ => false) with
      | some inner => langScoped fuel inScope inner
      | none => false
    else inScope || isCorePerformativeName head
  | _, _, _ => false

/-- Public recognition requires both the structural grammar and lang scope. -/
def parseMessage (sexpr : SExpr) : Option Message :=
  if langScoped (sexpr.size + 1) false sexpr then parseMessageShape sexpr else none

/-- The accepted grammar includes the mandatory custom-performative scope. -/
def ValidMessageGrammar (sexpr : SExpr) (msg : Message) : Prop :=
  langScoped (sexpr.size + 1) false sexpr = true ∧ ValidMessageShape sexpr msg

theorem parseMessage_complete (sexpr : SExpr) (msg : Message) :
    ValidMessageGrammar sexpr msg → parseMessage sexpr = some msg := by
  rintro ⟨hs, hg⟩
  simp [parseMessage, hs, parseMessageShape_complete sexpr msg hg]

theorem parseMessage_sound (sexpr : SExpr) (msg : Message) :
    parseMessage sexpr = some msg → ValidMessageGrammar sexpr msg := by
  intro h
  unfold parseMessage at h
  split at h
  · rename_i hs
    exact ⟨hs, parseMessageShape_sound sexpr msg h⟩
  · simp at h

/-- Full pipeline: string → validated CBCL message. -/
def parseAndValidate (input : String) : Except String Message :=
  match parse input with
  | .error msg => .error s!"parse error: {msg}"
  | .ok sexpr =>
    match parseMessage sexpr with
    | none => .error "not a valid CBCL message structure"
    | some msg =>
      let errors := validateMessage msg
      if errors.isEmpty then .ok msg
      else .error s!"validation errors: {errors}"

end CBCL
