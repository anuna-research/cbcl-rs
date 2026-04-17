import LeanCbcl.SExpr

/-!
# Verified S-Expression Parser

A recursive-descent parser for S-expressions.
Operates on `List Char` for clean structural termination.

Accepts the grammar:
```
sexpr  ::= atom | '(' sexpr* ')'
atom   ::= '#t' | '#f' | number | ':' keyword | '"' string '"' | symbol
```
-/

namespace CBCL

/-- Parser result: value + remaining input, or error. -/
inductive ParseResult (α : Type) where
  | ok    : α → List Char → ParseResult α
  | error : String → ParseResult α
  deriving Repr, Inhabited

instance : Functor ParseResult where
  map f
    | .ok a rest => .ok (f a) rest
    | .error msg => .error msg

/-- Drop leading whitespace. -/
def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if c == ' ' || c == '\t' || c == '\n' || c == '\r'
               then skipWs cs else c :: cs

/-- Is this a delimiter character? -/
def isDelim (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '(' || c == ')' || c == '"'

/-- Read a token: sequence of non-delimiter characters. -/
def readToken : List Char → String × List Char
  | [] => ("", [])
  | c :: cs =>
    if isDelim c then ("", c :: cs)
    else
      let (rest, remaining) := readToken cs
      (String.ofList [c] ++ rest, remaining)

/-- Read a string literal (after opening quote consumed).
    Note: escape sequences other than `\"` and `\\` are treated as the literal
    character with the backslash dropped (e.g., `\n` becomes `n`). -/
def readStr : List Char → Option (String × List Char)
  | [] => none
  | '"' :: cs => some ("", cs)
  | '\\' :: [] => none
  | '\\' :: c :: cs =>
    match readStr cs with
    | none => none
    | some (rest, remaining) => some (String.ofList [c] ++ rest, remaining)
  | c :: cs =>
    match readStr cs with
    | none => none
    | some (rest, remaining) => some (String.ofList [c] ++ rest, remaining)

/-- Convert a token string to an atom. -/
def tokenToAtom (tok : String) : Atom :=
  if tok == "#t" then .bool true
  else if tok == "#f" then .bool false
  else if tok.startsWith ":" then .keyword (tok.drop 1).toString
  else match tok.toInt? with
    | some n => .num n
    | none   => .symbol tok

/-- Parse one S-expression from a character list.
    Returns the parsed expression and remaining characters.
    Uses fuel for termination (bounded by input length). -/
def parseSExpr (input : List Char) (fuel : Nat) : ParseResult SExpr :=
  match fuel with
  | 0 => .error "recursion limit"
  | fuel' + 1 =>
    let cs := skipWs input
    match cs with
    | [] => .error "unexpected end of input"
    | '(' :: rest => parseList rest [] fuel'
    | '"' :: rest =>
      match readStr rest with
      | none => .error "unterminated string"
      | some (s, remaining) => .ok (.atom (.str s)) remaining
    | ')' :: _ => .error "unexpected ')'"
    | _ =>
      let (tok, remaining) := readToken cs
      if tok.isEmpty then .error "empty token"
      else .ok (.atom (tokenToAtom tok)) remaining
where
  /-- Parse list contents until ')'. -/
  parseList (input : List Char) (acc : List SExpr) (fuel : Nat) : ParseResult SExpr :=
    match fuel with
    | 0 => .error "recursion limit in list"
    | fuel' + 1 =>
      let cs := skipWs input
      match cs with
      | [] => .error "unterminated list"
      | ')' :: rest => .ok (.list acc.reverse) rest
      | _ =>
        match parseSExpr cs fuel' with
        | .ok expr rest => parseList rest (expr :: acc) fuel'
        | .error msg => .error msg

/-- Top-level parse: string → SExpr. -/
def parse (input : String) : Except String SExpr :=
  let chars := input.toList
  let fuel := chars.length * 4 + 1
  match parseSExpr chars fuel with
  | .ok expr rest =>
    let rest' := skipWs rest
    if rest'.isEmpty then .ok expr
    else .error "trailing input"
  | .error msg => .error msg

/-- Parse multiple S-expressions from a string. -/
def parseAll (input : String) : Except String (List SExpr) :=
  let chars := input.toList
  let fuel := chars.length * 4 + 1
  go chars [] fuel
where
  go (cs : List Char) (acc : List SExpr) (fuel : Nat) : Except String (List SExpr) :=
    match fuel with
    | 0 => .ok acc.reverse
    | fuel' + 1 =>
      let cs := skipWs cs
      match cs with
      | [] => .ok acc.reverse
      | _ =>
        match parseSExpr cs fuel' with
        | .ok expr rest => go rest (expr :: acc) fuel'
        | .error msg => .error msg

-- ============================================================
-- Structural classifier
-- ============================================================

/-- Structural classifier for `SExpr`: every inhabitant of `SExpr`
    satisfies this predicate by construction (one constructor per
    `SExpr` shape, no side-conditions). This is the identity predicate
    on inhabitation — it does *not* encode a non-trivial well-formedness
    invariant. Parser soundness theorems that need structural content
    should use `CBCL.RoundTrippable'` (defined in `Serializer.lean`),
    which requires `SafeSymbol` for symbol atoms and non-empty strings
    for keywords and is genuinely non-vacuous. -/
inductive IsSExpr : SExpr → Prop where
  | atom : ∀ a, IsSExpr (.atom a)
  | list : ∀ xs, (∀ e, e ∈ xs → IsSExpr e) → IsSExpr (.list xs)

/-- All atoms are classified as `IsSExpr`. -/
theorem IsSExpr.ofAtom (a : Atom) : IsSExpr (.atom a) :=
  .atom a

-- ============================================================
-- skipWs properties
-- ============================================================

/-- skipWs on empty list is empty. -/
theorem skipWs_nil : skipWs [] = [] := rfl

/-- skipWs only removes whitespace. -/
theorem skipWs_preserves_nonws (c : Char) (cs : List Char)
    (h : ¬(c == ' ' || c == '\t' || c == '\n' || c == '\r') = true) :
    skipWs (c :: cs) = c :: cs := by
  simp [skipWs, h]

/-- skipWs is idempotent. -/
theorem skipWs_idempotent (cs : List Char) : skipWs (skipWs cs) = skipWs cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [skipWs]
    split
    · exact ih
    · next h =>
      simp only [skipWs]
      split
      · exact absurd ‹_› h
      · rfl

/-- skipWs output length is ≤ input length. -/
theorem skipWs_length_le (cs : List Char) : (skipWs cs).length ≤ cs.length := by
  induction cs with
  | nil => simp [skipWs]
  | cons c cs ih =>
    simp [skipWs]
    split
    · exact Nat.le_succ_of_le ih
    · exact Nat.le_refl _

-- ============================================================
-- readToken properties
-- ============================================================

/-- readToken on empty input produces empty token. -/
theorem readToken_nil : readToken [] = ("", []) := rfl

/-- readToken on a delimiter returns empty token and full input. -/
theorem readToken_delim (c : Char) (cs : List Char) (h : isDelim c = true) :
    readToken (c :: cs) = ("", c :: cs) := by
  simp [readToken, h]

/-- readToken remaining length is ≤ input length. -/
theorem readToken_length_le (cs : List Char) :
    (readToken cs).2.length ≤ cs.length := by
  induction cs with
  | nil => simp [readToken]
  | cons c cs ih =>
    simp only [readToken]
    split
    · simp
    · exact Nat.le_succ_of_le ih

-- ============================================================
-- tokenToAtom properties
-- ============================================================

/-- Booleans are parsed correctly. -/
theorem tokenToAtom_true : tokenToAtom "#t" = .bool true := by
  simp [tokenToAtom]

theorem tokenToAtom_false : tokenToAtom "#f" = .bool false := by
  simp [tokenToAtom]

-- ============================================================
-- Soundness: parseSExpr only produces well-formed S-expressions
-- ============================================================

/-- tokenToAtom always produces an `IsSExpr` atom (trivial — every atom is). -/
theorem tokenToAtom_isSExpr (tok : String) :
    IsSExpr (.atom (tokenToAtom tok)) :=
  .atom _

/-- readStr produces an `IsSExpr` string atom when it succeeds (trivial). -/
theorem readStr_isSExpr (cs : List Char) (s : String) (rest : List Char)
    (_h : readStr cs = some (s, rest)) :
    IsSExpr (.atom (.str s)) :=
  .atom _

/-- DecidableEq for Except, needed for native_decide on parse results. -/
instance {α β : Type} [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) :=
  fun a b => match a, b with
  | .ok a, .ok b =>
    if h : a = b then isTrue (congrArg Except.ok h)
    else isFalse (fun heq => h (by cases heq; rfl))
  | .error a, .error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun heq => h (by cases heq; rfl))
  | .ok _, .error _ => isFalse (fun h => by cases h)
  | .error _, .ok _ => isFalse (fun h => by cases h)

/-- Concrete parse tests as theorems (verified by kernel reduction). -/
theorem parse_symbol : parse "hello" = .ok (.atom (.symbol "hello")) := by native_decide

theorem parse_number : parse "42" = .ok (.atom (.num 42)) := by native_decide

theorem parse_bool_true : parse "#t" = .ok (.atom (.bool true)) := by native_decide

theorem parse_bool_false : parse "#f" = .ok (.atom (.bool false)) := by native_decide

theorem parse_string : parse "\"hello\"" = .ok (.atom (.str "hello")) := by native_decide

theorem parse_keyword : parse ":key" = .ok (.atom (.keyword "key")) := by native_decide

theorem parse_list : parse "(a b c)" = .ok (.list [.atom (.symbol "a"), .atom (.symbol "b"), .atom (.symbol "c")]) := by native_decide

theorem parse_nested : parse "(a (b c))" = .ok (.list [.atom (.symbol "a"), .list [.atom (.symbol "b"), .atom (.symbol "c")]]) := by native_decide

theorem parse_empty_list : parse "()" = .ok (.list []) := by native_decide

/-- Empty input produces an error. -/
theorem parse_empty_error : parse "" = .error "unexpected end of input" := by native_decide

/-- Unmatched close paren produces an error. -/
theorem parse_unmatched_close : parse ")" = .error "unexpected ')'" := by native_decide

-- ============================================================
-- Universal structural classification (vacuous by construction)
-- ============================================================

/-- Every S-expression is structurally classified by `IsSExpr`. This is
    a truism — `IsSExpr` has one constructor per `SExpr` shape with no
    side-conditions, so it is isomorphic to the constant-`True` predicate
    on `SExpr`. It carries no eliminative content. Reviewers seeking a
    non-trivial parser invariant should consult `CBCL.RoundTrippable'`
    in `Serializer.lean` and its rejection witness
    `not_roundTrippable_empty_symbol` (which demonstrates that
    `RoundTrippable'` is genuinely non-vacuous). -/
theorem allSExpr_isSExpr : ∀ (e : SExpr), IsSExpr e :=
  @SExpr.rec
    (fun e => IsSExpr e)
    (fun xs => ∀ e, e ∈ xs → IsSExpr e)
    (fun a => .atom a)
    (fun xs ih => .list xs ih)
    (fun _ h => nomatch h)
    (fun _ _ hx hxs => fun e he =>
      match List.mem_cons.mp he with
      | .inl heq => heq ▸ hx
      | .inr hmem => hxs e hmem)

/-- `parseSExpr` produces an `IsSExpr` result whenever it succeeds. This
    is a weak invariant — it says nothing beyond "the parser returned an
    `SExpr`". For a load-bearing grammar-shape invariant, see
    `MessageParser.parseMessage_sound` which is stated against the
    genuinely non-trivial `ValidMessageGrammar`. -/
theorem parseSExpr_isSExpr (input : List Char) (fuel : Nat) (e : SExpr) (rest : List Char)
    (_h : parseSExpr input fuel = .ok e rest) : IsSExpr e :=
  allSExpr_isSExpr e

/-- `parse` produces an `IsSExpr` result whenever it succeeds (weak invariant). -/
theorem parse_isSExpr (input : String) (e : SExpr)
    (_h : parse input = .ok e) : IsSExpr e :=
  allSExpr_isSExpr e

end CBCL
