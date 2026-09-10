import LeanCbcl.LexicalComposition
import LeanCbcl.InstalledDCFL

/-! The scalar lexer of SPEC-018 CON-1803. All retained data have finite
representations. In particular, arbitrary atom/string/comment text is never
stored: exact names use a bounded cursor and a finite candidate vector. -/
namespace CBCL.InstalledSyntax.Raw
open FormalLanguage

abbrev ScalarCode := Fin 0x10f800

/-- Dense numbering of Unicode scalars skips the surrogate interval. -/
def codepoint (c : ScalarCode) : Nat := if c.val < 0xd800 then c.val else c.val + 0x800

def encodeChar (c : Char) : ScalarCode :=
  ⟨if c.toNat < 0xd800 then c.toNat else c.toNat - 0x800, by
    have h := c.valid
    change c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) at h
    split <;> omega⟩

theorem codepoint_encodeChar (c : Char) : codepoint (encodeChar c) = c.toNat := by
  have h := c.valid
  change c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) at h
  simp only [codepoint, encodeChar]
  split <;> (try split) <;> omega

def scalar (c : Nat) : Bool := c < 0xd800 || (0xe000 ≤ c && c < 0x110000)
def whitespace (c : Nat) : Bool := [32, 9, 10, 12, 13].contains c
def digit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def symbolChar (c : Nat) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || digit c ||
    [95, 45, 46, 47, 33, 63, 43, 42, 60, 62, 61, 64].contains c

def names (ds : List Dialect) : List String := symbolTable ds ++ ["thread", "sender", "caused-by"]
def width (ds : List Dialect) : Nat := ((names ds).map (fun s => s.toList.length)).foldl max 0

/-- Modes: idle, comment, string, escape, symbol, keyword, initial minus,
    number, initial hash, completed boolean. -/
structure State (ds : List Dialect) where
  mode : Fin 10
  position : Fin (width ds + 2)
  candidates : Fin (names ds).length → Bool
  address : Bool
  nonempty : Bool
  negative : Bool
  magnitude : Fin (2^63+1)

def State.codec (ds : List Dialect) : FiniteCodec (State ds) :=
  ((FiniteCodec.fin 9).product ((FiniteCodec.fin (width ds+1)).product
    ((FiniteCodec.functions FiniteCodec.bool (names ds).length).product
    (FiniteCodec.bool.product (FiniteCodec.bool.product
    (FiniteCodec.bool.product (FiniteCodec.fin (2^63)))))))).retract
    (fun s => (s.mode, s.position, s.candidates, s.address, s.nonempty, s.negative, s.magnitude))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
      p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (by intro s; cases s; rfl)

def initial (ds : List Dialect) : State ds :=
  ⟨0, 0, fun _ => true, false, false, false, 0⟩

/-- A saturating position and candidate elimination recognize exact finite
    names even when the input token is arbitrarily long. -/
def wordChar {ds : List Dialect} (s : State ds) (c : Nat) : State ds :=
  { s with
    position := ⟨min (s.position.val+1) (width ds+1), by omega⟩
    candidates := fun i => s.candidates i &&
      ((((names ds)[i].toList.map Char.toNat)[s.position.val]?).any (fun x => x == c))
    address := if s.nonempty then s.address else c == 64
    nonempty := true }

def nameMatches {ds : List Dialect} (s : State ds) (i : Fin (names ds).length) : Bool :=
  s.candidates i && (names ds)[i].toList.length == s.position.val

abbrev AtomCode (ds : List Dialect) := Fin ((symbolTable ds).length+7)

def symbolCode {ds : List Dialect} (s : State ds) : AtomCode ds :=
  match (List.finRange (symbolTable ds).length).find? (fun i =>
      nameMatches s ⟨i.val, by simp only [names, List.length_append, List.length_cons, List.length_nil]; omega⟩) with
  | some i => ⟨i.val+7, by omega⟩
  | none => if s.address && 2 ≤ s.position.val then 6 else 5

def keywordCode {ds : List Dialect} (s : State ds) : AtomCode ds :=
  let has (name : String) := (List.finRange (names ds).length).any
    (fun i => nameMatches s i && (names ds)[i] == name)
  if has "thread" || has "sender" then 3 else if has "caused-by" then 4 else 2

/-- Starting a token never emits an atom, only an optional parenthesis. -/
def start (ds : List Dialect) (c : Nat) : Option (State ds × Fin 3) :=
  let s := initial ds
  if whitespace c then some (s, 0)
  else if c == 59 then some ({s with mode := 1}, 0)
  else if c == 40 then some (s, 1)
  else if c == 41 then some (s, 2)
  else if c == 34 then some ({s with mode := 2}, 0)
  else if c == 35 then some ({s with mode := 8}, 0)
  else if c == 58 then some ({s with mode := 5}, 0)
  else if hd : digit c then some ({s with mode := 7, magnitude := ⟨c-48, by simp only [digit, Bool.and_eq_true, decide_eq_true_eq] at *; omega⟩}, 0)
  else if c == 45 then some ({wordChar s c with mode := 6}, 0)
  else if symbolChar c then some ({wordChar s c with mode := 4}, 0)
  else none

def flush {ds : List Dialect} (a : AtomCode ds) (c : Nat) :
    Option (State ds × Lexeme ((symbolTable ds).length+7)) :=
  (start ds c).map (fun (s, d) => (s, some a, d))

def numberChar {ds : List Dialect} (s : State ds) (c : Nat) : Option (State ds) :=
  let m := s.magnitude.val*10+(c-48)
  if h : m ≤ 2^63 ∧ (s.negative = true ∨ m < 2^63) then
    some {s with magnitude := ⟨m, by omega⟩}
  else none

def step (ds : List Dialect) (s : State ds) (input : ScalarCode) :
    Option (State ds × Lexeme ((symbolTable ds).length+7)) :=
  let c := codepoint input
  let keep (t : State ds) := some (t, none, 0)
  if !scalar c then none else
  match s.mode.val with
  | 0 => (start ds c).map (fun (t, d) => (t, none, d))
  | 1 => keep (if c == 10 then initial ds else s)
  | 2 => if c == 34 then some (initial ds, some 1, 0)
      else if c == 92 then keep {s with mode := 3} else keep s
  | 3 => if [34, 92, 110, 114, 116].contains c then keep {s with mode := 2} else none
  | 4 => if symbolChar c then keep (wordChar s c) else flush (symbolCode s) c
  | 5 => if symbolChar c then keep (wordChar s c)
      else if s.nonempty then flush (keywordCode s) c else none
  | 6 => if digit c then (numberChar {s with mode := 7, negative := true} c).map
        (fun t => (t, none, 0))
      else if symbolChar c then keep {wordChar s c with mode := 4}
      else flush (symbolCode s) c
  | 7 => if digit c then (numberChar s c).map (fun t => (t, none, 0))
      else if c == 45 then none else flush 0 c
  | 8 => if c == 116 || c == 102 then keep {s with mode := 9} else none
  | 9 => if whitespace c || [40, 41, 34, 59].contains c then flush 0 c else none
  | _ => none

def finish (ds : List Dialect) (s : State ds) : Option (Option (AtomCode ds)) :=
  match s.mode.val with
  | 0 | 1 => some none
  | 4 | 6 => some (some (symbolCode s))
  | 5 => if s.nonempty then some (some (keywordCode s)) else none
  | 7 | 9 => some (some 0)
  | _ => none

def lexer (ds : List Dialect) : FiniteLexer 0x10f800 ((symbolTable ds).length+7) (State ds) :=
  ⟨initial ds, step ds, finish ds⟩

/-- Every letter in the finite input alphabet is a Unicode scalar. -/
theorem codepoint_scalar (c : ScalarCode) : scalar (codepoint c) = true := by
  have h := c.isLt
  simp only [codepoint, scalar]
  split <;> simp_all <;> omega

/-- Exact scalar encoding of Lean strings, with no modular truncation. -/
def encode (s : String) : List ScalarCode := s.toList.map encodeChar

theorem encode_codepoints (s : String) : (encode s).map codepoint = s.toList.map Char.toNat := by
  simp [encode, List.map_map, Function.comp_def, codepoint_encodeChar]

def algebra (ds : List Dialect) :=
  (environmentGrammar ds).compile (alphabet ds) (Accumulator.codec ds.length)

def language (ds : List Dialect) (w : List ScalarCode) : Prop :=
  ∃ tokens, (lexer ds).lex w = some tokens ∧ tokenLanguage ds tokens

/-- A concrete finite, real-time character DPDA; equality holds on ALL input
    words, not just serializer output or balanced token streams. -/
def environmentDCFL (ds : List Dialect) : IsRealtimeDCFL (language ds) where
  stateSize := ((lexer ds).isRealtimeDCFL (State.codec ds) (algebra ds)).stateSize
  stackSize := ((lexer ds).isRealtimeDCFL (State.codec ds) (algebra ds)).stackSize
  machine := ((lexer ds).isRealtimeDCFL (State.codec ds) (algebra ds)).machine
  correct w := by
    rw [((lexer ds).isRealtimeDCFL (State.codec ds) (algebra ds)).correct]
    simp only [FiniteLexer.language, language, algebra, SummaryGrammar.language_eq,
      tokenLanguage]

/-- Observable equality with lexing followed by the classified-token recogniser. -/
theorem accepts_lex (ds : List Dialect) (w : List ScalarCode) :
    (environmentDCFL ds).machine.accepts w =
      ((lexer ds).lex w).any (InstalledSyntax.environmentDCFL ds).machine.accepts :=
  (lexer ds).product_accepts (State.codec ds) (algebra ds) w

theorem recognizes_expression (ds : List Dialect) (w : List ScalarCode) (e : SExpr)
    (h : (lexer ds).lex w = some (SyntaxTree.encode (classifyTree ds e))) :
    (environmentDCFL ds).machine.accepts w = true ↔ admitted ds e := by
  rw [accepts_lex, h]
  exact InstalledSyntax.recognizes_expression ds e

/-- Convenient executable reference check, retaining syntax trees rather than
    the enormous encoded finite-control numbers. The equality below is proved. -/
def tokenCheck (ds : List Dialect) (tokens : List (Fin ((symbolTable ds).length+7+2))) : Bool :=
  match ForestDecoder.run (some ([], [])) tokens with
  | some (xs, []) => (environmentGrammar ds).accept
      ((environmentGrammar ds).forest (alphabet ds) xs (environmentGrammar ds).empty)
  | _ => false

theorem tokenCheck_correct (ds : List Dialect) (tokens : List (Fin ((symbolTable ds).length+7+2))) :
    tokenCheck ds tokens = (InstalledSyntax.environmentDCFL ds).machine.accepts tokens := by
  have h := (algebra ds).abstract_run (some ([], [])) tokens
  change (algebra ds).abstractOption (ForestDecoder.run (some ([], [])) tokens) =
    (algebra ds).machine.runFrom (some (algebra ds).machine.initial) tokens at h
  change _ = (algebra ds).machine.accepts tokens
  unfold DPDA.accepts
  rw [← h]
  cases hd : ForestDecoder.run (some ([], [])) tokens with
  | none => simp [tokenCheck, hd, ForestAlgebra.abstractOption]
  | some out =>
    rcases out with ⟨xs, parents⟩
    cases parents with
    | nil =>
      simp [tokenCheck, hd, ForestAlgebra.abstractOption, ForestAlgebra.abstract,
        ForestAlgebra.control, ForestAlgebra.machine, algebra,
        SummaryGrammar.compile]
      change _ = (environmentGrammar ds).accept ((Accumulator.codec ds.length).decode
        (((environmentGrammar ds).compile (alphabet ds) (Accumulator.codec ds.length)).foldForest
          xs ((Accumulator.codec ds.length).encode (environmentGrammar ds).empty)))
      rw [SummaryGrammar.compile_forest, FiniteCodec.decode_encode]
    | cons p ps =>
      simp [tokenCheck, hd, ForestAlgebra.abstractOption, ForestAlgebra.abstract,
        ForestAlgebra.control, ForestAlgebra.machine]
      rw [← Fin.natAdd_eq_addNat, Fin.addCases_right]

def check (ds : List Dialect) (source : String) : Bool :=
  ((lexer ds).lex (encode source)).any (tokenCheck ds)

theorem check_correct (ds : List Dialect) (source : String) :
    check ds source = (environmentDCFL ds).machine.accepts (encode source) := by
  rw [accepts_lex]
  unfold check
  cases (lexer ds).lex (encode source) <;> simp [tokenCheck_correct]

def base_dcfl (id : String) : IsRealtimeDCFL (language (Agent.new id).dialects) :=
  environmentDCFL (Agent.new id).dialects

def dcfl_preserved (a : Agent) (d : Dialect) :
    IsRealtimeDCFL (language (a.installDialect d).dialects) :=
  environmentDCFL (a.installDialect d).dialects

def dcfl_preserved_many (a : Agent) (ds : List Dialect) :
    IsRealtimeDCFL (language (installMany a ds).dialects) :=
  environmentDCFL (installMany a ds).dialects

def accepted_installations_dcfl {accept : Agent → Dialect → Prop}
    {a b : Agent} {ds : List Dialect} (_h : AcceptedInstalls accept a ds b) :
    IsRealtimeDCFL (language b.dialects) := environmentDCFL b.dialects

def verified_fresh_installations_dcfl {a b : Agent} {ds : List Dialect}
    (h : VerifiedFreshInstalls a ds b) : IsRealtimeDCFL (language b.dialects) :=
  accepted_installations_dcfl h

end CBCL.InstalledSyntax.Raw
