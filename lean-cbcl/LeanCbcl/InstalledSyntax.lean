import LeanCbcl.FiniteSummary
import LeanCbcl.Agent

/-!
# Recursive installed-message syntax

SPEC-018 CON-1801. This grammar evaluator is independent of DPDA execution.
A completed subtree carries its admission verdict in each finite scope. The
list grammar reads its head, optional recipient, keyword/value pairs, and
recursive message positions. Payload trees have no message-admission obligation.

Scope 0 is unscoped; scope i+1 denotes dialect i. Tags: 0 non-symbol,
1 simple, 2 meta, 3 lang, 4 wrapper. Keyword classes: 0 positional,
1 arbitrary value, 2 symbol/string value, 3 causal value.
-/
namespace CBCL.InstalledSyntax
open FormalLanguage
/-- One Boolean verdict for each scope, including the unscoped position. -/
abbrev Scopes (n : Nat) := Fin (n+1) → Bool

/-- Finite atom predicates needed by the recursive installed-message grammar. -/
structure AtomClass (n : Nat) where
  /-- Dispatch category: non-symbol, simple, meta, lang, or wrapper. -/
  tag : Fin 5
  /-- Scopes in which this symbol is an admitted simple performative. -/
  permits : Scopes n
  /-- Installed dialect named by this symbol, or zero if absent. -/
  dialectScope : Fin (n+1)
  /-- Whether this atom is an address with a nonempty symbol suffix. -/
  address : Bool
  /-- Whether this atom is a symbol or string. -/
  symStr : Bool
  /-- Keyword category: positional, arbitrary, symbol/string, or causal value. -/
  keyword : Fin 4

/-- Finite summary accumulated while reading sibling expressions. -/
structure Accumulator (n : Nat) where
  /-- Sibling count saturated at three. -/
  count : Fin 4
  /-- Atom classification of the first sibling, or a non-atom sentinel. -/
  head : AtomClass n
  /-- Scope selected by the second sibling of a lang form. -/
  langScope : Fin (n+1)
  /-- Whether the third sibling is an admitted message in the selected lang scope. -/
  langOK : Bool
  /-- Admission verdicts of the most recent list-valued sibling. -/
  lastList : Scopes n
  /-- Whether the next simple-tail expression can be an optional recipient. -/
  firstArg : Bool
  /-- Pending keyword-value requirement, with four denoting rejection. -/
  pending : Fin 5
  /-- Whether every sibling is an address atom. -/
  allAddresses : Bool
  /-- Whether every sibling is a symbol or string atom. -/
  allSymStr : Bool
  /-- Admission verdicts of the first sibling for top-level singleton checking. -/
  singleton : Scopes n

/-- Grammar-relevant properties of one completed expression. -/
structure Value (n : Nat) where
  /-- Whether this expression is a list. -/
  isList : Bool
  /-- Atom classification, or a sentinel for list expressions. -/
  info : AtomClass n
  /-- Whether this expression can be a recipient address or address group. -/
  group : Bool
  /-- Whether this expression is an admissible caused-by value. -/
  causal : Bool
  /-- Recursive message admission verdict for each finite scope. -/
  messages : Scopes n

/-- Finite representation of atom predicates and scope membership. -/
def AtomClass.codec (n : Nat) : FiniteCodec (AtomClass n) :=
  ((FiniteCodec.fin 4).product ((FiniteCodec.bool.functions (n+1)).product ((FiniteCodec.fin n).product ((FiniteCodec.bool).product ((FiniteCodec.bool).product (FiniteCodec.fin 3)))))).retract
    (fun x => (x.tag, (x.permits, (x.dialectScope, (x.address, (x.symStr, x.keyword))))))
    (fun p => { tag := p.1, permits := p.2.1, dialectScope := p.2.2.1, address := p.2.2.2.1, symStr := p.2.2.2.2.1, keyword := p.2.2.2.2.2 }) (by intro x; cases x; rfl)

/-- Finite representation of all recursive sibling-summary fields. -/
def Accumulator.codec (n : Nat) : FiniteCodec (Accumulator n) :=
  ((FiniteCodec.fin 3).product ((AtomClass.codec n).product ((FiniteCodec.fin n).product ((FiniteCodec.bool).product ((FiniteCodec.bool.functions (n+1)).product ((FiniteCodec.bool).product ((FiniteCodec.fin 4).product ((FiniteCodec.bool).product ((FiniteCodec.bool).product (FiniteCodec.bool.functions (n+1))))))))))).retract
    (fun x => (x.count, (x.head, (x.langScope, (x.langOK, (x.lastList, (x.firstArg, (x.pending, (x.allAddresses, (x.allSymStr, x.singleton))))))))))
    (fun p => { count := p.1, head := p.2.1, langScope := p.2.2.1, langOK := p.2.2.2.1, lastList := p.2.2.2.2.1, firstArg := p.2.2.2.2.2.1, pending := p.2.2.2.2.2.2.1, allAddresses := p.2.2.2.2.2.2.2.1, allSymStr := p.2.2.2.2.2.2.2.2.1, singleton := p.2.2.2.2.2.2.2.2.2 }) (by intro x; cases x; rfl)

/-- Sentinel classification with no atom predicates enabled. -/
def noAtom (n : Nat) : AtomClass n := ⟨0, fun _ => false, 0, false, false, 0⟩

/-- Initial sibling summary for the installed grammar. -/
def empty (n : Nat) : Accumulator n :=
  ⟨0, noAtom n, 0, false, fun _ => false, true, 0, true, true, fun _ => false⟩

/-- Lift an atom classification to expression-level properties. -/
def atomValue (a : AtomClass n) : Value n :=
  ⟨false, a, a.address, a.symStr, fun _ => false⟩

/-- Grammar of simple tails, evaluated left to right. Pending 4 is rejection. -/
def nextPending (s : Accumulator n) (v : Value n) : Fin 5 :=
  if s.firstArg && v.group then 0
  else if s.pending == 1 then 0
  else if s.pending == 2 then if v.info.symStr then 0 else 4
  else if s.pending == 3 then if v.causal then 0 else 4
  else if s.pending == 4 then 4
  else if v.info.keyword == 1 then 1
  else if v.info.keyword == 2 then 2
  else if v.info.keyword == 3 then 3
  else if v.group then 4 else 0

/-- Append one expression and update all sibling grammar obligations. -/
def appendValue (s : Accumulator n) (v : Value n) : Accumulator n where
  count := if s.count == 0 then 1 else if s.count == 1 then 2 else 3
  head := if s.count == 0 then v.info else s.head
  langScope := if s.count == 1 then
    (if v.info.tag != 0 then v.info.dialectScope else 0) else s.langScope
  langOK := if s.count == 2 then s.langScope != 0 && v.messages s.langScope else s.langOK
  lastList := if v.isList then v.messages else s.lastList
  firstArg := if s.count == 0 then true else false
  pending := if s.count == 0 then 0 else nextPending s v
  allAddresses := s.allAddresses && v.info.address
  allSymStr := s.allSymStr && v.info.symStr
  singleton := if s.count == 0 then v.messages else s.singleton

/-- Recursive list productions: simple, meta, lang, and last-list wrappers. -/
def listValue (s : Accumulator n) : Value n where
  isList := true
  info := noAtom n
  group := s.count != 0 && s.allAddresses
  causal := s.count != 0 && s.allSymStr
  messages scope :=
    if s.head.tag == 1 then s.pending == 0 && s.head.permits scope
    else if s.head.tag == 2 then s.count.val >= 2
    else if s.head.tag == 3 then s.langOK
    else if s.head.tag == 4 then s.lastList scope
    else false

/-- Typed recursive message grammar for the given number of dialect scopes. -/
def grammar (n : Nat) : SummaryGrammar (AtomClass n) (Accumulator n) where
  empty := empty n
  atom s a := appendValue s (atomValue a)
  list s child := appendValue s (listValue child)
  accept s := s.count == 1 && s.singleton 0

/-- Recognise the symbol characters permitted by the lexical contract. -/
def symbolCharacter (c : Char) : Bool :=
  (c.toNat >= 65 && c.toNat <= 90) || (c.toNat >= 97 && c.toNat <= 122) ||
    (c.toNat >= 48 && c.toNat <= 57) || "_-./!?+*<>=@".toList.contains c

/-- Recognise an at sign followed by at least one symbol character. -/
def addressSymbol (s : String) : Bool :=
  match s.toList with
  | '@' :: c :: cs => (c :: cs).all symbolCharacter
  | _ => false

/-- The environment is consulted only while classifying finite atom categories. -/
def classify (ds : List Dialect) : Atom → AtomClass ds.length
  | .symbol s =>
    { tag := if s == "meta" then 2 else if s == "lang" then 3
        else if ["envelope", "signed", "with-limits", "with-roles"].contains s then 4 else 1
      permits := fun i => corePerformativeNames.contains s ||
        (i.val != 0 && (ds[i.val-1]?).any (fun d => d.performativeNames.contains s))
      dialectScope := ((List.finRange (ds.length+1)).find? (fun i =>
        i.val != 0 && (ds[i.val-1]?).any (fun d => d.name == s))).getD 0
      address := addressSymbol s
      symStr := true
      keyword := 0 }
  | .str _ => { noAtom ds.length with symStr := true }
  | .keyword k => { noAtom ds.length with keyword :=
      if k == "thread" || k == "sender" then 2 else if k == "caused-by" then 3 else 1 }
  | _ => noAtom ds.length

/-- All exact symbol comparisons made by the grammar occur in this finite table. -/
def symbolTable (ds : List Dialect) : List String :=
  ["meta", "lang", "envelope", "signed", "with-limits", "with-roles"] ++
    corePerformativeNames ++ ds.flatMap (fun d => d.name :: d.performativeNames)

/-- Finite alphabet of ordinary atom categories and exact environment names. -/
def alphabet (ds : List Dialect) : FiniteCodec (Fin ((symbolTable ds).length+7)) :=
  FiniteCodec.fin ((symbolTable ds).length+6)

/-- Ordinary atom categories precede the environment's exact symbol table. -/
def decodeAtom (ds : List Dialect) (i : Fin ((symbolTable ds).length+7)) : AtomClass ds.length :=
  if h : i.val < 7 then
    if i.val == 1 then { noAtom ds.length with symStr := true }
    else if i.val == 2 then { noAtom ds.length with keyword := 1 }
    else if i.val == 3 then { noAtom ds.length with keyword := 2 }
    else if i.val == 4 then { noAtom ds.length with keyword := 3 }
    else if i.val == 5 then { noAtom ds.length with tag := 1, symStr := true }
    else if i.val == 6 then { noAtom ds.length with tag := 1, symStr := true, address := true }
    else noAtom ds.length
  else classify ds (.symbol ((symbolTable ds)[i.val-7]'(by have := i.isLt; omega)))

/-- Encode a concrete atom without losing any grammar-relevant predicate. -/
def encodeAtom (ds : List Dialect) : Atom → Fin ((symbolTable ds).length+7)
  | .symbol s =>
    match (List.finRange (symbolTable ds).length).find? (fun i => (symbolTable ds)[i] == s) with
    | some i => ⟨i.val+7, by have := i.isLt; omega⟩
    | none => if (classify ds (.symbol s)).address then ⟨6, by omega⟩ else ⟨5, by omega⟩
  | .str _ => ⟨1, by omega⟩
  | .keyword k => if k == "thread" || k == "sender" then ⟨3, by omega⟩
      else if k == "caused-by" then ⟨4, by omega⟩ else ⟨2, by omega⟩
  | _ => ⟨0, by omega⟩

private theorem classify_unknown (ds : List Dialect) (s : String)
    (hn : s ∉ symbolTable ds) :
    classify ds (.symbol s) = ⟨1, fun _ => false, 0, (classify ds (.symbol s)).address, true, 0⟩ := by
  have hc : s ∉ corePerformativeNames := fun h => hn (by simp [symbolTable, h])
  have hr : s ∉ ["meta", "lang", "envelope", "signed", "with-limits", "with-roles"] :=
    fun h => hn (by simp only [symbolTable, List.mem_append]; exact Or.inl (Or.inl h))
  have hd (d : Dialect) (h : d ∈ ds) : s ≠ d.name ∧ s ∉ d.performativeNames := by
    constructor
    · intro he; apply hn; simp only [symbolTable, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨d, h, by simp [he]⟩
    · intro he; apply hn; simp only [symbolTable, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨d, h, by simp [he]⟩
  have hp (i : Nat) : (ds[i]?).any (fun d => d.performativeNames.contains s) = false := by
    cases hg : ds[i]? with
    | none => rfl
    | some d => simpa using (hd d (List.mem_of_getElem? hg)).2
  have hname (i : Nat) : (ds[i]?).any (fun d => d.name == s) = false := by
    cases hg : ds[i]? with
    | none => rfl
    | some d => simpa [ne_comm] using (hd d (List.mem_of_getElem? hg)).1
  have hf : (List.finRange (ds.length+1)).find? (fun _ => false) = none := by
    simp only [List.find?_eq_none]; simp
  simp only [List.mem_cons, not_or] at hr
  simp only [classify, hp, hname, Bool.and_false, Bool.or_false, hf]
  simp [hc, hr]

/-- The finite alphabet preserves every grammar predicate on concrete atoms. -/
theorem decode_encode_atom (ds : List Dialect) (a : Atom) :
    decodeAtom ds (encodeAtom ds a) = classify ds a := by
  cases a with
  | num _ => rfl
  | bool _ => rfl
  | str _ => rfl
  | keyword k =>
    simp only [encodeAtom, classify]
    split <;> simp_all [decodeAtom]
    split <;> simp_all
  | symbol s =>
    cases hf : (List.finRange (symbolTable ds).length).find?
        (fun i => (symbolTable ds)[i] == s) with
    | some i =>
      have he : (symbolTable ds)[i] = s := by simpa using List.find?_some hf
      simp only [encodeAtom, hf, decodeAtom]
      rw [dif_neg (by omega)]
      simpa using congrArg (fun name => classify ds (.symbol name)) he
    | none =>
      have hn : s ∉ symbolTable ds := by
        intro hm
        obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
        have h := (List.find?_eq_none.mp hf) ⟨i, hi⟩ (List.mem_finRange _)
        simp [he] at h
      have hu := classify_unknown ds s hn
      simp only [encodeAtom, hf]
      split <;> simp_all [decodeAtom, noAtom]

/-- Specialise the typed grammar to the environment-dependent atom alphabet. -/
def environmentGrammar (ds : List Dialect) :
    SummaryGrammar (Fin ((symbolTable ds).length+7)) (Accumulator ds.length) :=
  { grammar ds.length with atom := fun s i => appendValue s (atomValue (decodeAtom ds i)) }

/-- Language of encoded forests admitted by the installed grammar. -/
def tokenLanguage (ds : List Dialect) := (environmentGrammar ds).language (alphabet ds)

/-- Each finite installed environment has its own finite-alphabet DPDA. -/
def environmentDCFL (ds : List Dialect) : IsRealtimeDCFL (tokenLanguage ds) :=
  (environmentGrammar ds).isRealtimeDCFL (alphabet ds) (Accumulator.codec ds.length)

/-- Replace concrete atoms in a syntax tree with their finite classifications. -/
def classifyTree (ds : List Dialect) : SExpr → SyntaxTree (alphabet ds).size
  | .atom a => .atom (encodeAtom ds a)
  | .list xs => .node (xs.map (classifyTree ds))

mutual
 /-- Direct syntax interpretation, using concrete atoms rather than alphabet codes. -/
 def directTree (ds : List Dialect) (s : Accumulator ds.length) : SExpr → Accumulator ds.length
   | .atom a => appendValue s (atomValue (classify ds a))
   | .list xs => appendValue s (listValue (directForest ds xs (empty ds.length)))
 /-- Evaluate concrete siblings directly, without finite-code machine execution. -/
 def directForest (ds : List Dialect) : List SExpr → Accumulator ds.length → Accumulator ds.length
   | [], s => s
   | x :: xs, s => directForest ds xs (directTree ds s x)
end

/-- Compute the grammar properties of one concrete expression. -/
def directValue (ds : List Dialect) : SExpr → Value ds.length
  | .atom a => atomValue (classify ds a)
  | .list xs => listValue (directForest ds xs (empty ds.length))

/-- Concrete, scope-indexed recursive syntactic admission, independent of machine execution. -/
def admittedAt (ds : List Dialect) (scope : Fin (ds.length+1)) (e : SExpr) : Prop :=
  (directValue ds e).messages scope = true

/-- Concrete recursive admission in the initial unscoped context. -/
def admitted (ds : List Dialect) (e : SExpr) : Prop := admittedAt ds 0 e

instance (ds : List Dialect) (scope : Fin (ds.length+1)) (e : SExpr) :
    Decidable (admittedAt ds scope e) := inferInstanceAs (Decidable (_ = true))
instance (ds : List Dialect) (e : SExpr) : Decidable (admitted ds e) :=
  inferInstanceAs (Decidable (admittedAt ds 0 e))

mutual
 theorem encoded_direct_tree (ds : List Dialect) (e : SExpr) (s : Accumulator ds.length) :
    (environmentGrammar ds).tree (alphabet ds) s (classifyTree ds e) = directTree ds s e := by
  cases e with
  | atom a =>
    simp only [classifyTree, SummaryGrammar.tree, environmentGrammar, alphabet, FiniteCodec.fin, id_eq]
    change appendValue s (atomValue (decodeAtom ds (encodeAtom ds a))) = _
    rw [decode_encode_atom]
    rfl
  | list xs =>
    simp only [classifyTree, SummaryGrammar.tree]
    change appendValue s (listValue ((environmentGrammar ds).forest (alphabet ds)
      (xs.map (classifyTree ds)) (empty ds.length))) = _
    rw [encoded_direct_forest]
    rfl
 termination_by sizeOf e

 theorem encoded_direct_forest (ds : List Dialect) (xs : List SExpr) (s : Accumulator ds.length) :
    (environmentGrammar ds).forest (alphabet ds) (xs.map (classifyTree ds)) s = directForest ds xs s := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [List.map_cons, SummaryGrammar.forest, directForest]
    rw [encoded_direct_tree, encoded_direct_forest]
 termination_by sizeOf xs
end

/-- Recognition of a concrete expression by the constructed finite DPDA. -/
theorem recognizes_expression (ds : List Dialect) (e : SExpr) :
    (environmentDCFL ds).machine.accepts (SyntaxTree.encode (classifyTree ds e)) = true ↔
      admitted ds e := by
  have h := ((environmentGrammar ds).compile (alphabet ds)
    (Accumulator.codec ds.length)).accepts_encoding [classifyTree ds e]
  change (environmentDCFL ds).machine.accepts (SyntaxTree.encodeForest [classifyTree ds e]) =
    (environmentGrammar ds).accept ((Accumulator.codec ds.length).decode
      (((environmentGrammar ds).compile (alphabet ds) (Accumulator.codec ds.length)).foldForest
        [classifyTree ds e] ((Accumulator.codec ds.length).encode (environmentGrammar ds).empty))) at h
  rw [SummaryGrammar.compile_forest, (Accumulator.codec ds.length).decode_encode] at h
  simp only [SummaryGrammar.forest, SyntaxTree.encodeForest_single] at h
  change _ = (environmentGrammar ds).accept ((environmentGrammar ds).tree (alphabet ds)
    (empty ds.length) (classifyTree ds e)) at h
  rw [encoded_direct_tree] at h
  rw [h]
  cases e <;> rfl

end CBCL.InstalledSyntax
