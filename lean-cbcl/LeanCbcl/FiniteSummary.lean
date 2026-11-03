import LeanCbcl.FiniteCodec

namespace CBCL.FormalLanguage

/-- A typed presentation of a finite grammar evaluator. Its finite encodings
    are compiled through the already proved forest construction. -/
structure SummaryGrammar (α σ : Type) where
  /-- Typed summary of an empty forest. -/
  empty : σ
  /-- Update a typed sibling summary with an atom. -/
  atom : σ → α → σ
  /-- Update a typed parent summary with a completed child-list summary. -/
  list : σ → σ → σ
  /-- Accept a completed top-level typed summary. -/
  accept : σ → Bool

namespace SummaryGrammar

/-- Compile typed grammar operations through finite atom and summary codecs. -/
def compile (G : SummaryGrammar α σ) (C : FiniteCodec α) (S : FiniteCodec σ) :
    ForestAlgebra C.size S.size where
  empty := S.encode G.empty
  atom s a := S.encode (G.atom (S.decode s) (C.decode a))
  list s child := S.encode (G.list (S.decode s) (S.decode child))
  accept s := G.accept (S.decode s)

mutual
 /-- Evaluate one encoded tree using typed grammar operations. -/
 def tree (G : SummaryGrammar α σ) (C : FiniteCodec α) (s : σ) : SyntaxTree C.size → σ
   | .atom a => G.atom s (C.decode a)
   | .node xs => G.list s (G.forest C xs G.empty)
 /-- Evaluate encoded siblings using typed grammar operations. -/
 def forest (G : SummaryGrammar α σ) (C : FiniteCodec α) : List (SyntaxTree C.size) → σ → σ
   | [], s => s
   | x :: xs, s => G.forest C xs (G.tree C s x)
end

mutual
 theorem compile_tree (G : SummaryGrammar α σ) (C : FiniteCodec α) (S : FiniteCodec σ)
    (x : SyntaxTree C.size) (s : σ) :
    (G.compile C S).foldTree (S.encode s) x = S.encode (G.tree C s x) := by
  cases x with
  | atom a => simp [ForestAlgebra.foldTree, compile, tree, S.decode_encode]
  | node xs =>
    change S.encode (G.list (S.decode (S.encode s))
      (S.decode ((G.compile C S).foldForest xs (S.encode G.empty)))) =
      S.encode (G.list s (G.forest C xs G.empty))
    rw [compile_forest G C S xs G.empty]
    simp only [S.decode_encode]
 termination_by sizeOf x

 theorem compile_forest (G : SummaryGrammar α σ) (C : FiniteCodec α) (S : FiniteCodec σ)
    (xs : List (SyntaxTree C.size)) (s : σ) :
    (G.compile C S).foldForest xs (S.encode s) = S.encode (G.forest C xs s) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [ForestAlgebra.foldForest, forest]
    rw [compile_tree G C S x s, compile_forest G C S xs (G.tree C s x)]
 termination_by sizeOf xs
end

/-- Encoded forests whose typed summary satisfies the grammar. -/
def language (G : SummaryGrammar α σ) (C : FiniteCodec α) (w : List (Fin (C.size+1+1))) : Prop :=
  ∃ xs, SyntaxTree.encodeForest xs = w ∧ G.accept (G.forest C xs G.empty) = true

theorem language_eq (G : SummaryGrammar α σ) (C : FiniteCodec α) (S : FiniteCodec σ)
    (w : List (Fin (C.size+1+1))) : (G.compile C S).language w ↔ G.language C w := by
  change (∃ xs, SyntaxTree.encodeForest xs = w ∧
    G.accept (S.decode ((G.compile C S).foldForest xs (S.encode G.empty))) = true) ↔ _
  simp only [compile_forest, S.decode_encode, language]

/-- Construct a finite DPDA certificate for the typed grammar language. -/
def isRealtimeDCFL (G : SummaryGrammar α σ) (C : FiniteCodec α) (S : FiniteCodec σ) :
    IsRealtimeDCFL (G.language C) where
  stateSize := S.size + S.size
  stackSize := S.size + S.size + 1
  machine := (G.compile C S).machine
  correct w := ((G.compile C S).accepts_iff w).trans (G.language_eq C S w)

end SummaryGrammar
end CBCL.FormalLanguage
