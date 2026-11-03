import LeanCbcl.FiniteForest

/-! Finite representations for the scope vectors and syntax summaries of
SPEC-018. A decoder/encoder retraction is required, not merely a size claim. -/
namespace CBCL.FormalLanguage

/-- A finite representation with a decoder that retracts the encoder. -/
structure FiniteCodec (α : Type) where
  /-- Number of available representation codes. -/
  size : Nat
  positive : 0 < size
  /-- Encode a value as a bounded natural number. -/
  encode : α → Fin size
  /-- Interpret every representation code as a value. -/
  decode : Fin size → α
  decode_encode : ∀ x, decode (encode x) = x

namespace FiniteCodec

/-- Transport a finite representation along a retraction. -/
def retract (c : FiniteCodec β) (pack : α → β) (unpack : β → α)
    (h : ∀ x, unpack (pack x) = x) : FiniteCodec α where
  size := c.size
  positive := c.positive
  encode x := c.encode (pack x)
  decode x := unpack (c.decode x)
  decode_encode x := by rw [c.decode_encode, h]

/-- Identity representation for a nonempty finite interval. -/
def fin (n : Nat) : FiniteCodec (Fin (n+1)) where
  size := n+1
  positive := Nat.zero_lt_succ n
  encode := id
  decode := id
  decode_encode _ := rfl

/-- Two-code representation of Boolean values. -/
def bool : FiniteCodec Bool where
  size := 2
  positive := by decide
  encode b := if b then 1 else 0
  decode i := i.val == 1
  decode_encode b := by cases b <;> rfl

/-- Singleton representation of the unit type. -/
def unit : FiniteCodec Unit where
  size := 1
  positive := by decide
  encode _ := 0
  decode _ := ()
  decode_encode x := by cases x; rfl

/-- Represent a pair by mixed-radix encoding of its components. -/
def product (a : FiniteCodec α) (b : FiniteCodec β) : FiniteCodec (α × β) where
  size := a.size * b.size
  positive := Nat.mul_pos a.positive b.positive
  encode x := ⟨(a.encode x.1).val * b.size + (b.encode x.2).val, by
    have h := Nat.mul_le_mul_right b.size (Nat.succ_le_of_lt (a.encode x.1).isLt)
    have hb := (b.encode x.2).isLt
    simp only [Nat.succ_mul] at h
    omega⟩
  decode i := (a.decode ⟨i.val / b.size, (Nat.div_lt_iff_lt_mul b.positive).mpr i.isLt⟩,
    b.decode ⟨i.val % b.size, Nat.mod_lt _ b.positive⟩)
  decode_encode x := by
    have h₁ : ((a.encode x.1).val * b.size + (b.encode x.2).val) / b.size =
        (a.encode x.1).val := by
      simp [Nat.add_div, Nat.div_eq_of_lt (b.encode x.2).isLt, Nat.mod_lt _ b.positive, b.positive]
    have h₂ : ((a.encode x.1).val * b.size + (b.encode x.2).val) % b.size =
        (b.encode x.2).val := by simp [Nat.add_mod, Nat.mod_eq_of_lt (b.encode x.2).isLt]
    apply Prod.ext
    · exact (congrArg a.decode (Fin.ext h₁)).trans (a.decode_encode x.1)
    · exact (congrArg b.decode (Fin.ext h₂)).trans (b.decode_encode x.2)

/-- Represent functions on a finite domain by their finite vector of values. -/
def functions (c : FiniteCodec α) : (n : Nat) → FiniteCodec (Fin n → α)
  | 0 => unit.retract (fun _ => ()) (fun _ i => Fin.elim0 i) (by
      intro f; funext i; exact Fin.elim0 i)
  | n+1 => (c.product (functions c n)).retract
      (fun f => (f 0, fun i => f i.succ))
      (fun p i => Fin.cases p.1 p.2 i) (by
        intro f; funext i; induction i using Fin.cases <;> simp)

end FiniteCodec
end CBCL.FormalLanguage
