import Lean
import Init.Data.Rat.Lemmas

/-! SPEC-041 exact, representation-tagged values. This additive model does not
silently add float/decimal cases to legacy CBCL.Atom or its existing proofs. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace CBCL.FlatContracts

inductive Rep where
  | integer | float | decimal | string | symbol | keyword | bool | list
  deriving Repr, DecidableEq

def allReps : List Rep := [.integer,.float,.decimal,.string,.symbol,.keyword,.bool,.list]

theorem mem_allReps (r : Rep) : r ∈ allReps := by cases r <;> simp [allReps]

/-- Float payloads are canonical finite IEEE-754 bits. Decimal payloads are a
signed coefficient and nonnegative base-ten scale, with trailing zeroes removed.
Recognition is explicit so malformed transport values cannot masquerade as wire atoms. -/
inductive Atom where
  | integer (n : Int)
  | float (bits : Nat)
  | decimal (coefficient : Int) (scale : Nat)
  | string (text : String)
  | symbol (text : String)
  | keyword (text : String)
  | bool (value : Bool)
  deriving Repr, DecidableEq

def Atom.rep : Atom → Rep
  | .integer _ => .integer | .float _ => .float | .decimal _ _ => .decimal
  | .string _ => .string | .symbol _ => .symbol | .keyword _ => .keyword | .bool _ => .bool

def Atom.Valid : Atom → Prop
  | .integer n => -(2^63 : Int) ≤ n ∧ n < 2^63
  | .float bits => bits < 2^64 ∧ (bits / 2^52) % 2048 < 2047 ∧ bits ≠ 2^63
  | .decimal n scale => scale = 0 ∨ n % 10 ≠ 0
  | _ => True

instance (a : Atom) : Decidable a.Valid := by cases a <;> unfold Atom.Valid <;> infer_instance

/-- Exact decoding, including subnormals; no binary-to-decimal text approximation. -/
def binary64 (bits : Nat) : Rat :=
  let exponent := (bits / 2^52) % 2048
  let mantissa := bits % 2^52 + if exponent = 0 then 0 else 2^52
  let signed : Int := if bits / 2^63 = 0 then Int.ofNat mantissa else -Int.ofNat mantissa
  if exponent = 0 then Rat.normalize signed (2^1074) (by simp)
  else if 1075 ≤ exponent then Rat.normalize (signed * Int.ofNat (2^(exponent-1075)))
  else Rat.normalize signed (2^(1075-exponent)) (by simp)

def Atom.numeric (a : Atom) : Option Rat :=
  if a.Valid then
    match a with
    | .integer n => some (Rat.normalize n)
    | .float bits => some (binary64 bits)
    | .decimal n scale => some (Rat.normalize n (10^scale) (by simp))
    | _ => none
  else none

inductive Value where
  | atom (a : Atom)
  | list (values : List Value)
  deriving Repr

def Value.rep : Value → Rep
  | .atom a => a.rep | .list _ => .list

def Value.scalar : Value → Option Atom
  | .atom a => some a | .list _ => none

def Value.numeric : Value → Option Rat
  | .atom a => a.numeric | .list _ => none

/-- Unicode scalar count, or immediate element count. -/
def Value.length : Value → Option Nat
  | .atom (.string s) => some s.toList.length
  | .list xs => some xs.length
  | _ => none

inductive Cmp where
  | gt | ge | lt | le
  deriving Repr, DecidableEq

/-- Independent mathematical ordering of the interpreted rational values. -/
def Cmp.Denotes : Cmp → Rat → Rat → Prop
  | .gt,a,b => b < a | .ge,a,b => b ≤ a | .lt,a,b => a < b | .le,a,b => a ≤ b

/-- Operational cross-products, as used by the arbitrary-precision Rust checker. -/
def Cmp.run : Cmp → Rat → Rat → Bool
  | .gt,a,b => decide (b.num * Int.ofNat a.den < a.num * Int.ofNat b.den)
  | .ge,a,b => decide (b.num * Int.ofNat a.den ≤ a.num * Int.ofNat b.den)
  | .lt,a,b => decide (a.num * Int.ofNat b.den < b.num * Int.ofNat a.den)
  | .le,a,b => decide (a.num * Int.ofNat b.den ≤ b.num * Int.ofNat a.den)

theorem comparison_correct (op : Cmp) (a b : Rat) : op.run a b = true ↔ op.Denotes a b := by
  cases op <;> simp [Cmp.run,Cmp.Denotes,Rat.lt_iff,Rat.le_iff]

/-- Canonical identity retains tags even when mathematical values coincide. -/
theorem integer_not_float (n : Int) (bits : Nat) : Atom.integer n ≠ Atom.float bits := by intro h; cases h

theorem integer_not_decimal (n c : Int) (scale : Nat) : Atom.integer n ≠ Atom.decimal c scale := by intro h; cases h

theorem integer_numeric (n : Int) (h : (Atom.integer n).Valid) :
    (Atom.integer n).numeric = some (Rat.normalize n) := by simp [Atom.numeric,h]

theorem decimal_numeric (n : Int) (scale : Nat) (h : (Atom.decimal n scale).Valid) :
    (Atom.decimal n scale).numeric = some (Rat.normalize n (10^scale) (by simp)) := by simp [Atom.numeric,h]

def decimalBytes (n : Int) (scale : Nat) : Nat :=
  let digits := n.natAbs.repr.length
  let sign := if n < 0 then 1 else 0
  if scale = 0 then sign + digits
  else if scale < digits then sign + digits + 1 else sign + 2 + scale

def Atom.storage : Atom → Nat
  | .string s | .symbol s | .keyword s => s.utf8ByteSize + 1
  | .decimal n scale => decimalBytes n scale + 1
  | _ => 32

def Value.storage : Value → Nat
  | .atom a => a.storage
  | .list xs => 1 + (xs.map Value.storage).sum

def Value.depth : Value → Nat
  | .atom _ => 0
  | .list xs => xs.foldl (fun m x => max m (x.depth + 1)) 0

def Value.decimalsFit : Value → Bool
  | .atom (.decimal n scale) => decide (decimalBytes n scale ≤ 4096)
  | .atom _ => true
  | .list xs => (xs.map Value.decimalsFit).all id

def Value.fits (v : Value) : Bool := decide (v.storage ≤ 65536 ∧ v.depth ≤ 32) && v.decimalsFit

end CBCL.FlatContracts
