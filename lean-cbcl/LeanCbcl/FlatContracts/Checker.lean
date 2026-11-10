import LeanCbcl.FlatContracts.Value

/-! Declarative contract membership and executable Boolean checking. Regex
correctness is a named leaf hypothesis, never an axiom or a Rust result input. -/
set_option autoImplicit false
namespace CBCL.FlatContracts

inductive Builtin where
  | integer | float | decimal | number | nonnegative | string | hlc | symbol | keyword | bool | list
  deriving Repr, BEq, DecidableEq

def hexChar (c : Char) : Prop := ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')
instance (c : Char) : Decidable (hexChar c) := by unfold hexChar; infer_instance

def hlcSyntax (s : String) : Prop :=
  s.startsWith "hlc-" = true ∧ s.toList.length = 29 ∧ s.toList[20]? = some '-' ∧
  (∀ c ∈ (s.toList.drop 4).take 16, hexChar c) ∧ (∀ c ∈ s.toList.drop 21, hexChar c)
instance (s : String) : Decidable (hlcSyntax s) := by unfold hlcSyntax; infer_instance

/-- Representation-level mathematical predicates, independent of the checker. -/
def Builtin.Denotes : Builtin → Value → Prop
  | .integer,.atom (.integer n) => (Atom.integer n).Valid
  | .float,.atom (.float bits) => (Atom.float bits).Valid
  | .decimal,.atom (.decimal n s) => (Atom.decimal n s).Valid
  | .number,v => v.numeric.isSome = true
  | .nonnegative,.atom (.integer n) => (Atom.integer n).Valid ∧ 0 ≤ n
  | .string,.atom (.string _) => True
  | .hlc,.atom (.string text) => hlcSyntax text
  | .symbol,.atom (.symbol _) => True
  | .keyword,.atom (.keyword _) => True
  | .bool,.atom (.bool _) => True
  | .list,.list _ => True
  | _,_ => False

instance (b : Builtin) (v : Value) : Decidable (b.Denotes v) := by
  cases b <;> cases v with
  | atom a => cases a <;> unfold Builtin.Denotes <;> infer_instance
  | list xs => unfold Builtin.Denotes; infer_instance

def Builtin.run (b : Builtin) (v : Value) : Bool := decide (b.Denotes v)

def Cmp.natDenotes : Cmp → Nat → Nat → Prop
  | .gt,a,b => b < a | .ge,a,b => b ≤ a | .lt,a,b => a < b | .le,a,b => a ≤ b

def Cmp.natRun (op : Cmp) (a b : Nat) : Bool :=
  match op with
  | .gt => decide (b < a) | .ge => decide (b ≤ a) | .lt => decide (a < b) | .le => decide (a ≤ b)

theorem nat_comparison_correct (op : Cmp) (a b : Nat) :
    op.natRun a b = true ↔ op.natDenotes a b := by cases op <;> simp [Cmp.natRun,Cmp.natDenotes]

inductive Predicate where
  | bound (op : Cmp) (literal : Atom)
  | length (bounds : List (Cmp × Nat))
  | pattern (source : String)
  deriving Repr

/-- No particular regex implementation is baked into the theorem. -/
structure RegexBackend where
  run : String → String → Bool
  language : String → String → Prop
  work : String → Nat

def RegexCorrect (backend : RegexBackend) : Prop :=
  ∀ source text, backend.run source text = true ↔ backend.language source text

def Predicate.Denotes (language : String → String → Prop) : Predicate → Value → Prop
  | .bound op literal,value => ∃ a b, value.numeric = some a ∧ literal.numeric = some b ∧ op.Denotes a b
  | .length bounds,value => ∃ n, value.length = some n ∧ ∀ bound ∈ bounds, bound.1.natDenotes n bound.2
  | .pattern source,.atom (.string text) => language source text
  | .pattern _,_ => False

def Predicate.run (backend : RegexBackend) : Predicate → Value → Bool
  | .bound op literal,value => match value.numeric,literal.numeric with
      | some a,some b => op.run a b | _,_ => false
  | .length bounds,value => match value.length with
      | some n => bounds.all (fun bound => bound.1.natRun n bound.2) | none => false
  | .pattern source,.atom (.string text) => backend.run source text
  | .pattern _,_ => false

theorem predicate_correct (backend : RegexBackend) (correct : RegexCorrect backend)
    (p : Predicate) (v : Value) : p.run backend v = true ↔ p.Denotes backend.language v := by
  cases p with
  | bound op literal =>
      cases hv : v.numeric <;> cases hl : literal.numeric <;>
        simp [Predicate.run,Predicate.Denotes,hv,hl,comparison_correct]
  | length bounds =>
      cases hv : v.length <;>
        simp [Predicate.run,Predicate.Denotes,hv,List.all_eq_true,nat_comparison_correct]
  | pattern source =>
      cases v with
      | atom a => cases a <;> simp [Predicate.run,Predicate.Denotes]
                  exact correct source _
      | list xs => simp [Predicate.run,Predicate.Denotes]

inductive Leaf where
  | builtin (kind : Builtin)
  | enumeration (members : List Atom)
  | refined (base : Builtin) (predicates : List Predicate)
  deriving Repr

def Leaf.Denotes (language : String → String → Prop) : Leaf → Value → Prop
  | .builtin kind,value => kind.Denotes value
  | .enumeration members,value => ∃ a, value.scalar = some a ∧ a ∈ members
  | .refined base predicates,value => base.Denotes value ∧ ∀ p ∈ predicates, p.Denotes language value

def Leaf.run (backend : RegexBackend) : Leaf → Value → Bool
  | .builtin kind,value => kind.run value
  | .enumeration members,value => match value.scalar with
      | some a => decide (a ∈ members) | none => false
  | .refined base predicates,value => base.run value && predicates.all (fun p => p.run backend value)

theorem leaf_correct (backend : RegexBackend) (correct : RegexCorrect backend)
    (leaf : Leaf) (value : Value) : leaf.run backend value = true ↔ leaf.Denotes backend.language value := by
  cases leaf with
  | builtin kind => simp [Leaf.run,Leaf.Denotes,Builtin.run]
  | enumeration members => cases hv : value.scalar <;> simp [Leaf.run,Leaf.Denotes,hv]
  | refined base predicates =>
      simp [Leaf.run,Leaf.Denotes,Builtin.run,List.all_eq_true,predicate_correct backend correct]

inductive Code where
  | leaf (contract : Leaf)
  | named (name : String) (body : Code)
  | all (children : List Code)
  | any (children : List Code)
  deriving Repr

/-- Structural recursion over code and its genuine child lists. -/
noncomputable def Code.fold {W : Type} (leaf : Leaf → W) (named : String → W → W)
    (all any : List W → W) : Code → W :=
  Code.rec (motive_1 := fun _ => W) (motive_2 := fun _ => List W)
    leaf (fun name _ result => named name result)
    (fun _ results => all results) (fun _ results => any results) [] (fun _ _ x xs => x::xs)

theorem Code.fold_list {W : Type} (leaf : Leaf → W) (named : String → W → W)
    (all any : List W → W) (children : List Code) :
    Code.rec_1 (motive_1 := fun _ => W) (motive_2 := fun _ => List W)
      leaf (fun name _ result => named name result)
      (fun _ results => all results) (fun _ results => any results) [] (fun _ _ x xs => x::xs) children =
      children.map (Code.fold leaf named all any) := by
  induction children with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (Code.fold leaf named all any head)) ih

@[simp] theorem Code.fold_all {W : Type} (leaf : Leaf → W) (named : String → W → W)
    (all any : List W → W) (children : List Code) :
    Code.fold leaf named all any (.all children) = all (children.map (Code.fold leaf named all any)) :=
  congrArg all (Code.fold_list leaf named all any children)

@[simp] theorem Code.fold_any {W : Type} (leaf : Leaf → W) (named : String → W → W)
    (all any : List W → W) (children : List Code) :
    Code.fold leaf named all any (.any children) = any (children.map (Code.fold leaf named all any)) :=
  congrArg any (Code.fold_list leaf named all any children)

/-- Operational n-ary Boolean composition. -/
def Code.run (backend : RegexBackend) : Code → Value → Bool
  | .leaf contract,value => contract.run backend value
  | .named _ body,value => body.run backend value
  | .all children,value => (children.map (fun child => child.run backend value)).all id
  | .any children,value => (children.map (fun child => child.run backend value)).any id

/-- Set-theoretic membership, rather than an alias for a checker result. -/
noncomputable def Code.Denotes (language : String → String → Prop) : Code → Value → Prop :=
  Code.fold (Leaf.Denotes language) (fun _ body => body)
    (fun children value => ∀ p ∈ children, p value)
    (fun children value => ∃ p ∈ children, p value)

@[simp] theorem Code.run_all (backend : RegexBackend) (children : List Code) (value : Value) :
    (.all children : Code).run backend value = children.all (fun c => c.run backend value) := by
  simp [Code.run, List.all_map,Function.comp_def]

@[simp] theorem Code.run_any (backend : RegexBackend) (children : List Code) (value : Value) :
    (.any children : Code).run backend value = children.any (fun c => c.run backend value) := by
  simp [Code.run, List.any_map,Function.comp_def]

@[simp] theorem Code.denotes_all (language : String → String → Prop) (children : List Code) (value : Value) :
    (.all children : Code).Denotes language value ↔ ∀ c ∈ children, c.Denotes language value := by
  simp [Code.Denotes]

@[simp] theorem Code.denotes_any (language : String → String → Prop) (children : List Code) (value : Value) :
    (.any children : Code).Denotes language value ↔ ∃ c ∈ children, c.Denotes language value := by
  unfold Code.Denotes
  rw [Code.fold_any]
  constructor
  · rintro ⟨p,hm,yes⟩
    rcases List.mem_map.mp hm with ⟨c,hc,equal⟩
    rw [← equal] at yes
    exact ⟨c,hc,yes⟩
  · rintro ⟨c,member,yes⟩
    exact ⟨_,List.mem_map.mpr ⟨c,member,rfl⟩,yes⟩

/-- The checker theorem is conditional only on the named regex leaf hypothesis. -/
theorem checker_correct (backend : RegexBackend) (correct : RegexCorrect backend)
    (code : Code) (value : Value) : code.run backend value = true ↔ code.Denotes backend.language value := by
  induction code using Code.rec
      (motive_2 := fun children => ∀ child ∈ children,
        child.run backend value = true ↔ child.Denotes backend.language value) with
  | leaf contract => simpa [Code.run,Code.Denotes,Code.fold] using leaf_correct backend correct contract value
  | named name body ih => simpa [Code.run,Code.Denotes,Code.fold] using ih
  | all children ih =>
      simp only [Code.run_all,List.all_eq_true,Code.denotes_all]
      constructor
      · intro h child member; exact (ih child member).mp (h child member)
      · intro h child member; exact (ih child member).mpr (h child member)
  | any children ih =>
      simp only [Code.run_any,List.any_eq_true,Code.denotes_any]
      constructor
      · rintro ⟨child,member,h⟩; exact ⟨child,member,(ih child member).mp h⟩
      · rintro ⟨child,member,h⟩; exact ⟨child,member,(ih child member).mpr h⟩
  | nil child member => simp at member
  | cons head tail ih iht child member =>
      rcases List.mem_cons.mp member with equal | member
      · subst child; exact ih
      · exact iht child member

def Predicate.work (backend : RegexBackend) : Predicate → Nat
  | .bound _ _ => 16 * 4096 * 4096
  | .length bounds => 65536 * (bounds.length + 1)
  | .pattern source => backend.work source

def Leaf.work (backend : RegexBackend) : Leaf → Nat
  | .builtin _ => 1
  | .enumeration members => 65536 * members.length + 1
  | .refined _ predicates => 1 + (predicates.map (Predicate.work backend)).sum

/-- Repeated aliases count repeatedly in reservation; no caller's actual
short-circuit path can change the complete pre-evaluation allowance. -/
def Code.work (backend : RegexBackend) : Code → Nat
  | .leaf contract => contract.work backend
  | .named _ body => 1 + body.work backend
  | .all children | .any children => 1 + (children.map (Code.work backend)).sum

inductive Verdict where
  | accepted | violation | resourceLimit
  deriving Repr, DecidableEq, BEq

def check (backend : RegexBackend) (fits : Value → Bool) (code : Code) (value : Value) (available : Nat) : Verdict :=
  if available < code.work backend ∨ fits value = false then .resourceLimit
  else if code.run backend value then .accepted else .violation

theorem insufficient_work (backend : RegexBackend) (fits : Value → Bool) (code : Code) (value : Value)
    (available : Nat) (short : available < code.work backend) :
    check backend fits code value available = .resourceLimit := by simp [check,short]

theorem bounded_acceptance (backend : RegexBackend) (correct : RegexCorrect backend)
    (fits : Value → Bool) (code : Code) (value : Value) (available : Nat)
    (enough : code.work backend ≤ available) (input : fits value = true) :
    check backend fits code value available = .accepted ↔ code.Denotes backend.language value := by
  simp [check,Nat.not_lt.mpr enough,input,checker_correct backend correct]

theorem bounded_violation (backend : RegexBackend) (correct : RegexCorrect backend)
    (fits : Value → Bool) (code : Code) (value : Value) (available : Nat)
    (enough : code.work backend ≤ available) (input : fits value = true) :
    check backend fits code value available = .violation ↔ ¬code.Denotes backend.language value := by
  simp [check,Nat.not_lt.mpr enough,input,← checker_correct backend correct]

theorem reservation_permutation (backend : RegexBackend) (a b : List Code) (permuted : a.Perm b) :
    (Code.all a).work backend = (Code.all b).work backend := by
  simp only [Code.work]
  congr 1
  induction permuted with
  | nil => rfl
  | cons head _ ih => simp [ih]
  | swap a b tail => simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem conjunction_permutation (language : String → String → Prop) (a b : List Code)
    (permuted : a.Perm b) (value : Value) :
    (Code.all a).Denotes language value ↔ (Code.all b).Denotes language value := by
  simp only [Code.denotes_all]
  constructor <;> intro h child member
  · exact h child (permuted.mem_iff.mpr member)
  · exact h child (permuted.mem_iff.mp member)

theorem alias_transparent (backend : RegexBackend) (name : String) (body : Code) (value : Value) :
    (Code.named name body).run backend value = body.run backend value := by simp [Code.run]

/-- A successful validation returns the original value, never a converted atom. -/
def checkedValue (backend : RegexBackend) (fits : Value → Bool) (code : Code) (value : Value) (available : Nat) : Option Value :=
  if check backend fits code value available = .accepted then some value else none

theorem preserves_value (backend : RegexBackend) (fits : Value → Bool) (code : Code) (value result : Value) (available : Nat)
    (accepted : checkedValue backend fits code value available = some result) : result = value := by
  unfold checkedValue at accepted
  split at accepted
  · exact (Option.some.inj accepted).symm
  · contradiction

end CBCL.FlatContracts
