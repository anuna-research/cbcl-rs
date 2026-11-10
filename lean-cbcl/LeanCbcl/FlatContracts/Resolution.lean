import LeanCbcl.FlatContracts.Checker

/-! Finite source expansion, declaration-order invariance, and cycle exclusion.
The declarative expansion judgment is independent of the executable resolver. -/
set_option autoImplicit false
namespace CBCL.FlatContracts

def Builtin.reps : Builtin → List Rep
  | .integer | .nonnegative => [.integer]
  | .float => [.float] | .decimal => [.decimal] | .number => [.integer,.float,.decimal]
  | .string | .hlc => [.string] | .symbol => [.symbol] | .keyword => [.keyword]
  | .bool => [.bool] | .list => [.list]

def Leaf.reps : Leaf → List Rep
  | .builtin b | .refined b _ => b.reps
  | .enumeration atoms => allReps.filter (fun r => atoms.any (fun a => decide (a.rep = r)))

def Code.reps : Code → List Rep
  | .leaf contract => contract.reps
  | .named _ body => body.reps
  | .all children => allReps.filter (fun r => (children.map Code.reps).all (fun reps => decide (r ∈ reps)))
  | .any children => allReps.filter (fun r => (children.map Code.reps).any (fun reps => decide (r ∈ reps)))

def isNumeric : Builtin → Bool
  | .integer | .float | .decimal | .number => true | _ => false

def Predicate.domain (base : Builtin) : Predicate → Bool
  | .bound _ atom => isNumeric base && atom.numeric.isSome
  | .pattern _ => decide (base = .string)
  | .length bounds => decide (base = .string ∨ base = .list) &&
      decide (bounds ≠ []) && bounds.all (fun bound => decide (bound.2 < 2^63))

def lower : Cmp → Bool | .gt | .ge => true | _ => false
def upper : Cmp → Bool | .lt | .le => true | _ => false
def strict : Cmp → Bool | .gt | .lt => true | _ => false

/-- Endpoint conditions use exact rational order; they do not attempt to prove
representation-specific domain inhabitation, which SPEC-040 deliberately permits empty. -/
def intervalPair : Predicate → Predicate → Bool
  | .bound lo a,.bound hi b =>
      if lower lo && upper hi then match a.numeric,b.numeric with
        | some x,some y => if strict lo || strict hi then Cmp.lt.run x y else Cmp.le.run x y
        | _,_ => false
      else true
  | _,_ => true

def lengthInterval (predicates : List Predicate) : Bool :=
  let bounds := predicates.flatMap (fun p => match p with | .length bs => bs | _ => [])
  let endpoints := bounds.foldl (fun (range : Int × Int) bound =>
      match bound.1 with
      | .ge => (max range.1 (Int.ofNat bound.2),range.2)
      | .gt => (max range.1 (Int.ofNat bound.2 + 1),range.2)
      | .le => (range.1,min range.2 (Int.ofNat bound.2))
      | .lt => (range.1,min range.2 (Int.ofNat bound.2 - 1))) (0,2^63-1)
  decide (endpoints.1 ≤ endpoints.2)

def Leaf.valid : Leaf → Bool
  | .builtin _ => true
  | .enumeration atoms => decide (atoms ≠ [] ∧ atoms.length ≤ 256 ∧ atoms.Nodup) && atoms.all (fun a => decide a.Valid)
  | .refined base predicates =>
      decide (predicates ≠ []) && predicates.all (Predicate.domain base) &&
      predicates.all (fun a => predicates.all (intervalPair a)) && lengthInterval predicates

inductive Expr where
  | leaf (contract : Leaf)
  | ref (name : String)
  | all (children : List Expr)
  | any (children : List Expr)
  deriving Repr

abbrev Env := String → Option Expr
abbrev Definitions := List (String × Expr)

/-- All declarations are available during resolution, not a prefix of the source. -/
def lookup : Definitions → Env
  | [],_ => none
  | (name,body)::rest,key => if name = key then some body else lookup rest key

def FunctionalNames (definitions : Definitions) : Prop :=
  ∀ key a b, (key,a) ∈ definitions → (key,b) ∈ definitions → a = b

theorem lookup_some_mem (definitions : Definitions) (key : String) (body : Expr)
    (found : lookup definitions key = some body) : (key,body) ∈ definitions := by
  induction definitions with
  | nil => simp [lookup] at found
  | cons head tail ih =>
      rcases head with ⟨name,value⟩
      by_cases equal : name = key
      · subst name; simp [lookup] at found; subst value; simp
      · simp [lookup,equal] at found; exact List.mem_cons_of_mem _ (ih found)

theorem lookup_of_mem (definitions : Definitions) (unique : FunctionalNames definitions)
    (key : String) (body : Expr) (member : (key,body) ∈ definitions) : lookup definitions key = some body := by
  induction definitions with
  | nil => simp at member
  | cons head tail ih =>
      rcases head with ⟨name,value⟩
      by_cases equal : name = key
      · subst name
        have same : value = body := unique key value body (by simp) member
        simp [lookup,same]
      · have tailMember : (key,body) ∈ tail := by
          rcases List.mem_cons.mp member with h | h
          · cases h; exact False.elim (equal rfl)
          · exact h
        have tailUnique : FunctionalNames tail := by
          intro k a b ha hb; exact unique k a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)
        simpa [lookup,equal] using ih tailUnique tailMember

theorem lookup_permutation (a b : Definitions) (ua : FunctionalNames a) (ub : FunctionalNames b)
    (permuted : a.Perm b) (key : String) : lookup a key = lookup b key := by
  cases ha : lookup a key with
  | some value => exact (lookup_of_mem b ub key value (permuted.mem_iff.mp (lookup_some_mem a key value ha))).symm
  | none =>
      cases hb : lookup b key with
      | none => rfl
      | some value =>
          have contradiction := lookup_of_mem a ua key value (permuted.mem_iff.mpr (lookup_some_mem b key value hb))
          simp [ha] at contradiction

def traverse {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | head::tail => match f head,traverse f tail with
      | some value,some values => some (value::values)
      | _,_ => none

/-- Named bodies consume one unit of expansion depth, just as constructor nodes do. -/
def resolve : Nat → Env → Expr → Option Code
  | 0,_,_ => none
  | fuel+1,env,expression => match expression with
      | .leaf contract => if contract.valid then some (.leaf contract) else none
      | .ref name => do
          let body ← env name
          let code ← resolve fuel env body
          return .named name code
      | .all children => do
          if children.length < 2 then none else do
            let codes ← traverse (resolve fuel env) children
            if (Code.all codes).reps = [] then none else some (.all codes)
      | .any children => do
          if children.length < 2 then none else do
            let codes ← traverse (resolve fuel env) children
            return .any codes

inductive Links {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Links R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Links R as bs → Links R (a::as) (b::bs)

theorem Links.imp {α β : Type} {R S : α → β → Prop} (convert : ∀ a b, R a b → S a b)
    {xs : List α} {ys : List β} (h : Links R xs ys) : Links S xs ys := by
  induction h with
  | nil => exact .nil
  | cons first rest ih => exact .cons (convert _ _ first) ih

theorem Links.congr {α β : Type} {R S : α → β → Prop} (convert : ∀ a b, R a b ↔ S a b)
    (xs : List α) (ys : List β) : Links R xs ys ↔ Links S xs ys :=
  ⟨Links.imp (fun a b => (convert a b).mp),Links.imp (fun a b => (convert a b).mpr)⟩

theorem traverse_links {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    traverse f xs = some ys ↔ Links (fun a b => f a = some b) xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
      | cons head tail => constructor <;> intro h <;> cases h
  | cons head tail ih =>
      cases hf : f head with
      | none =>
          simp only [traverse,hf]
          constructor
          · intro h; cases h
          · intro h; cases h with | cons first _ => simp [hf] at first
      | some value =>
          cases ht : traverse f tail with
          | none =>
              simp only [traverse,hf,ht]
              constructor
              · intro h; cases h
              · intro h; cases h with | cons _ rest => have := (ih _).mpr rest; simp [ht] at this
          | some values =>
              simp only [traverse,hf,ht]
              constructor
              · intro h; cases h; exact .cons hf ((ih _).mp ht)
              · intro h; cases h with
                | cons first rest =>
                    have firstEq := Option.some.inj (hf.symm.trans first)
                    have restEq := Option.some.inj (ht.symm.trans ((ih _).mpr rest))
                    simp [firstEq,restEq]

/-- A depth-indexed finite-expansion judgment. Its constructors require actual
name lookup and valid leaf/arity/carrier conditions, never a resolver verdict. -/
def Expansion : Nat → Env → Expr → Code → Prop
  | 0,_,_,_ => False
  | fuel+1,env,expression,code => match expression with
      | .leaf contract => contract.valid = true ∧ code = .leaf contract
      | .ref name => ∃ body child, env name = some body ∧ Expansion fuel env body child ∧ code = .named name child
      | .all children => ∃ codes, 2 ≤ children.length ∧ (Code.all codes).reps ≠ [] ∧
          Links (Expansion fuel env) children codes ∧ code = .all codes
      | .any children => ∃ codes, 2 ≤ children.length ∧ Links (Expansion fuel env) children codes ∧ code = .any codes

/-- Completeness includes real successful expansion, excluding vacuous reject-all implementations. -/
theorem resolve_iff_expansion (fuel : Nat) (env : Env) (expression : Expr) (code : Code) :
    resolve fuel env expression = some code ↔ Expansion fuel env expression code := by
  induction fuel generalizing expression code with
  | zero => simp [resolve,Expansion]
  | succ fuel ih =>
      have lists : ∀ xs cs, traverse (resolve fuel env) xs = some cs ↔ Links (Expansion fuel env) xs cs := by
        intro xs cs
        rw [traverse_links]
        exact Links.congr ih xs cs
      cases expression with
      | leaf contract => by_cases valid : contract.valid = true <;> simp [resolve,Expansion,valid,eq_comm]
      | ref name =>
          cases found : env name with
          | none => simp [resolve,Expansion,found]
          | some body =>
              cases checked : resolve fuel env body with
              | none => simp [resolve,Expansion,found,← ih,checked]
              | some child => simp [resolve,Expansion,found,← ih,checked,eq_comm]
      | all children =>
          by_cases arity : children.length < 2
          · simp [resolve,Expansion,arity,Nat.not_le.mpr arity]
          · cases mapped : traverse (resolve fuel env) children with
            | none =>
                have impossible : ∀ cs, ¬ Links (Expansion fuel env) children cs := by
                  intro cs h; have := (lists children cs).mpr h; simp [mapped] at this
                simp [resolve,Expansion,arity,mapped,impossible]
            | some codes =>
                have fixed : ∀ cs, Links (Expansion fuel env) children cs ↔ codes = cs := by
                  intro cs; rw [← lists,mapped,Option.some.injEq]
                by_cases carrier : (Code.all codes).reps = []
                · simp [resolve,Expansion,arity,carrier,mapped,fixed]
                  intro _ xs live same
                  subst xs
                  exact False.elim (live carrier)
                · simp [resolve,Expansion,arity,carrier,mapped,fixed,Nat.le_of_not_lt arity]
                  constructor
                  · intro h; exact ⟨codes,carrier,rfl,h.symm⟩
                  · rintro ⟨xs,_,same,h⟩; subst xs; exact h.symm
      | any children =>
          by_cases arity : children.length < 2
          · simp [resolve,Expansion,arity,Nat.not_le.mpr arity]
          · cases mapped : traverse (resolve fuel env) children with
            | none =>
                have impossible : ∀ cs, ¬ Links (Expansion fuel env) children cs := by
                  intro cs h; have := (lists children cs).mpr h; simp [mapped] at this
                simp [resolve,Expansion,arity,mapped,impossible]
            | some codes =>
                have fixed : ∀ cs, Links (Expansion fuel env) children cs ↔ codes = cs := by
                  intro cs; rw [← lists,mapped,Option.some.injEq]
                simp [resolve,Expansion,arity,mapped,fixed,Nat.le_of_not_lt arity]
                exact eq_comm

theorem resolve_permutation (a b : Definitions) (ua : FunctionalNames a) (ub : FunctionalNames b)
    (permuted : a.Perm b) (fuel : Nat) (expression : Expr) :
    resolve fuel (lookup a) expression = resolve fuel (lookup b) expression := by
  have environments : lookup a = lookup b := funext (lookup_permutation a b ua ub permuted)
  rw [environments]

theorem unknown_rejected (env : Env) (name : String) (missing : env name = none) (fuel : Nat) :
    resolve fuel env (.ref name) = none := by cases fuel <;> simp [resolve,missing]

theorem builtin_resolves (env : Env) (builtin : Builtin) :
    resolve 1 env (.leaf (.builtin builtin)) = some (.leaf (.builtin builtin)) := by simp [resolve,Leaf.valid]




theorem Links.all_iff {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop}
    {xs : List α} {ys : List β} (h : Links R xs ys) (agree : ∀ a b, R a b → (P a ↔ Q b)) :
    (∀ a ∈ xs, P a) ↔ ∀ b ∈ ys, Q b := by
  induction h with
  | nil => simp
  | cons first rest ih => simpa using and_congr (agree _ _ first) ih

theorem Links.any_iff {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop}
    {xs : List α} {ys : List β} (h : Links R xs ys) (agree : ∀ a b, R a b → (P a ↔ Q b)) :
    (∃ a ∈ xs, P a) ↔ ∃ b ∈ ys, Q b := by
  induction h with
  | nil => simp
  | cons first rest ih => simpa using or_congr (agree _ _ first) ih

/-- Source meaning follows actual environment lookup, not compiled code. -/
noncomputable def SourceDenotes (language : String → String → Prop) : Nat → Env → Expr → Value → Prop
  | 0,_,_,_ => False
  | fuel+1,env,expression,value => match expression with
      | .leaf contract => contract.Denotes language value
      | .ref name => ∃ body, env name = some body ∧ SourceDenotes language fuel env body value
      | .all children => ∀ child ∈ children, SourceDenotes language fuel env child value
      | .any children => ∃ child ∈ children, SourceDenotes language fuel env child value

theorem resolution_semantics (language : String → String → Prop) (fuel : Nat) (env : Env)
    (expression : Expr) (code : Code) (value : Value) (resolved : resolve fuel env expression = some code) :
    SourceDenotes language fuel env expression value ↔ code.Denotes language value := by
  induction fuel generalizing expression code with
  | zero => simp [resolve] at resolved
  | succ fuel ih =>
      have expansion := (resolve_iff_expansion _ _ _ _).mp resolved
      cases expression with
      | leaf contract =>
          obtain ⟨_,rfl⟩ := expansion
          simp [SourceDenotes,Code.Denotes,Code.fold]
      | ref name =>
          obtain ⟨body,child,found,childExpansion,rfl⟩ := expansion
          have childResolved := (resolve_iff_expansion _ _ _ _).mpr childExpansion
          simpa [SourceDenotes,found,Code.Denotes,Code.fold] using ih body child childResolved
      | all children =>
          obtain ⟨codes,_,_,related,rfl⟩ := expansion
          simp only [SourceDenotes,Code.denotes_all]
          exact related.all_iff (fun a b h => ih a b ((resolve_iff_expansion _ _ _ _).mpr h))
      | any children =>
          obtain ⟨codes,_,related,rfl⟩ := expansion
          simp only [SourceDenotes,Code.denotes_any]
          exact related.any_iff (fun a b h => ih a b ((resolve_iff_expansion _ _ _ _).mpr h))

/-- Dependency expansion includes both named lookup and structural child edges. -/
inductive Step (env : Env) : Expr → Expr → Prop where
  | reference {name : String} {body : Expr} : env name = some body → Step env (.ref name) body
  | allChild {children : List Expr} {child : Expr} : child ∈ children → Step env (.all children) child
  | anyChild {children : List Expr} {child : Expr} : child ∈ children → Step env (.any children) child

inductive Path (env : Env) : Expr → Expr → Prop where
  | single {a b : Expr} : Step env a b → Path env a b
  | cons {a b c : Expr} : Step env a b → Path env b c → Path env a c

def Safe : Nat → Env → Expr → Prop
  | 0,_,_ => False
  | fuel+1,env,expression => match expression with
      | .leaf _ => True
      | .ref name => ∃ body, env name = some body ∧ Safe fuel env body
      | .all children | .any children => ∀ child ∈ children, Safe fuel env child

theorem expansion_safe (fuel : Nat) (env : Env) (expression : Expr) (code : Code)
    (h : Expansion fuel env expression code) : Safe fuel env expression := by
  induction fuel generalizing expression code with
  | zero => exact False.elim h
  | succ fuel ih =>
      cases expression with
      | leaf contract => trivial
      | ref name => obtain ⟨body,child,found,good,_⟩ := h; exact ⟨body,found,ih _ _ good⟩
      | all children =>
          obtain ⟨codes,_,_,related,_⟩ := h
          have good : ∀ c ∈ codes, True := by simp
          exact (related.all_iff (fun a b rel => ⟨fun _ => trivial,fun _ => ih a b rel⟩)).mpr good
      | any children =>
          obtain ⟨codes,_,related,_⟩ := h
          have good : ∀ c ∈ codes, True := by simp
          exact (related.all_iff (fun a b rel => ⟨fun _ => trivial,fun _ => ih a b rel⟩)).mpr good

theorem safe_step (env : Env) {fuel : Nat} {a b : Expr} (safe : Safe fuel env a)
    (step : Step env a b) : ∃ smaller < fuel, Safe smaller env b := by
  cases fuel with
  | zero => exact False.elim safe
  | succ fuel =>
      cases step with
      | reference found =>
          obtain ⟨body,lookupBody,good⟩ := safe
          have same := Option.some.inj (lookupBody.symm.trans found)
          subst body
          exact ⟨fuel,Nat.lt_succ_self fuel,good⟩
      | allChild member => exact ⟨fuel,Nat.lt_succ_self fuel,safe _ member⟩
      | anyChild member => exact ⟨fuel,Nat.lt_succ_self fuel,safe _ member⟩

theorem safe_path (env : Env) {a b : Expr} (path : Path env a b) {fuel : Nat}
    (safe : Safe fuel env a) : ∃ smaller < fuel, Safe smaller env b := by
  induction path generalizing fuel with
  | single step => exact safe_step env safe step
  | cons step rest ih =>
      obtain ⟨middle,less,safeMiddle⟩ := safe_step env safe step
      obtain ⟨smaller,lessAgain,safeEnd⟩ := ih safeMiddle
      exact ⟨smaller,Nat.lt_trans lessAgain less,safeEnd⟩

theorem safe_no_cycle (env : Env) (expression : Expr) (fuel : Nat)
    (safe : Safe fuel env expression) : ¬ Path env expression expression := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro loop
      obtain ⟨smaller,less,stillSafe⟩ := safe_path env loop safe
      exact ih smaller less stillSafe loop

/-- A successful resolver cannot hide a cycle behind an accepting union branch. -/
theorem resolved_no_cycle (fuel : Nat) (env : Env) (expression : Expr) (code : Code)
    (resolved : resolve fuel env expression = some code) : ¬Path env expression expression :=
  safe_no_cycle env expression fuel (expansion_safe _ _ _ _ ((resolve_iff_expansion _ _ _ _).mp resolved))

/-- Every reachable descendant is acyclic, including unchosen union branches. -/
theorem resolved_descendant_no_cycle (fuel : Nat) (env : Env) (root child : Expr) (code : Code)
    (resolved : resolve fuel env root = some code) (reachable : Path env root child) :
    ¬ Path env child child := by
  have safe := expansion_safe _ _ _ _ ((resolve_iff_expansion _ _ _ _).mp resolved)
  obtain ⟨smaller,_,childSafe⟩ := safe_path env reachable safe
  exact safe_no_cycle env child smaller childSafe

/-- Installation checks every declaration, including unreachable bodies. -/
def installable (fuel : Nat) (definitions : Definitions) : Prop :=
  ∀ declaration ∈ definitions, (resolve fuel (lookup definitions) declaration.2).isSome = true

instance (fuel : Nat) (definitions : Definitions) : Decidable (installable fuel definitions) := by
  unfold installable; infer_instance

def install (fuel : Nat) (definitions : Definitions) (root : Expr) : Option Code :=
  if decide (installable fuel definitions) then resolve (fuel+1) (lookup definitions) root else none

theorem installed_definitions_resolve (fuel : Nat) (definitions : Definitions) (root : Expr) (code : Code)
    (installed : install fuel definitions root = some code) : installable fuel definitions := by
  unfold install at installed
  split at installed
  · simpa using ‹decide (installable fuel definitions) = true›
  · contradiction

theorem unused_cycle_rejected (fuel : Nat) (definitions : Definitions) (root : Expr)
    (name : String) (body : Expr) (member : (name,body) ∈ definitions)
    (cycle : Path (lookup definitions) body body) : install fuel definitions root = none := by
  unfold install
  have bad : ¬ installable fuel definitions := by
    intro allGood
    have present := allGood (name,body) member
    cases h : resolve fuel (lookup definitions) body with
    | none => simp [h] at present
    | some code => exact resolved_no_cycle _ _ _ _ h cycle
  simp [bad]

end CBCL.FlatContracts
