import Batteries.Data.List.Perm
import Batteries.Data.List.Lemmas

/-!
# SPEC-019 State Layer — R7 (REQ-1930)

Model of the state layer of `specs/SPEC-019-state-rules.md`: accepted acts,
the kernel of two selections (`acts`, `current`) and reductions (`pick`,
`size`, `has`, `sumField`), the author-facing rules as sugar over the
kernel, and the intent binder.

## Model

The accepted set of a thread is represented as a `List Act`. The store
that produces it is a G-set keyed by content address, so the invariant
`NodupAddr` (no two acts share an address) is the store's, not an
assumption about the network. "Same accepted set" is set-extensional
equality `SetEq`. Addresses are `Nat`: an injective, order-preserving
image of the 64-hex address, which is all the order-by-address rule uses.
Collection-valued outputs (sets, maps) are modelled as characteristic
functions, so they are set functions by construction; the renderer's
sorting is the implementation's concern (SPEC-019 R.3).

Mirrors `crates/cbcl-core/src/state.rs` and `intend.rs`. The Rust/Lean
correspondence is checked by the conformance corpus
(`test-vectors/state/`), not proved here.

## Theorems (SPEC-019 REQ-1930, in the order listed there)

* `fold_perm_invariant` / `fold_dedup_invariant` — R7: every rule is a
  function of the accepted set: invariant under permutation
  (`SetEq`) and under duplicate delivery (the store's `insert`);
  `histogramPerKey_setEq` and `actsDom_setEq` are the per-key histogram
  and the domain filter, folded into the conjunction.
* `actsDom_excluded` / `excluded_not_mem` — a domain is a fold filter
  (ADR-1909): an act outside the opener's list is accepted and
  contributes to no rule.
* `acts_mono`, `size_mono`, `has_mono`, `exists_mono` — monotone rules.
* `mem_current_iff`, `replaced_never_current`, `unnamed_is_current` —
  the register characterisation (a replaced write never wins; an
  unnamed write is always current, add-wins).
* `sumField_insert` — `sum` and `counter` contribute once per address.
* `intend_pred_valid`, `intend_replaces_current`, `intend_supersedes`,
  `intend_current_after` — binder soundness: the predecessor is an
  accepted act of an admitted type; `:replaces` names exactly the
  current writes for the key; after acceptance those writes are no
  longer current and the new act is.
-/

namespace CBCL
namespace State

/-- A scalar: the element type of a scalar list (SPEC-019 R.3). -/
inductive Scalar where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr

/-- A state-bearing field value (SPEC-019 R.3): a scalar, or a scalar list
such as the opener's `:options`, over which a `domain` entry filters. -/
inductive Val where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  | list (xs : List Scalar)
  deriving DecidableEq, Repr

/-- A scalar as a field value, for membership of a key in a scalar list. -/
def Scalar.toVal : Scalar → Val
  | .str s => .str s
  | .int n => .int n
  | .bool b => .bool b

/-- An accepted act as the fold sees it (SPEC-019 Reference, "act"). -/
structure Act where
  /-- Content address, as an order-preserving image of the 64-hex form. -/
  addr : Nat
  /-- The performative the act performs. -/
  verb : String
  /-- The authenticated signer. -/
  signer : String
  /-- The addresses of the act's causal predecessors (`:caused-by`). -/
  preds : List Nat
  /-- The keyword fields, in order. -/
  fields : List (String × Val)
  /-- The reserved bookkeeping field (SPEC-019 ADR-1901). -/
  replaces : List Nat
  deriving DecidableEq

/-- The value of a keyword field. -/
def Act.get (a : Act) (k : String) : Option Val := List.lookup k a.fields

/-- Set-extensional equality of accepted lists. -/
def SetEq (A B : List Act) : Prop := ∀ a, a ∈ A ↔ a ∈ B

/-- The store invariant: no two accepted acts share an address. -/
def NodupAddr (A : List Act) : Prop := (A.map Act.addr).Nodup

theorem SetEq.refl (A : List Act) : SetEq A A := fun _ => Iff.rfl

theorem SetEq.symm {A B : List Act} (h : SetEq A B) : SetEq B A := fun a => (h a).symm

theorem SetEq.of_perm {A B : List Act} (h : A.Perm B) : SetEq A B := fun _ => h.mem_iff

/-- Duplicate delivery changes nothing set-extensionally. -/
theorem SetEq.append_self (A : List Act) : SetEq (A ++ A) A := fun _ => by
  simp only [List.mem_append, or_self]

/-- Emptiness is determined by membership. -/
theorem isEmpty_setEq {T U : List Act} (h : SetEq T U) : T.isEmpty = U.isEmpty := by
  cases T with
  | nil =>
    cases U with
    | nil => rfl
    | cons u _ => exact absurd ((h u).2 List.mem_cons_self) List.not_mem_nil
  | cons t _ =>
    cases U with
    | nil => exact absurd ((h t).1 List.mem_cons_self) List.not_mem_nil
    | cons _ _ => rfl

/-- Filtering respects set-extensional equality. -/
theorem SetEq.filter {A B : List Act} (h : SetEq A B) (p : Act → Bool) :
    SetEq (A.filter p) (B.filter p) := by
  intro a; simp only [List.mem_filter]; rw [h a]

/-- `any` is determined by membership. -/
theorem any_setEq {A B : List Act} (h : SetEq A B) (p : Act → Bool) : A.any p = B.any p := by
  cases hA : A.any p <;> cases hB : B.any p <;> simp only [List.any_eq_true, List.any_eq_false] at hA hB
  · rfl
  · obtain ⟨x, hx, hp⟩ := hB; exact absurd hp (hA x ((h x).2 hx))
  · obtain ⟨x, hx, hp⟩ := hA; exact absurd hp (hB x ((h x).1 hx))
  · rfl

/-- `all` is determined by membership. -/
theorem all_setEq {A B : List Act} (h : SetEq A B) (p : Act → Bool) : A.all p = B.all p := by
  cases hA : A.all p <;> cases hB : B.all p <;> simp only [List.all_eq_true, List.all_eq_false] at hA hB
  · rfl
  · obtain ⟨x, hx, hp⟩ := hA; exact absurd (hB x ((h x).1 hx)) hp
  · obtain ⟨x, hx, hp⟩ := hB; exact absurd (hA x ((h x).2 hx)) hp
  · rfl

theorem NodupAddr.sublist {A B : List Act} (s : A.Sublist B) (h : NodupAddr B) : NodupAddr A :=
  List.Nodup.sublist (s.map Act.addr) h

theorem NodupAddr.filter {A : List Act} (h : NodupAddr A) (p : Act → Bool) :
    NodupAddr (A.filter p) :=
  h.sublist List.filter_sublist



/-- Distinct acts of a `NodupAddr` list have distinct addresses. -/
theorem NodupAddr.eq_of_addr {A : List Act} (h : NodupAddr A) {a b : Act} (ha : a ∈ A) (hb : b ∈ A)
    (e : a.addr = b.addr) : a = b := by
  induction A with
  | nil => simp at ha
  | cons t rest ih =>
    simp only [NodupAddr, List.map_cons, List.nodup_cons, List.mem_map] at h
    obtain ⟨hnot, hrest⟩ := h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, e.symm⟩ hnot
    · exact absurd ⟨a, ha, e⟩ hnot
    · exact ih hrest ha hb

/-- A `NodupAddr` list has no duplicate acts. -/
theorem NodupAddr.nodup {A : List Act} (h : NodupAddr A) : A.Nodup := by
  induction A with
  | nil => exact List.nodup_nil
  | cons t rest ih =>
    simp only [NodupAddr, List.map_cons, List.nodup_cons, List.mem_map] at h
    obtain ⟨hnot, hrest⟩ := h
    exact List.nodup_cons.2 ⟨fun hm => hnot ⟨t, hm, rfl⟩, ih hrest⟩

/-- Two `NodupAddr` lists with the same members are permutations. -/
theorem perm_of_setEq {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B) :
    A.Perm B :=
  (List.perm_ext_iff_of_nodup hA.nodup hB.nodup).2 h

/-! ## The kernel (SPEC-019 R.2) -/

/-- `acts v`: the accepted acts of a verb. Under a `domain` entry the
rules over `v` read `actsDom` instead, a further filter of this list. -/
def acts (v : String) (A : List Act) : List Act := A.filter (fun a => a.verb == v)

/-- The key of a write: the value of the key field, or a constant when unkeyed. -/
def keyOf (k : Option String) (a : Act) : Option Val :=
  match k with
  | none => none
  | some k => a.get k

/-- The acts whose `:replaces` can retire a write of `v`: writes of `v` and,
when a delete verb is declared, its acts. -/
def replacers (v : String) (d : Option String) (A : List Act) : List Act :=
  acts v A ++ (match d with | none => [] | some d => acts d A)

/-- Whether some replacer of the same key names `w` in `:replaces`. -/
def isReplaced (v : String) (k d : Option String) (A : List Act) (w : Act) : Bool :=
  (replacers v d A).any (fun r => decide (keyOf k r = keyOf k w) && r.replaces.contains w.addr)

/-- `current v kk d`: the writes of `v` no replacer of the same key names. -/
def current (v : String) (k d : Option String) (A : List Act) : List Act :=
  (acts v A).filter (fun w => !isReplaced v k d A w)

theorem NodupAddr.acts {A : List Act} (h : NodupAddr A) (v : String) : NodupAddr (acts v A) :=
  h.filter _

theorem NodupAddr.current {A : List Act} (h : NodupAddr A) (v : String) (k d : Option String) :
    NodupAddr (current v k d A) :=
  (h.acts v).filter _

/-- Whether `a` has the greatest address in `T`. -/
def isTop (T : List Act) (a : Act) : Bool := T.all (fun b => decide (b.addr ≤ a.addr))

/-- `pick`: the act with the greatest address (SPEC-019 REQ-1916). -/
def pickAct (T : List Act) : Option Act := T.find? (isTop T)

/-- `pick T k`: the value of `k` on the greatest-address act. -/
def pick (k : String) (T : List Act) : Option Val := (pickAct T).bind (fun a => a.get k)

/-- `size T`. -/
def size (T : List Act) : Nat := T.length

/-- `distinct T k` as a characteristic function: whether some act of `T` has value `x` at `k`. -/
def has (k : String) (T : List Act) (x : Val) : Bool := T.any (fun a => a.get k == some x)

/-- The integer amount an act contributes at `k` (0 when absent or not a number). -/
def amount (k : String) (a : Act) : Int :=
  match a.get k with
  | some (Val.int n) => n
  | _ => 0

/-- `sum T k`: exact integer total. -/
def sumField (k : String) (T : List Act) : Int := T.foldl (fun acc a => acc + amount k a) 0

/-! ## Sugar (the author-facing rules, SPEC-019 R.2 table) -/

/-- `last v :k`: one value across everyone, chosen by greatest address (SPEC-019 R.2). -/
def last (v k : String) (A : List Act) : Option Val := pick k (acts v A)

/-- `latest-per-signer v :k`: the signer `s`'s own latest value. -/
def latestPerSigner (v k : String) (A : List Act) (s : String) : Option Val :=
  pick k ((acts v A).filter (fun a => a.signer == s))

/-- `latest-per-key v :kk :k`: the latest value under key `x`, by address. -/
def latestPerKey (v kk k : String) (A : List Act) (x : Val) : Option Val :=
  pick k ((acts v A).filter (fun a => a.get kk == some x))

/-- `exists v`: whether any accepted act of `v` exists. -/
def existsRule (v : String) (A : List Act) : Bool := !(acts v A).isEmpty

/-- `count v`: the number of distinct accepted acts of `v`. -/
def count (v : String) (A : List Act) : Nat := size (acts v A)

/-- `set-union v :k`: membership in the union of every `k` value; additions only. -/
def setUnion (v k : String) (A : List Act) (x : Val) : Bool := has k (acts v A) x

/-- `values v :k`: membership in the multi-value register (values no later write replaced). -/
def values (v k : String) (A : List Act) (x : Val) : Bool := has k (current v none none A) x

/-- `values-per-key v :kk :k [d]`: membership in the register under key `x`, every current value kept. -/
def valuesPerKey (v kk k : String) (d : Option String) (A : List Act) (x y : Val) : Bool :=
  has k ((current v (some kk) d A).filter (fun a => a.get kk == some x)) y

/-- `register-per-key v :kk :k [d]`: the one current value under key `x`, by address. -/
def registerPerKey (v kk k : String) (d : Option String) (A : List Act) (x : Val) : Option Val :=
  pick k ((current v (some kk) d A).filter (fun a => a.get kk == some x))

/-- `observed-set` is `current` keyed by the value with the remove verb as the delete verb
(SPEC-019 ADR-1900). -/
def observedSet (add rem k : String) (A : List Act) (x : Val) : Bool :=
  has k (current add (some k) (some rem) A) x

/-- `counter inc dec :k`: increments minus decrements. -/
def counter (inc dec k : String) (A : List Act) : Int :=
  sumField k (acts inc A) - sumField k (acts dec A)

/-- `histogram` over `latest-per-signer`: the number of signers whose latest value is `x`,
counted as the acts that top their own signer's group. -/
def histogramPerSigner (v k : String) (A : List Act) (x : Val) : Nat :=
  ((acts v A).filter (fun a =>
      isTop ((acts v A).filter (fun b => b.signer == a.signer)) a && a.get k == some x)).length

/-- `histogram` over `latest-per-key`: the number of keys whose latest value is `x`,
counted as the acts that top their own key's group. An act without the key
field belongs to no group, as the implementation's `group_by_key` drops it. -/
def histogramPerKey (v kk k : String) (A : List Act) (x : Val) : Nat :=
  ((acts v A).filter (fun a =>
      (a.get kk).isSome && isTop ((acts v A).filter (fun b => b.get kk == a.get kk)) a
        && a.get k == some x)).length

/-! ## Domains (SPEC-019 R.2 `domain`, ADR-1909) -/

/-- The list a `(domain v k F)` entry reads: the opener's `F`, a scalar list
selected by `last ov F`, or nothing. -/
def allowedOf (ov F : String) (A : List Act) : List Val :=
  match last ov F A with
  | some (Val.list xs) => xs.map Scalar.toVal
  | _ => []

/-- Whether an act's `k` is an element of the allowed list. An act without
the field is outside every domain. -/
def inDomain (k : String) (allowed : List Val) (a : Act) : Bool :=
  match a.get k with
  | some x => allowed.contains x
  | none => false

/-- `acts v` under `(domain v k F)`: the acts of `v` whose `k` is in the
opener's `F`. Every rule over `v` reads this list in place of `acts v`
(R.2); the excluded act stays accepted and contributes nothing. -/
def actsDom (v k ov F : String) (A : List Act) : List Act :=
  (acts v A).filter (inDomain k (allowedOf ov F A))

theorem NodupAddr.actsDom {A : List Act} (h : NodupAddr A) (v k ov F : String) :
    NodupAddr (actsDom v k ov F A) :=
  (h.acts v).filter _

/-! ## R7: every rule is a set function (REQ-1915) -/

theorem acts_setEq {A B : List Act} (h : SetEq A B) (v : String) : SetEq (acts v A) (acts v B) :=
  h.filter _

theorem replacers_setEq {A B : List Act} (h : SetEq A B) (v : String) (d : Option String) :
    SetEq (replacers v d A) (replacers v d B) := by
  intro a
  have h1 := (acts_setEq h v) a
  cases d with
  | none =>
    simp only [replacers, List.mem_append, List.not_mem_nil, or_false]
    exact h1
  | some d =>
    have h2 := (acts_setEq h d) a
    simp only [replacers, List.mem_append]
    rw [h1, h2]

theorem isReplaced_setEq {A B : List Act} (h : SetEq A B) (v : String) (k d : Option String)
    (w : Act) : isReplaced v k d A w = isReplaced v k d B w :=
  any_setEq (replacers_setEq h v d) _

theorem current_setEq {A B : List Act} (h : SetEq A B) (v : String) (k d : Option String) :
    SetEq (current v k d A) (current v k d B) := by
  intro a
  simp only [current, List.mem_filter, isReplaced_setEq h]
  rw [(acts_setEq h v) a]

theorem has_setEq {T U : List Act} (h : SetEq T U) (k : String) (x : Val) : has k T x = has k U x :=
  any_setEq h _

theorem isTop_setEq {T U : List Act} (h : SetEq T U) (a : Act) : isTop T a = isTop U a :=
  all_setEq h _

/-- The specification of `pickAct`: a member every address is at most. -/
theorem pickAct_spec {T : List Act} {a : Act} (h : pickAct T = some a) :
    a ∈ T ∧ ∀ b ∈ T, b.addr ≤ a.addr := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa [isTop, List.all_eq_true] using this

/-- A non-empty list has a top. -/
theorem exists_top {T : List Act} (hne : T ≠ []) : ∃ a ∈ T, ∀ b ∈ T, b.addr ≤ a.addr := by
  induction T with
  | nil => exact absurd rfl hne
  | cons t rest ih =>
    by_cases hr : rest = []
    · subst hr; exact ⟨t, List.mem_cons_self, fun b hb => by simp at hb; subst hb; exact Nat.le_refl _⟩
    · obtain ⟨m, hm, hmax⟩ := ih hr
      by_cases hle : t.addr ≤ m.addr
      · refine ⟨m, List.mem_cons_of_mem _ hm, fun b hb => ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · exact hle
        · exact hmax b hb
      · refine ⟨t, List.mem_cons_self, fun b hb => ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax b hb) (Nat.le_of_lt (Nat.lt_of_not_le hle))

theorem pickAct_eq_none_iff {T : List Act} : pickAct T = none ↔ T = [] := by
  constructor
  · intro h
    cases T with
    | nil => rfl
    | cons t rest =>
      exfalso
      obtain ⟨a, ha, hmax⟩ := exists_top (T := t :: rest) (List.cons_ne_nil t rest)
      have := (List.find?_eq_none.1 h) a ha
      exact this (by simpa [isTop, List.all_eq_true] using hmax)
  · rintro rfl; rfl

/-- `pick` is a set function on `NodupAddr` lists (REQ-1916). -/
theorem pickAct_setEq {T U : List Act} (hT : NodupAddr T) (hU : NodupAddr U) (h : SetEq T U) :
    pickAct T = pickAct U := by
  cases hpT : pickAct T with
  | none =>
    have : T = [] := pickAct_eq_none_iff.1 hpT
    subst this
    have : U = [] := by
      cases U with
      | nil => rfl
      | cons u rest => exact absurd ((h u).2 List.mem_cons_self) (List.not_mem_nil)
    subst this; rfl
  | some a =>
    obtain ⟨haT, hmaxT⟩ := pickAct_spec hpT
    cases hpU : pickAct U with
    | none =>
      have : U = [] := pickAct_eq_none_iff.1 hpU
      subst this; exact absurd ((h a).1 haT) List.not_mem_nil
    | some b =>
      obtain ⟨hbU, hmaxU⟩ := pickAct_spec hpU
      have hbT : b ∈ T := (h b).2 hbU
      have haU : a ∈ U := (h a).1 haT
      have e : a.addr = b.addr := Nat.le_antisymm (hmaxU a haU) (hmaxT b hbT)
      rw [hT.eq_of_addr haT hbT e]

theorem pick_setEq {T U : List Act} (hT : NodupAddr T) (hU : NodupAddr U) (h : SetEq T U)
    (k : String) : pick k T = pick k U := by
  simp only [pick, pickAct_setEq hT hU h]

theorem size_setEq {T U : List Act} (hT : NodupAddr T) (hU : NodupAddr U) (h : SetEq T U) :
    size T = size U :=
  (perm_of_setEq hT hU h).length_eq

theorem sumField_setEq {T U : List Act} (hT : NodupAddr T) (hU : NodupAddr U) (h : SetEq T U)
    (k : String) : sumField k T = sumField k U :=
  (perm_of_setEq hT hU h).foldl_eq' (fun _ _ _ _ z => by simp only [Int.add_right_comm]) 0

/-- `histogram` over `latest-per-key` is a set function (`histogramPerKey_setEq`). -/
theorem histogramPerKey_setEq {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v kk k : String) (x : Val) :
    histogramPerKey v kk k A x = histogramPerKey v kk k B x := by
  have hav : SetEq (acts v A) (acts v B) := acts_setEq h v
  have nA : NodupAddr (acts v A) := hA.filter _
  have nB : NodupAddr (acts v B) := hB.filter _
  apply size_setEq (nA.filter _) (nB.filter _)
  intro a
  simp only [List.mem_filter]
  rw [hav a, isTop_setEq (hav.filter (fun b => b.get kk == a.get kk)) a]

/-- The domain list is a set function: it is a `last` over the opener. -/
theorem allowedOf_setEq {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B)
    (ov F : String) : allowedOf ov F A = allowedOf ov F B := by
  simp only [allowedOf, last, pick_setEq (hA.acts ov) (hB.acts ov) (acts_setEq h ov) F]

/-- **Domains are fold filters** (ADR-1909, `actsDom_setEq`): the filtered
`acts` is a set function of the accepted acts, so every rule over it is. -/
theorem actsDom_setEq {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B)
    (v k ov F : String) : SetEq (actsDom v k ov F A) (actsDom v k ov F B) := by
  simp only [actsDom, allowedOf_setEq hA hB h ov F]
  exact (acts_setEq h v).filter _

/-- **R7, permutation invariance** (REQ-1915, `fold_perm_invariant`): every
rule of the sugar table is a set function of the accepted acts. Stated
per rule; the fold is their tuple. -/
theorem fold_perm_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v kk k add rem inc dec ov F : String) (d : Option String) (s : String)
    (x y : Val) :
    last v k A = last v k B ∧
    latestPerSigner v k A s = latestPerSigner v k B s ∧
    latestPerKey v kk k A x = latestPerKey v kk k B x ∧
    existsRule v A = existsRule v B ∧
    count v A = count v B ∧
    setUnion v k A x = setUnion v k B x ∧
    values v k A x = values v k B x ∧
    valuesPerKey v kk k d A x y = valuesPerKey v kk k d B x y ∧
    registerPerKey v kk k d A x = registerPerKey v kk k d B x ∧
    observedSet add rem k A x = observedSet add rem k B x ∧
    counter inc dec k A = counter inc dec k B ∧
    histogramPerSigner v k A x = histogramPerSigner v k B x ∧
    histogramPerKey v kk k A x = histogramPerKey v kk k B x ∧
    SetEq (actsDom v kk ov F A) (actsDom v kk ov F B) := by
  have hav : ∀ v, SetEq (acts v A) (acts v B) := fun v => acts_setEq h v
  have nA : ∀ v, NodupAddr (acts v A) := fun v => hA.filter _
  have nB : ∀ v, NodupAddr (acts v B) := fun v => hB.filter _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pick_setEq (nA v) (nB v) (hav v) k
  · exact pick_setEq ((nA v).filter _) ((nB v).filter _) ((hav v).filter _) k
  · exact pick_setEq ((nA v).filter _) ((nB v).filter _) ((hav v).filter _) k
  · simp only [existsRule, isEmpty_setEq (hav v)]
  · exact size_setEq (nA v) (nB v) (hav v)
  · exact has_setEq (hav v) k x
  · exact has_setEq (current_setEq h v none none) k x
  · exact has_setEq ((current_setEq h v (some kk) d).filter _) k y
  · exact pick_setEq ((hA.current v (some kk) d).filter _) ((hB.current v (some kk) d).filter _)
      ((current_setEq h v (some kk) d).filter _) k
  · exact has_setEq (current_setEq h add (some k) (some rem)) k x
  · simp only [counter, sumField_setEq (nA inc) (nB inc) (hav inc) k,
      sumField_setEq (nA dec) (nB dec) (hav dec) k]
  · apply size_setEq ((nA v).filter _) ((nB v).filter _)
    intro a
    simp only [List.mem_filter]
    rw [(hav v) a, isTop_setEq ((hav v).filter (fun b => b.signer == a.signer)) a]
  · exact histogramPerKey_setEq hA hB h v kk k x
  · exact actsDom_setEq hA hB h v kk ov F

/-- The store's insertion: a re-delivered act is the same act (REQ-1920). -/
def insertAct (a : Act) (A : List Act) : List Act := if a ∈ A then A else a :: A

theorem insertAct_setEq (a : Act) (A : List Act) : SetEq (insertAct a A) (a :: A) := by
  intro b; simp only [insertAct]; split
  · rename_i ha; simp only [List.mem_cons]
    exact ⟨fun hb => Or.inr hb, fun hb => hb.elim (fun e => e ▸ ha) id⟩
  · exact Iff.rfl

theorem NodupAddr.insertAct {A : List Act} (h : NodupAddr A) {a : Act}
    (fresh : ∀ b ∈ A, b.addr ≠ a.addr) : NodupAddr (insertAct a A) := by
  simp only [State.insertAct]; split
  · exact h
  · simp only [NodupAddr, List.map_cons, List.nodup_cons, List.mem_map]
    exact ⟨fun ⟨b, hb, e⟩ => fresh b hb e, h⟩

/-- **R7, duplicate insensitivity** (REQ-1915, `fold_dedup_invariant`):
inserting an already-accepted act changes no rule, since `insertAct`
leaves the list unchanged. -/
theorem fold_dedup_invariant {A : List Act} {a : Act} (ha : a ∈ A) : insertAct a A = A := by
  simp [insertAct, ha]

/-- **An excluded act contributes nothing** (ADR-1909, `actsDom_excluded`):
accepting an act of `v` whose `k` is outside the domain leaves the filtered
`acts` unchanged, so every rule over `v` is unchanged. `v` is not the opener
verb, which R7 forbids a domain to filter, so the domain list is unchanged
too. -/
theorem actsDom_excluded {A : List Act} {a : Act} {v k ov F : String}
    (hv : a.verb = v) (hne : v ≠ ov)
    (hout : inDomain k (allowedOf ov F A) a = false) :
    actsDom v k ov F (insertAct a A) = actsDom v k ov F A := by
  by_cases ha : a ∈ A
  · simp [insertAct, ha]
  · have hins : insertAct a A = a :: A := by simp [insertAct, ha]
    have hov : acts ov (a :: A) = acts ov A := by
      simp [acts, hv, hne]
    have hallowed : allowedOf ov F (a :: A) = allowedOf ov F A := by
      simp only [allowedOf, last, hov]
    have hacts : acts v (a :: A) = a :: acts v A := by
      simp [acts, hv]
    rw [hins, actsDom, hallowed, hacts]
    simp [actsDom, hout]

/-- An excluded act is in no rule's table. -/
theorem excluded_not_mem {A : List Act} {a : Act} {v k ov F : String}
    (hout : inDomain k (allowedOf ov F A) a = false) : a ∉ actsDom v k ov F A := by
  intro h
  have := (List.mem_filter.1 h).2
  rw [hout] at this
  exact Bool.false_ne_true this

/-! ## Monotone rules (REQ-1917, `acts_mono` etc.) -/

theorem acts_mono {A B : List Act} (s : A.Sublist B) (v : String) : (acts v A).Sublist (acts v B) :=
  s.filter _

theorem size_mono {A B : List Act} (s : A.Sublist B) : size A ≤ size B := s.length_le

theorem count_mono {A B : List Act} (s : A.Sublist B) (v : String) : count v A ≤ count v B :=
  (acts_mono s v).length_le

theorem has_mono {T U : List Act} (s : T.Sublist U) (k : String) (x : Val) (h : has k T x = true) :
    has k U x = true := by
  have ⟨a, ha, hp⟩ := List.any_eq_true.1 h
  exact List.any_eq_true.2 ⟨a, s.subset ha, hp⟩

theorem exists_mono {A B : List Act} (s : A.Sublist B) (v : String) (h : existsRule v A = true) :
    existsRule v B = true := by
  simp only [existsRule, Bool.not_eq_true'] at h ⊢
  cases hB : (acts v B).isEmpty with
  | false => rfl
  | true =>
    exfalso
    rw [List.isEmpty_iff] at hB
    have hs := acts_mono s v
    rw [hB] at hs
    rw [List.sublist_nil.1 hs] at h
    simp at h

theorem setUnion_mono {A B : List Act} (s : A.Sublist B) (v k : String) (x : Val)
    (h : setUnion v k A x = true) : setUnion v k B x = true :=
  has_mono (acts_mono s v) k x h

/-! ## Registers (REQ-1917, `mem_current_iff`, `replaced_never_picked`) -/

/-- Membership in `current`: an accepted write of `v` that no replacer of its
key names. -/
theorem mem_current_iff {v : String} {k d : Option String} {A : List Act} {w : Act} :
    w ∈ current v k d A ↔
      w ∈ acts v A ∧ ∀ r ∈ replacers v d A, keyOf k r = keyOf k w → w.addr ∉ r.replaces := by
  simp only [current, List.mem_filter, isReplaced, Bool.not_eq_true', List.any_eq_false,
    Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, not_and]

/-- A write some replacer of its key names is never current, so no register
ever reads it (`replaced_never_picked`). -/
theorem replaced_never_current {v : String} {k d : Option String} {A : List Act} {w r : Act}
    (hr : r ∈ replacers v d A) (e : keyOf k r = keyOf k w) (hm : w.addr ∈ r.replaces) :
    w ∉ current v k d A := by
  intro hw
  exact (mem_current_iff.1 hw).2 r hr e hm

/-- A write nobody names is current whatever else is accepted (add-wins). -/
theorem unnamed_is_current {v : String} {k d : Option String} {A : List Act} {w : Act}
    (hw : w ∈ acts v A) (h : ∀ r ∈ replacers v d A, w.addr ∉ r.replaces) :
    w ∈ current v k d A :=
  mem_current_iff.2 ⟨hw, fun r hr _ => h r hr⟩

/-- Whatever a register reads, it reads from a current write. -/
theorem registerPerKey_from_current {v kk : String} {d : Option String} {A : List Act}
    {x : Val} {a : Act}
    (h : pickAct ((current v (some kk) d A).filter (fun a => a.get kk == some x)) = some a) :
    a ∈ current v (some kk) d A ∧ a.get kk = some x := by
  have hm := (pickAct_spec h).1
  simp only [List.mem_filter, beq_iff_eq] at hm
  exact hm

/-! ## Sums contribute once per address (REQ-1930, `sum_once_per_address`) -/

theorem foldl_add_init (k : String) (T : List Act) (c : Int) :
    T.foldl (fun acc a => acc + amount k a) c = c + T.foldl (fun acc a => acc + amount k a) 0 := by
  induction T generalizing c with
  | nil => simp
  | cons t rest ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [ih (c + amount k t), ih (amount k t), Int.add_assoc]

theorem sumField_cons (k : String) (a : Act) (T : List Act) :
    sumField k (a :: T) = amount k a + sumField k T := by
  simp only [sumField, List.foldl_cons, Int.zero_add]
  exact foldl_add_init k T (amount k a)

/-- A newly accepted act adds its amount exactly once; a re-delivered one
adds nothing. -/
theorem sumField_insert (k : String) (a : Act) (A : List Act) :
    sumField k (insertAct a A) = sumField k A + (if a ∈ A then 0 else amount k a) := by
  simp only [insertAct]; split
  · simp
  · rw [sumField_cons, Int.add_comm]

/-! ## The binder (SPEC-019 R.5; REQ-1930 `intend_sound`) -/

/-- The predecessor performatives a protocol admits for a verb (one alternative set). -/
structure Protocol where
  /-- The verbs an accepted predecessor of `verb` may carry. -/
  allowed : String → List String

/-- The accepted acts whose verb the protocol admits as a predecessor of `verb`. -/
def candidates (P : Protocol) (A : List Act) (verb : String) : List Act :=
  A.filter (fun a => (P.allowed verb).contains a.verb)

/-- The signer's own candidates. -/
def ownActs (P : Protocol) (A : List Act) (signer verb : String) : List Act :=
  (candidates P A verb).filter (fun a => a.signer == signer)

/-- The signer's tips: own candidates no own candidate names as predecessor. -/
def tips (P : Protocol) (A : List Act) (signer verb : String) : List Act :=
  (ownActs P A signer verb).filter (fun a => !(ownActs P A signer verb).any (fun b => b.preds.contains a.addr))

/-- Step 5 of R.5: the signer's own tip among candidates, else the greatest address. -/
def choosePred (P : Protocol) (A : List Act) (signer verb : String) : Option Act :=
  match pickAct (tips P A signer verb), pickAct (ownActs P A signer verb) with
  | some t, _ => some t
  | none, some t => some t
  | none, none => pickAct (candidates P A verb)

/-- The key of an intent, read from its fields before the act exists. -/
def keyOfFields (k : Option String) (fields : List (String × Val)) : Option Val :=
  match k with
  | none => none
  | some k => List.lookup k fields

theorem keyOf_eq (k : Option String) (a : Act) : keyOf k a = keyOfFields k a.fields := by
  cases k <;> rfl

/-- Step 4 of R.5: the addresses of the current writes for the intent's key. -/
def bindReplaces (v : String) (kk d : Option String) (A : List Act) (key : Option Val) : List Nat :=
  ((current v kk d A).filter (fun w => decide (keyOf kk w = key))).map Act.addr

/-- Steps 4–6 of R.5 for a writing verb: the completed act. `fresh` is the
content address the canonicalised act will have; the host supplies the
signer. -/
def intend (P : Protocol) (v : String) (kk d : Option String) (A : List Act) (signer : String)
    (fields : List (String × Val)) (fresh : Nat) : Option Act :=
  (choosePred P A signer v).map fun p =>
    { addr := fresh, verb := v, signer := signer, preds := [p.addr], fields := fields,
      replaces := bindReplaces v kk d A (keyOfFields kk fields) }

theorem mem_candidates {P : Protocol} {A : List Act} {verb : String} {q : Act}
    (hq : q ∈ candidates P A verb) : q ∈ A ∧ q.verb ∈ P.allowed verb := by
  have := List.mem_filter.1 hq
  exact ⟨this.1, List.contains_iff_mem.1 this.2⟩

theorem choosePred_mem {P : Protocol} {A : List Act} {signer verb : String} {p : Act}
    (h : choosePred P A signer verb = some p) : p ∈ A ∧ p.verb ∈ P.allowed verb := by
  unfold choosePred at h
  cases ht : pickAct (tips P A signer verb) with
  | some t =>
    rw [ht] at h
    simp only [Option.some.injEq] at h
    subst h
    exact mem_candidates (List.mem_filter.1 (List.mem_filter.1 (pickAct_spec ht).1).1).1
  | none =>
    rw [ht] at h
    cases ho : pickAct (ownActs P A signer verb) with
    | some t =>
      rw [ho] at h
      simp only [Option.some.injEq] at h
      subst h
      exact mem_candidates (List.mem_filter.1 (pickAct_spec ho).1).1
    | none =>
      rw [ho] at h
      exact mem_candidates (pickAct_spec h).1

/-- **Binder soundness, predecessor** (`intend_pred_valid`): the act's one
predecessor is an accepted act whose verb the protocol admits for `v`, so
`verify_causal` returns `Valid` against the accepted set. -/
theorem intend_pred_valid {P : Protocol} {v : String} {kk d : Option String} {A : List Act}
    {signer : String} {fields : List (String × Val)} {fresh : Nat} {m : Act}
    (h : intend P v kk d A signer fields fresh = some m) :
    ∃ p ∈ A, m.preds = [p.addr] ∧ p.verb ∈ P.allowed v := by
  simp only [intend, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨hpA, hv⟩ := choosePred_mem hp
  exact ⟨p, hpA, rfl, hv⟩

/-- **Binder soundness, `:replaces`** (`intend_replaces_current`): the act
names exactly the current writes of its key, no more and no fewer. -/
theorem intend_replaces_current {P : Protocol} {v : String} {kk d : Option String} {A : List Act}
    {signer : String} {fields : List (String × Val)} {fresh : Nat} {m : Act}
    (h : intend P v kk d A signer fields fresh = some m) (x : Nat) :
    x ∈ m.replaces ↔ ∃ w ∈ current v kk d A, keyOf kk w = keyOf kk m ∧ w.addr = x := by
  simp only [intend, Option.map_eq_some_iff] at h
  obtain ⟨p, _, rfl⟩ := h
  simp only [bindReplaces, List.mem_map, List.mem_filter, decide_eq_true_eq, keyOf_eq]
  constructor
  · rintro ⟨w, ⟨hw, hk⟩, rfl⟩
    exact ⟨w, hw, hk, rfl⟩
  · rintro ⟨w, hw, hk, rfl⟩
    exact ⟨w, ⟨hw, hk⟩, rfl⟩

/-- **Binder soundness, supersession** (`intend_supersedes`): once the act is
accepted, every write it names is no longer current. -/
theorem intend_supersedes {P : Protocol} {v : String} {kk d : Option String} {A : List Act}
    {signer : String} {fields : List (String × Val)} {fresh : Nat} {m w : Act}
    (h : intend P v kk d A signer fields fresh = some m)
    (hw : w ∈ current v kk d A) (hk : keyOf kk w = keyOf kk m) :
    w ∉ current v kk d (insertAct m A) := by
  have hm : m ∈ acts v (insertAct m A) := by
    have : m.verb = v := by
      simp only [intend, Option.map_eq_some_iff] at h
      obtain ⟨p, _, rfl⟩ := h; rfl
    simp only [acts, List.mem_filter, beq_iff_eq, this, and_true]
    exact (insertAct_setEq m A m).2 List.mem_cons_self
  have hr : m ∈ replacers v d (insertAct m A) := by
    simp only [replacers, List.mem_append]; exact Or.inl hm
  have named : w.addr ∈ m.replaces :=
    (intend_replaces_current h w.addr).2 ⟨w, hw, hk, rfl⟩
  exact replaced_never_current hr hk.symm named

/-- **Binder soundness, currency** (`intend_current_after`): the accepted act
is itself current, provided nothing already accepted names its fresh
address. -/
theorem intend_current_after {P : Protocol} {v : String} {kk d : Option String} {A : List Act}
    {signer : String} {fields : List (String × Val)} {fresh : Nat} {m : Act}
    (h : intend P v kk d A signer fields fresh = some m)
    (unnamed : ∀ r ∈ replacers v d A, fresh ∉ r.replaces)
    (self : fresh ∉ bindReplaces v kk d A (keyOf kk m)) :
    m ∈ current v kk d (insertAct m A) := by
  have hv : m.verb = v ∧ m.addr = fresh ∧ m.replaces = bindReplaces v kk d A (keyOf kk m) := by
    simp only [intend, Option.map_eq_some_iff] at h
    obtain ⟨p, _, rfl⟩ := h
    exact ⟨rfl, rfl, by rw [keyOf_eq]⟩
  obtain ⟨hverb, haddr, hrep⟩ := hv
  apply unnamed_is_current
  · simp only [acts, List.mem_filter, beq_iff_eq, hverb, and_true]
    exact (insertAct_setEq m A m).2 List.mem_cons_self
  · intro r hr
    simp only [replacers, List.mem_append] at hr
    have hmem : r ∈ (m :: A) ∨ r ∈ A := by
      rcases hr with hr | hr
      · left; exact (insertAct_setEq m A r).1 (List.mem_filter.1 hr).1
      · cases d with
        | none => simp at hr
        | some d => left; exact (insertAct_setEq m A r).1 (List.mem_filter.1 hr).1
    rw [haddr]
    by_cases hrm : r = m
    · subst hrm; rw [hrep]; exact self
    · have hrA : r ∈ A := by
        rcases hmem with hr' | hr'
        · rcases List.mem_cons.1 hr' with e | e
          · exact absurd e hrm
          · exact e
        · exact hr'
      have hr_rep : r ∈ replacers v d A := by
        simp only [replacers, List.mem_append]
        rcases hr with hr | hr
        · left
          simp only [acts, List.mem_filter] at hr ⊢
          exact ⟨hrA, hr.2⟩
        · right
          cases d with
          | none => simp at hr
          | some d =>
            simp only [acts, List.mem_filter] at hr ⊢
            exact ⟨hrA, hr.2⟩
      exact unnamed r hr_rep

end State
end CBCL
