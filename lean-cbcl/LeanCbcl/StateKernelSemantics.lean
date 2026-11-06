import LeanCbcl.State
import LeanCbcl.StateProgress
import LeanCbcl.HlcRegister

/-!
Independent declarative correctness of the typed application-data kernel.
Specifications below use only logical membership, field lookup, maximality,
finite enumeration and arithmetic. They never call executable selections or
reductions. Addresses and field lookup retain the State.lean typed boundary.
-/
namespace CBCL.StateKernelSemantics
open CBCL.State

/-! ## Independent selection specification -/

/-- Raw-history opener evidence, before application-data filtering. -/
def Allowed (A : List Act) (opener field : String) (x : Val) : Prop :=
  ∃ o ∈ A, o.verb = opener ∧
    (∀ b ∈ A, b.verb = opener → b.addr ≤ o.addr) ∧
    ∃ xs, o.get field = some (.list xs) ∧ x ∈ xs.map Scalar.toVal

/-- Resolved domain filter with a raw opener initializer. -/
structure Domain where
  /-- Verb filtered by the domain. -/
  verb : String
  /-- Field tested for domain membership. -/
  key : String
  /-- Initializer verb. -/
  opener : String
  /-- Initializer list field. -/
  field : String

/-- Admission here means a data-domain filter, never protocol acceptance. -/
def Admitted (ds : List Domain) (A : List Act) (a : Act) : Prop :=
  a ∈ A ∧ ∀ d ∈ ds, a.verb = d.verb →
    ∃ x, a.get d.key = some x ∧ Allowed A d.opener d.field x

/-- All replacement evidence is taken from one fixed admitted source. -/
inductive Selection where
  | verb (v : String)
  | current (v : String) (key delete : Option String)
  | own (v : String)
  | byKey (source : Selection) (key : String) (value : Val)
  | bySigner (source : Selection) (signer : String)
  | withField (source : Selection) (key : String)

/-- Independent semantics: membership, not evaluation of a list algorithm. -/
def Selected (P : Act → Prop) : Selection → Act → Prop
  | .verb v, a => P a ∧ a.verb = v
  | .current v k d, a => P a ∧ a.verb = v ∧
      ∀ r, P r → (r.verb = v ∨ ∃ dv, d = some dv ∧ r.verb = dv) →
        keyOf k r = keyOf k a → a.addr ∉ r.replaces
  | .own v, a => P a ∧ a.verb = v ∧
      ∀ r, P r → r.verb = v → r.signer = a.signer → a.addr ∉ r.replaces
  | .byKey s k x, a => Selected P s a ∧ a.get k = some x
  | .bySigner s signer, a => Selected P s a ∧ a.signer = signer
  | .withField s k, a => Selected P s a ∧ (a.get k).isSome = true

/-- Executable selection over a fixed admitted history. -/
def select (A : List Act) : Selection → List Act
  | .verb v => acts v A
  | .current v k d => current v k d A
  | .own v => currentOwn v A
  | .byKey s k x => (select A s).filter (fun a => a.get k == some x)
  | .bySigner s signer => (select A s).filter (fun a => a.signer == signer)
  | .withField s k => (select A s).filter (fun a => (a.get k).isSome)

/-- The named key lookup is shared typed input access, not a selector. -/
theorem select_correct (A : List Act) (s : Selection) (a : Act) :
    a ∈ select A s ↔ Selected (fun a => a ∈ A) s a := by
  induction s with
  | verb v => simp [select, Selected, acts]
  | current v k d =>
      simp only [select, mem_current_iff, acts, List.mem_filter, beq_iff_eq, Selected]
      constructor
      · rintro ⟨⟨ha, hv⟩, hn⟩
        refine ⟨ha, hv, ?_⟩
        intro r hr verbs key
        apply hn r
        · simp only [replacers, acts, List.mem_append, List.mem_filter, beq_iff_eq]
          rcases verbs with hv | ⟨dv, hd, hv⟩
          · exact Or.inl ⟨hr, hv⟩
          · subst d; exact Or.inr (by simpa using And.intro hr hv)
        · exact key
      · rintro ⟨ha, hv, hn⟩
        refine ⟨⟨ha, hv⟩, ?_⟩
        intro r hr key
        simp only [replacers, acts, List.mem_append, List.mem_filter, beq_iff_eq] at hr
        rcases hr with hr | hr
        · exact hn r hr.1 (Or.inl hr.2) key
        · cases d with
          | none => simp at hr
          | some dv =>
              have hr : r ∈ A ∧ r.verb = dv := by simpa using hr
              exact hn r hr.1 (Or.inr ⟨dv, rfl, hr.2⟩) key
  | own v =>
      simp only [select, mem_currentOwn_iff, acts, List.mem_filter, beq_iff_eq, Selected]
      constructor
      · rintro ⟨⟨ha, hv⟩, hn⟩
        exact ⟨ha, hv, fun r hr hv hs => hn r ⟨hr, hv⟩ hs⟩
      · rintro ⟨ha, hv, hn⟩
        exact ⟨⟨ha, hv⟩, fun r hr hs => hn r hr.1 hr.2 hs⟩
  | byKey s k x ih => simp [select, Selected, ih]
  | bySigner s signer ih => simp [select, Selected, ih]
  | withField s k ih => simp [select, Selected, ih]

theorem select_unique {A : List Act} (h : NodupAddr A) (s : Selection) :
    NodupAddr (select A s) := by
  induction s with
  | verb v => exact h.acts v
  | current v k d => exact h.current v k d
  | own v => exact h.currentOwn v
  | byKey s k x ih => exact ih.filter _
  | bySigner s signer ih => exact ih.filter _
  | withField s k ih => exact ih.filter _

/-! ## Independent reduction specifications -/

/-- A finite set is described by any duplicate-free enumeration, not the
concrete selection order. Address uniqueness excludes conflicting bodies. -/
def Enumerates (P : Act → Prop) (T : List Act) : Prop :=
  NodupAddr T ∧ ∀ a, a ∈ T ↔ P a

/-- Independent greatest-address predicate. -/
def Greatest (P : Act → Prop) (a : Act) : Prop :=
  P a ∧ ∀ b, P b → b.addr ≤ a.addr

/-- Independent optional winner projection. -/
def Choice (P : Act → Prop) (key : String) (result : Option Val) : Prop :=
  ((¬ ∃ a, P a) ∧ result = none) ∨
  ∃ a, Greatest P a ∧ result = a.get key

/-- Independent finite set cardinality. -/
def Cardinality (P : Act → Prop) (n : Nat) : Prop :=
  ∃ T, Enumerates P T ∧ n = T.length

/-- Arithmetic meaning of a typed field, independently of State.amount. -/
def Number (key : String) (a : Act) : Int :=
  match a.get key with
  | some (.int z) => z
  | _ => 0

/-- Independent exact integer total over an arbitrary enumeration. -/
def Total (P : Act → Prop) (key : String) (z : Int) : Prop :=
  ∃ T, Enumerates P T ∧ z = (T.map (Number key)).sum

/-- Independent distinct field membership. -/
def Values (P : Act → Prop) (key : String) (result : Val → Bool) : Prop :=
  ∀ x, result x = true ↔ ∃ a, P a ∧ a.get key = some x

/-- Independent nonempty source observation. -/
def Existence (P : Act → Prop) (result : Bool) : Prop :=
  result = true ↔ ∃ a, P a

/-- Independent address-keyed event provenance. -/
def Events (P : Act → Prop) (key : String)
    (result : Nat → Option (String × Val)) : Prop :=
  ∀ address signer value, result address = some (signer, value) ↔
    ∃ a, P a ∧ a.addr = address ∧ a.signer = signer ∧ a.get key = some value

private theorem greatest_unique {T : List Act} (unique : NodupAddr T)
    {a b : Act} (ha : Greatest (fun a => a ∈ T) a)
    (hb : Greatest (fun a => a ∈ T) b) : a = b :=
  unique.eq_of_addr ha.1 hb.1 (Nat.le_antisymm (hb.2 a ha.1) (ha.2 b hb.1))

theorem pick_correct {T : List Act} (unique : NodupAddr T) (key : String)
    (result : Option Val) : Choice (fun a => a ∈ T) key result ↔ result = pick key T := by
  cases hp : pickAct T with
  | none =>
      have empty := pickAct_eq_none_iff.mp hp
      subst T
      simp [Choice, Greatest, pick, pickAct]
  | some a =>
      have ha := pickAct_spec hp
      constructor
      · intro spec
        rcases spec with ⟨empty, _⟩ | ⟨b, hb, result⟩
        · exact False.elim (empty ⟨a, ha.1⟩)
        · have same := greatest_unique unique hb ha
          simpa [pick, hp, same] using result
      · intro result
        exact Or.inr ⟨a, ha, by simpa [pick, hp] using result⟩

theorem cardinality_correct {T : List Act} (unique : NodupAddr T) (n : Nat) :
    Cardinality (fun a => a ∈ T) n ↔ n = size T := by
  constructor
  · rintro ⟨U, ⟨hu, same⟩, rfl⟩
    exact (perm_of_setEq hu unique same).length_eq
  · intro h; exact ⟨T, ⟨unique, fun _ => Iff.rfl⟩, h⟩

theorem sumField_eq (key : String) (T : List Act) :
    sumField key T = (T.map (Number key)).sum := by
  induction T with
  | nil => rfl
  | cons a T ih =>
      rw [sumField_cons, List.map_cons, List.sum_cons, ih]
      rfl

theorem total_correct {T : List Act} (unique : NodupAddr T) (key : String) (z : Int) :
    Total (fun a => a ∈ T) key z ↔ z = sumField key T := by
  constructor
  · rintro ⟨U, ⟨hu, same⟩, rfl⟩
    rw [← sumField_eq]
    exact sumField_setEq hu unique same key
  · intro h
    exact ⟨T, ⟨unique, fun _ => Iff.rfl⟩, h.trans (sumField_eq key T)⟩

theorem values_correct (T : List Act) (key : String) :
    Values (fun a => a ∈ T) key (has key T) := by
  intro x
  simp [has]

theorem existence_correct (T : List Act) :
    Existence (fun a => a ∈ T) (!(T.isEmpty)) := by
  cases T <;> simp [Existence]

/-- New typed counterpart of the address-keyed events rule; absent fields
produce no entry, and each retained value includes its authenticated signer. -/
def events (key : String) (T : List Act) (address : Nat) : Option (String × Val) :=
  (T.find? (fun a => a.addr == address)).bind
    (fun a => (a.get key).map (fun value => (a.signer, value)))

theorem events_correct {T : List Act} (unique : NodupAddr T) (key : String) :
    Events (fun a => a ∈ T) key (events key T) := by
  intro address signer value
  constructor
  · intro h
    unfold events at h
    cases found : T.find? (fun a => a.addr == address) with
    | none => simp [found] at h
    | some a =>
        have mem := List.mem_of_find?_eq_some found
        have addr : a.addr = address := by simpa using List.find?_some found
        cases field : a.get key with
        | none => simp [found, field] at h
        | some x =>
            simp only [found, Option.bind_some, field, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at h
            exact ⟨a, mem, addr, h.1, by simpa [h.2] using field⟩
  · rintro ⟨a, ha, addr, hs, field⟩
    have found : T.find? (fun b => b.addr == address) = some a := by
      cases hf : T.find? (fun b => b.addr == address) with
      | none =>
          have no := (List.find?_eq_none.mp hf) a ha
          simp [addr] at no
      | some b =>
          have hb := List.mem_of_find?_eq_some hf
          have hbaddr : b.addr = address := by simpa using List.find?_some hf
          have same := unique.eq_of_addr hb ha (hbaddr.trans addr.symm)
          simp [same]
    simp [events, found, field, hs]



/-! ## Domain filtering before every data selection -/

theorem allowed_correct {A : List Act} (unique : NodupAddr A)
    (opener field : String) (x : Val) :
    x ∈ allowedOf opener field A ↔ Allowed A opener field x := by
  cases hp : pickAct (acts opener A) with
  | none =>
      have empty := pickAct_eq_none_iff.mp hp
      simp only [allowedOf, last, pick, hp, Option.bind_none, List.not_mem_nil, false_iff]
      rintro ⟨o, ho, hv, _⟩
      have mem : o ∈ acts opener A := by simp [acts, ho, hv]
      rw [empty] at mem
      exact List.not_mem_nil mem
  | some o =>
      have top := pickAct_spec hp
      have omem := List.mem_filter.mp top.1
      have ov : o.verb = opener := by simpa using omem.2
      have greatest : ∀ b ∈ A, b.verb = opener → b.addr ≤ o.addr := by
        intro b hb hv; exact top.2 b (by simp [acts, hb, hv])
      have other_unique : ∀ b ∈ A, b.verb = opener →
          (∀ a ∈ A, a.verb = opener → a.addr ≤ b.addr) → b = o := by
        intro b hb hv max
        exact unique.eq_of_addr hb omem.1 (Nat.le_antisymm (greatest b hb hv) (max o omem.1 ov))
      simp only [allowedOf, last, pick, hp, Option.bind_some]
      constructor
      · intro member
        refine ⟨o, omem.1, ov, greatest, ?_⟩
        cases hf : o.get field with
        | none => simp [hf] at member
        | some value =>
            cases value with
            | str s => simp [hf] at member
            | int n => simp [hf] at member
            | bool b => simp [hf] at member
            | list xs => exact ⟨xs, rfl, by simpa [hf] using member⟩
      · rintro ⟨b, hb, hv, max, xs, fieldValue, member⟩
        have same := other_unique b hb hv max
        subst b
        simpa [fieldValue] using member

/-- Concrete domain pass retains the raw history as opener evidence. -/
def admitted (ds : List Domain) (A : List Act) : List Act :=
  A.filter (fun a => ds.all (fun d => if a.verb == d.verb then
    inDomain d.key (allowedOf d.opener d.field A) a else true))

theorem domain_check (key : String) (allowed : List Val) (a : Act) :
    inDomain key allowed a = true ↔ ∃ x, a.get key = some x ∧ x ∈ allowed := by
  cases h : a.get key <;> simp [inDomain, h]

theorem admitted_correct {A : List Act} (unique : NodupAddr A)
    (ds : List Domain) (a : Act) : a ∈ admitted ds A ↔ Admitted ds A a := by
  simp only [admitted, List.mem_filter, List.all_eq_true, Admitted]
  constructor
  · rintro ⟨ha, checked⟩
    refine ⟨ha, ?_⟩
    intro d hd hv
    have good := checked d hd
    simp only [hv, beq_self_eq_true, ↓reduceIte] at good
    obtain ⟨x, field, member⟩ := (domain_check _ _ _).mp good
    exact ⟨x, field, (allowed_correct unique _ _ _).mp member⟩
  · rintro ⟨ha, spec⟩
    refine ⟨ha, ?_⟩
    intro d hd
    by_cases hv : a.verb = d.verb
    · obtain ⟨x, field, allowed⟩ := spec d hd hv
      simp only [hv, beq_self_eq_true, ↓reduceIte]
      exact (domain_check _ _ _).mpr ⟨x, field, (allowed_correct unique _ _ _).mpr allowed⟩
    · simp [hv]

theorem admitted_unique {A : List Act} (unique : NodupAddr A) (ds : List Domain) :
    NodupAddr (admitted ds A) := unique.filter _

/-- Replacing a membership predicate by an equivalent one preserves selection. -/
theorem selected_congr {P Q : Act → Prop} (same : ∀ a, P a ↔ Q a)
    (s : Selection) (a : Act) : Selected P s a ↔ Selected Q s a := by
  induction s with
  | verb v => simp only [Selected, same]
  | current v k d => simp only [Selected, same]
  | own v => simp only [Selected, same]
  | byKey s k x ih => simp only [Selected, ih]
  | bySigner s signer ih => simp only [Selected, ih]
  | withField s k ih => simp only [Selected, ih]

theorem data_selection_correct {A : List Act} (unique : NodupAddr A)
    (ds : List Domain) (s : Selection) (a : Act) :
    a ∈ select (admitted ds A) s ↔ Selected (Admitted ds A) s a :=
  (select_correct _ _ _).trans (selected_congr (admitted_correct unique ds) s a)

end CBCL.StateKernelSemantics
