import LeanCbcl.CheckpointSummary
import LeanCbcl.CheckpointRender

/-!
Compact, domain-free exists/count/counter/set-union/events state. Histories below
are ghost reference inputs. Coverage is exact accepted-identity membership; no
signature or certificate-truth claim is made. Integer arithmetic is unbounded:
Rust's checked-overflow diagnostics require a separate refinement obligation.
Events store only address, authenticated signer and selected value, never an Act.
-/
namespace CBCL.CheckpointData
open State StateKernelSemantics StateKernelQueries StateKernel CheckpointSummary

namespace Exists
/-- Compact stored state for this rule. -/
abbrev Summary := Bool
/-- Initial state before any accepted identity. -/
def empty : Summary := false
/-- Apply one fresh identity; covered identities leave state unchanged. -/
def step (verb : String) (coverage : Nat → Bool) (s : Summary) (e : Act) : Summary :=
  if coverage e.addr then s else s || e.verb == verb
/-- Exact correspondence with the normalized reference history. -/
def Invariant (verb : String) (H : List Act) (s : Summary) : Prop :=
  s = State.existsRule verb H
theorem empty_invariant (verb : String) : Invariant verb [] empty := by
  rfl
theorem step_preserves {verb : String} {H : List Act} {s : Summary} {e : Act}
    (valid : Invariant verb H s) (fresh : covered H e.addr = false) :
    Invariant verb (e :: H) (step verb (covered H) s e) := by
  rw [Invariant] at valid ⊢
  rw [valid]
  by_cases h : e.verb = verb <;>
    simp [step, fresh, State.existsRule, acts, h]
theorem duplicate_noop (verb : String) (coverage : Nat → Bool) (s : Summary) (e : Act)
    (seen : coverage e.addr = true) : step verb coverage s e = s := by
  simp [step, seen]
theorem render_eq (input : Input) {verb : String} {H : List Act} {s : Summary}
    (valid : Invariant verb H s) :
    Observation.boolean s = evaluate {input with acts := H} [] (.existsRule (.verb verb)) := by
  simp only [evaluate, CheckpointRender.admitted_empty, select]
  exact congrArg Observation.boolean valid
end Exists

namespace Count
/-- Compact stored state for this rule. -/
abbrev Summary := Nat
/-- Initial state before any accepted identity. -/
def empty : Summary := 0
/-- Apply one fresh identity; covered identities leave state unchanged. -/
def step (verb : String) (coverage : Nat → Bool) (s : Summary) (e : Act) : Summary :=
  if coverage e.addr then s else if e.verb = verb then s + 1 else s
/-- Exact correspondence with the normalized reference history. -/
def Invariant (verb : String) (H : List Act) (s : Summary) : Prop :=
  s = State.count verb H
theorem empty_invariant (verb : String) : Invariant verb [] empty := by
  rfl
theorem step_preserves {verb : String} {H : List Act} {s : Summary} {e : Act}
    (valid : Invariant verb H s) (fresh : covered H e.addr = false) :
    Invariant verb (e :: H) (step verb (covered H) s e) := by
  rw [Invariant] at valid ⊢
  rw [valid]
  by_cases h : e.verb = verb <;> simp [step, fresh, State.count, size, acts, h]
theorem duplicate_noop (verb : String) (coverage : Nat → Bool) (s : Summary) (e : Act)
    (seen : coverage e.addr = true) : step verb coverage s e = s := by
  simp [step, seen]
theorem render_eq (input : Input) {verb : String} {H : List Act} {s : Summary}
    (valid : Invariant verb H s) :
    Observation.integer (Int.ofNat s) = evaluate {input with acts := H} [] (.count (.verb verb)) := by
  simp only [evaluate, CheckpointRender.admitted_empty, select]
  exact congrArg (fun n => Observation.integer (Int.ofNat n)) valid
end Count

namespace Counter
/-- Compact stored state for this rule. -/
abbrev Summary := Int
/-- Initial state before any accepted identity. -/
def empty : Summary := 0
/-- Independent increment and decrement contributions, using unbounded integers. -/
def delta (increment decrement field : String) (e : Act) : Int :=
  (if e.verb = increment then amount field e else 0) -
    (if e.verb = decrement then amount field e else 0)
/-- Apply one fresh identity; covered identities leave state unchanged. -/
def step (increment decrement field : String) (coverage : Nat → Bool)
    (s : Summary) (e : Act) : Summary :=
  if coverage e.addr then s else s + delta increment decrement field e
/-- Exact correspondence with the normalized reference history. -/
def Invariant (increment decrement field : String) (H : List Act) (s : Summary) : Prop :=
  s = State.counter increment decrement field H
theorem empty_invariant (increment decrement field : String) :
    Invariant increment decrement field [] empty := by rfl
theorem step_preserves {increment decrement field : String} {H : List Act}
    {s : Summary} {e : Act} (valid : Invariant increment decrement field H s)
    (fresh : covered H e.addr = false) :
    Invariant increment decrement field (e :: H)
      (step increment decrement field (covered H) s e) := by
  rw [Invariant] at valid ⊢
  rw [valid]
  simp only [step, fresh, Bool.false_eq_true, ↓reduceIte, delta, State.counter, acts,
    List.filter_cons]
  by_cases hi : e.verb = increment <;> by_cases hd : e.verb = decrement <;>
    simp_all [sumField_cons] <;>
      simp only [Int.sub_eq_add_neg, Int.neg_add] <;> ac_rfl
theorem duplicate_noop (increment decrement field : String) (coverage : Nat → Bool)
    (s : Summary) (e : Act) (seen : coverage e.addr = true) :
    step increment decrement field coverage s e = s := by simp [step, seen]
theorem render_eq (input : Input) {increment decrement field : String}
    {H : List Act} {s : Summary} (valid : Invariant increment decrement field H s) :
    Observation.integer s = evaluate {input with acts := H} []
      (.counter (.verb increment) (.verb decrement) field) := by
  simp only [evaluate, CheckpointRender.admitted_empty, select]
  exact congrArg Observation.integer valid
end Counter

namespace SetUnion
/-- Compact stored state for this rule. -/
abbrev Summary := List Val
/-- Initial state before any accepted identity. -/
def empty : Summary := []
/-- Apply one fresh identity; covered identities leave state unchanged. -/
def step (verb field : String) (coverage : Nat → Bool) (s : Summary) (e : Act) : Summary :=
  if coverage e.addr then s else if e.verb = verb then
    match e.get field with
    | none => s
    | some value => s.insert value
  else s
/-- Exact correspondence with the normalized reference history. -/
def Invariant (verb field : String) (H : List Act) (s : Summary) : Prop :=
  ∀ value, value ∈ s ↔ ∃ a ∈ H, a.verb = verb ∧ a.get field = some value
theorem empty_invariant (verb field : String) : Invariant verb field [] empty := by
  simp [Invariant, empty]
theorem step_preserves {verb field : String} {H : List Act} {s : Summary} {e : Act}
    (valid : Invariant verb field H s) (fresh : covered H e.addr = false) :
    Invariant verb field (e :: H) (step verb field (covered H) s e) := by
  intro value
  have old := valid value
  by_cases hv : e.verb = verb <;> cases hg : e.get field <;>
    simp [step, fresh, hv, hg, old, List.mem_cons] <;> grind
theorem duplicate_noop (verb field : String) (coverage : Nat → Bool) (s : Summary) (e : Act)
    (seen : coverage e.addr = true) : step verb field coverage s e = s := by
  simp [step, seen]
/-- Observe set membership without retaining acts. -/
def render (s : Summary) : Val → Bool := fun value => s.contains value
theorem render_native {verb field : String} {H : List Act} {s : Summary}
    (valid : Invariant verb field H s) : render s = State.setUnion verb field H := by
  funext value
  apply Bool.eq_iff_iff.mpr
  change s.contains value = true ↔ (acts verb H).any (fun a => a.get field == some value) = true
  rw [List.contains_iff_mem, valid value]
  simp only [List.any_eq_true, acts, List.mem_filter, beq_iff_eq]
  grind
theorem render_eq (input : Input) {verb field : String} {H : List Act} {s : Summary}
    (valid : Invariant verb field H s) :
    Observation.values (render s) = evaluate {input with acts := H} [] (.distinct (.verb verb) field) := by
  simp only [evaluate, CheckpointRender.admitted_empty, select]
  exact congrArg Observation.values (render_native valid)
end SetUnion

namespace Events
/-- Output projection only: neither predecessors, verb nor unrelated fields are retained. -/
structure Projection where
  /-- Accepted identity used as the event key. -/
  addr : Nat
  /-- Authenticated event signer. -/
  signer : String
  /-- Selected event field value. -/
  value : Val
  deriving DecidableEq
/-- Compact stored state for this rule. -/
abbrev Summary := List Projection
/-- Initial state before any accepted identity. -/
def empty : Summary := []
/-- Select only the event address, signer and requested field. -/
def projection (verb field : String) (e : Act) : Option Projection :=
  if e.verb = verb then (e.get field).map (fun value => ⟨e.addr, e.signer, value⟩) else none
/-- Apply one fresh identity; covered identities leave state unchanged. -/
def step (verb field : String) (coverage : Nat → Bool) (s : Summary) (e : Act) : Summary :=
  if coverage e.addr then s else
    match projection verb field e with
    | none => s
    | some p => p :: s
/-- Exact correspondence with the normalized reference history. -/
def Invariant (verb field : String) (H : List Act) (s : Summary) : Prop :=
  ∀ p, p ∈ s ↔ ∃ a ∈ H,
    a.verb = verb ∧ a.addr = p.addr ∧ a.signer = p.signer ∧ a.get field = some p.value
theorem projection_eq_some (verb field : String) (e : Act) (p : Projection) :
    projection verb field e = some p ↔
      e.verb = verb ∧ e.addr = p.addr ∧ e.signer = p.signer ∧ e.get field = some p.value := by
  cases p
  by_cases hv : e.verb = verb <;> cases hg : e.get field <;>
    simp [projection, hv, hg, Projection.mk.injEq] <;> grind
theorem empty_invariant (verb field : String) : Invariant verb field [] empty := by
  simp [Invariant, empty]
theorem mem_step (verb field : String) (coverage : Nat → Bool) (s : Summary) (e : Act)
    (fresh : coverage e.addr = false) (p : Projection) :
    p ∈ step verb field coverage s e ↔ p ∈ s ∨ projection verb field e = some p := by
  cases h : projection verb field e <;> simp [step, fresh, h, eq_comm, or_comm]
theorem step_preserves {verb field : String} {H : List Act} {s : Summary} {e : Act}
    (valid : Invariant verb field H s) (fresh : covered H e.addr = false) :
    Invariant verb field (e :: H) (step verb field (covered H) s e) := by
  intro p
  rw [mem_step _ _ _ _ _ fresh, valid p, projection_eq_some]
  simp only [List.mem_cons]
  grind
theorem duplicate_noop (verb field : String) (coverage : Nat → Bool) (s : Summary) (e : Act)
    (seen : coverage e.addr = true) : step verb field coverage s e = s := by
  simp [step, seen]
/-- Read the projected signer and value at an accepted address. -/
def read (s : Summary) (address : Nat) : Option (String × Val) :=
  (s.find? (fun p => p.addr == address)).map (fun p => (p.signer, p.value))
theorem read_correct {verb field : String} {H : List Act} {s : Summary}
    (valid : Invariant verb field H s) (unique : NodupAddr H)
    (address : Nat) (signer : String) (value : Val) :
    read s address = some (signer, value) ↔
      ∃ a ∈ H, a.verb = verb ∧ a.addr = address ∧ a.signer = signer ∧ a.get field = some value := by
  constructor
  · intro h
    cases found : s.find? (fun p => p.addr == address) with
    | none => simp [read, found] at h
    | some p =>
      have mem := List.mem_of_find?_eq_some found
      have addr : p.addr = address := by simpa using List.find?_some found
      have eq : p.signer = signer ∧ p.value = value := by simpa [read, found] using h
      obtain ⟨a, ha, hv, hid, hs, hf⟩ := (valid p).mp mem
      exact ⟨a, ha, hv, hid.trans addr, hs.trans eq.1, by simpa [eq.2] using hf⟩
  · rintro ⟨a, ha, hv, hid, hs, hf⟩
    have mem : (⟨address, signer, value⟩ : Projection) ∈ s :=
      (valid _).mpr ⟨a, ha, hv, hid, hs, hf⟩
    cases found : s.find? (fun p => p.addr == address) with
    | none =>
      have no := (List.find?_eq_none.mp found) _ mem
      simp at no
    | some p =>
      obtain ⟨b, hb, _, bid, bs, bf⟩ := (valid p).mp (List.mem_of_find?_eq_some found)
      have addr : p.addr = address := by simpa using List.find?_some found
      have same := unique.eq_of_addr hb ha (bid.trans (addr.trans hid.symm))
      subst b
      have ps : p.signer = signer := bs.symm.trans hs
      have pv : p.value = value := Option.some.inj (bf.symm.trans hf)
      simp [read, found, ps, pv]
theorem read_native {verb field : String} {H : List Act} {s : Summary}
    (valid : Invariant verb field H s) (unique : NodupAddr H) :
    read s = StateKernelSemantics.events field (acts verb H) := by
  funext address
  apply Option.ext
  intro pair
  obtain ⟨signer, value⟩ := pair
  rw [read_correct valid unique]
  have hu : NodupAddr (acts verb H) := unique.filter _
  rw [events_correct hu field]
  simp only [acts, List.mem_filter, beq_iff_eq]
  grind

/-- Convert a projected event lookup to its observable cell. -/
def cell : Option (String × Val) → Cell
  | none => .absent
  | some (signer, value) => .event signer value

/-- Finite native-address support and projected event payloads only. -/
def map (s : Summary) : FiniteMap :=
  ⟨uniqueKeys (s.map (fun p => .int p.addr)), fun key => match key with
    | .int n => if 0 ≤ n then cell (read s n.toNat) else .absent
    | _ => .absent⟩

theorem map_keys_nodup (s : Summary) : (map s).keys.Nodup :=
  uniqueKeys_nodup _

@[simp] theorem map_read_address (s : Summary) (address : Nat) :
    (map s).read (.int address) = cell (read s address) := by
  simp [map]

theorem map_keys {verb field : String} {H : List Act} {s : Summary}
    (valid : Invariant verb field H s) (key : Val) :
    key ∈ (map s).keys ↔ ∃ a ∈ H, a.verb = verb ∧
      ∃ value, a.get field = some value ∧ key = .int a.addr := by
  simp only [map, uniqueKeys_member, List.mem_map]
  constructor
  · rintro ⟨p, hp, hk⟩
    obtain ⟨a, ha, hv, hid, _, hf⟩ := (valid p).mp hp
    exact ⟨a, ha, hv, p.value, hf, by simp [hid, hk]⟩
  · rintro ⟨a, ha, hv, value, hf, rfl⟩
    exact ⟨⟨a.addr, a.signer, value⟩,
      (valid _).mpr ⟨a, ha, hv, rfl, rfl, hf⟩, rfl⟩

/-- Full native map graph for the events plan, including signer provenance. -/
theorem map_meaning (input : Input) {verb field : String} {H : List Act} {s : Summary}
    (valid : Invariant verb field H s) (unique : NodupAddr H) :
    MapMeaning input.clock input.signerRank (fun a => a ∈ H)
      ⟨.withField (.verb verb) field, .address, .address, field, true⟩ (map s) := by
  have support : ∀ key, key ∈ (map s).keys ↔ ∃ a,
      Selected (fun a => a ∈ H) (.withField (.verb verb) field) a ∧
        groupKey .address a = some key := by
    intro key
    rw [map_keys valid]
    simp only [Selected, groupKey, Option.some.injEq]
    constructor
    · rintro ⟨a, ha, hv, value, hf, rfl⟩
      exact ⟨a, ⟨⟨ha, hv⟩, by simp [hf]⟩, rfl⟩
    · rintro ⟨a, ⟨⟨ha, hv⟩, present⟩, hk⟩
      cases hf : a.get field with
      | none => simp [hf] at present
      | some value => exact ⟨a, ha, hv, value, hf, hk.symm⟩
  refine ⟨map_keys_nodup s, support, ?_⟩
  intro key hk
  obtain ⟨a, ha, hv, value, hf, rfl⟩ := (map_keys valid key).mp hk
  have lookup : read s a.addr = some (a.signer, value) :=
    (read_correct valid unique a.addr a.signer value).mpr ⟨a, ha, hv, rfl, rfl, hf⟩
  have output : (map s).read (.int a.addr) = .event a.signer value := by
    simp [lookup, cell]
  rw [output]
  refine ⟨some a, Or.inr ⟨a, ⟨0, 0, 0, a.addr⟩, ?_, rfl, ?_, rfl⟩,
    StateKernelQueries.Projection.paired a value hf⟩
  · exact ⟨⟨⟨ha, hv⟩, by simp [hf]⟩, rfl⟩
  · intro b other hb he
    have address : b.addr = a.addr :=
      Int.ofNat_inj.mp (by simpa [groupKey] using hb.2)
    change other = ⟨0, 0, 0, b.addr⟩ at he
    subst other
    simpa [address] using (HlcRegister.le_refl (⟨0, 0, 0, a.addr⟩ : HlcRegister.Key))

theorem map_native (input : Input) {verb field : String} {H : List Act} {s : Summary}
    (valid : Invariant verb field H s) (unique : NodupAddr H) :
    MapEquivalent (map s) (evalMap input.clock input.signerRank H
      ⟨.withField (.verb verb) field, .address, .address, field, true⟩) :=
  ((map_complete unique input.clock input.signerRank _ (map s)).mp
    (map_meaning input valid unique)).2
end Events

/- Shared identity-only execution harness. Concrete rule preservation lemmas,
not a hypothesized rendering/continuation equality, discharge its local contract. -/
namespace Machine
/-- Compact rule payload paired with exact identity coverage. -/
structure State (α : Type) where
  /-- Exact membership of accepted identities; retains no act bodies. -/
  coverage : Nat → Bool
  /-- Rule-specific compact payload. -/
  data : α

/-- Initial state before any accepted identity. -/
def empty (initial : α) : State α := ⟨fun _ => false, initial⟩
/-- Apply one fresh identity; covered identities leave state unchanged. -/
def step (update : (Nat → Bool) → α → Act → α) (s : State α) (e : Act) : State α :=
  if s.coverage e.addr then s else
    ⟨insertCoverage s.coverage e.addr, update s.coverage s.data e⟩
/-- Fold accepted tail inputs with identity deduplication. -/
def advance (update : (Nat → Bool) → α → Act → α) (s : State α) (tail : List Act) : State α :=
  tail.foldl (step update) s
/-- Construct compact state from a finite accepted prefix. -/
def checkpoint (initial : α) (update : (Nat → Bool) → α → Act → α) (H : List Act) : State α :=
  advance update (empty initial) H
/-- Exact coverage and the rule-specific history invariant. -/
def Valid (invariant : List Act → α → Prop) (H : List Act) (s : State α) : Prop :=
  (∀ id, s.coverage id = covered H id) ∧ invariant H s.data

theorem empty_valid {initial : α} {invariant : List Act → α → Prop}
    (valid : invariant [] initial) : Valid invariant [] (empty initial) :=
  ⟨fun _ => rfl, valid⟩

theorem step_valid {update : (Nat → Bool) → α → Act → α}
    {invariant : List Act → α → Prop}
    (preserves : ∀ {H s e}, invariant H s → covered H e.addr = false →
      invariant (e :: H) (update (covered H) s e))
    {H : List Act} {s : State α} (valid : Valid invariant H s) (e : Act) :
    Valid invariant (ingest H e) (step update s e) := by
  by_cases seen : covered H e.addr = true
  · simpa [step, valid.1, ingest, seen] using valid
  · have fresh : covered H e.addr = false := Bool.eq_false_iff.mpr seen
    have coverage : s.coverage = covered H := funext valid.1
    simp only [step, coverage, fresh, Bool.false_eq_true, ↓reduceIte, ingest, Valid]
    exact ⟨fun id => by simp [insertCoverage], preserves valid.2 fresh⟩

theorem advance_valid {update : (Nat → Bool) → α → Act → α}
    {invariant : List Act → α → Prop}
    (preserves : ∀ {H s e}, invariant H s → covered H e.addr = false →
      invariant (e :: H) (update (covered H) s e))
    {H : List Act} {s : State α} (valid : Valid invariant H s) (tail : List Act) :
    Valid invariant (replay H tail) (advance update s tail) := by
  induction tail generalizing H s with
  | nil => exact valid
  | cons e rest ih => exact ih (step_valid preserves valid e)

theorem checkpoint_continuation {initial : α} {update : (Nat → Bool) → α → Act → α}
    {invariant : List Act → α → Prop}
    (genesis : invariant [] initial)
    (preserves : ∀ {H s e}, invariant H s → covered H e.addr = false →
      invariant (e :: H) (update (covered H) s e)) (H tail : List Act) :
    Valid invariant (normalize (H ++ tail))
      (advance update (checkpoint initial update H) tail) := by
  rw [normalize_append]
  exact advance_valid preserves (advance_valid preserves (empty_valid genesis) H) tail

theorem duplicate_noop (update : (Nat → Bool) → α → Act → α) (s : State α) (e : Act)
    (seen : s.coverage e.addr = true) : step update s e = s := by simp [step, seen]
end Machine

theorem exists_continuation (verb : String) (H tail : List Act) :
    Machine.Valid (Exists.Invariant verb) (normalize (H ++ tail))
      (Machine.advance (Exists.step verb)
        (Machine.checkpoint Exists.empty (Exists.step verb) H) tail) :=
  Machine.checkpoint_continuation (Exists.empty_invariant verb) Exists.step_preserves H tail

theorem count_continuation (verb : String) (H tail : List Act) :
    Machine.Valid (Count.Invariant verb) (normalize (H ++ tail))
      (Machine.advance (Count.step verb)
        (Machine.checkpoint Count.empty (Count.step verb) H) tail) :=
  Machine.checkpoint_continuation (Count.empty_invariant verb) Count.step_preserves H tail

theorem counter_continuation (increment decrement field : String) (H tail : List Act) :
    Machine.Valid (Counter.Invariant increment decrement field) (normalize (H ++ tail))
      (Machine.advance (Counter.step increment decrement field)
        (Machine.checkpoint Counter.empty (Counter.step increment decrement field) H) tail) :=
  Machine.checkpoint_continuation (Counter.empty_invariant increment decrement field)
    Counter.step_preserves H tail

theorem setUnion_continuation (verb field : String) (H tail : List Act) :
    Machine.Valid (SetUnion.Invariant verb field) (normalize (H ++ tail))
      (Machine.advance (SetUnion.step verb field)
        (Machine.checkpoint SetUnion.empty (SetUnion.step verb field) H) tail) :=
  Machine.checkpoint_continuation (SetUnion.empty_invariant verb field) SetUnion.step_preserves H tail

theorem events_continuation (verb field : String) (H tail : List Act) :
    Machine.Valid (Events.Invariant verb field) (normalize (H ++ tail))
      (Machine.advance (Events.step verb field)
        (Machine.checkpoint Events.empty (Events.step verb field) H) tail) :=
  Machine.checkpoint_continuation (Events.empty_invariant verb field) Events.step_preserves H tail

end CBCL.CheckpointData
