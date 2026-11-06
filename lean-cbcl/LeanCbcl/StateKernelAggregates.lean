import LeanCbcl.StateKernelQueries

/-! SPEC-036 finite map statistics, independent of enumeration order. -/
namespace CBCL.StateKernelAggregates
open CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries

/-- Arbitrary duplicate-free enumeration of a finite key predicate. -/
def Enumeration (P : Val → Prop) (keys : List Val) : Prop :=
  keys.Nodup ∧ ∀ key, key ∈ keys ↔ P key
/-- Cardinality is independent of the chosen valid enumeration. -/
def KeyCount (P : Val → Prop) (n : Nat) : Prop :=
  ∃ keys, Enumeration P keys ∧ n = keys.length
/-- Exact integer total over any valid enumeration, not an implementation fold. -/
def KeyTotal (P : Val → Prop) (number : Val → Int) (total : Int) : Prop :=
  ∃ keys, Enumeration P keys ∧ total = (keys.map number).sum

/-- Logical scalar projection; absent cells contribute no histogram value. -/
def ProjectedValue (cell : Cell) (v : Val) : Prop :=
  cell = .value v ∨ ∃ signer, cell = .event signer v
/-- Concrete scalar/event access; not an aggregate. -/
def cellScalar : Cell → Option Val
  | .absent => none
  | .value v => some v
  | .event _ v => some v
/-- Numeric scalar/event access; nonnumbers and absence contribute zero. -/
def cellNumber : Cell → Int
  | .value (.int n) | .event _ (.int n) => n
  | _ => 0

/-- Independent numeric meaning; nonnumeric payloads and absence contribute zero. -/
def CellNumberMeaning (cell : Cell) (n : Int) : Prop :=
  (∃ value, cell = .value (.int value) ∧ n = value) ∨
  (∃ signer value, cell = .event signer (.int value) ∧ n = value) ∨
  ((∀ value, cell ≠ .value (.int value)) ∧
   (∀ signer value, cell ≠ .event signer (.int value)) ∧ n = 0)

/-- Executable numeric projection satisfies the independent relation. -/
theorem cell_number_correct (cell : Cell) : CellNumberMeaning cell (cellNumber cell) := by
  cases cell with
  | absent => simp [CellNumberMeaning, cellNumber]
  | value v => cases v <;> simp [CellNumberMeaning, cellNumber]
  | event signer v => cases v <;> simp [CellNumberMeaning, cellNumber]

theorem cell_scalar_correct (cell : Cell) (v : Val) :
    cellScalar cell = some v ↔ ProjectedValue cell v := by
  cases cell <;> simp [cellScalar, ProjectedValue, eq_comm]

/-- Concrete histogram counts keys, never messages inside a group. -/
def histogram (m : FiniteMap) (v : Val) : Nat :=
  (m.keys.filter (fun key => cellScalar (m.read key) == some v)).length
/-- Concrete support omits absent payloads and coalesces equal scalar values. -/
def histogramKeys (m : FiniteMap) : List Val :=
  uniqueKeys (m.keys.filterMap (fun key => cellScalar (m.read key)))
/-- Concrete map sum is a left fold over the supported keys. -/
def mapSum (m : FiniteMap) : Int :=
  m.keys.foldl (fun acc key => acc + cellNumber (m.read key)) 0

/-- Independent histogram graph and exact support. -/
def HistogramMeaning (m : FiniteMap) (counts : Val → Nat) (keys : List Val) : Prop :=
  keys.Nodup ∧
  (∀ v, v ∈ keys ↔ ∃ key ∈ m.keys, ProjectedValue (m.read key) v) ∧
  ∀ v, KeyCount (fun key => key ∈ m.keys ∧ ProjectedValue (m.read key) v) (counts v)
/-- Independent map sum graph. Event payloads use the same numeric access as scalars. -/
def SumMeaning (m : FiniteMap) (total : Int) : Prop :=
  ∃ number : Val → Int, (∀ key ∈ m.keys, CellNumberMeaning (m.read key) (number key)) ∧
    KeyTotal (fun key => key ∈ m.keys) number total

theorem histogram_correct (m : FiniteMap) (unique : m.keys.Nodup) :
    HistogramMeaning m (histogram m) (histogramKeys m) := by
  refine ⟨uniqueKeys_nodup _, ?_, ?_⟩
  · intro v
    simp only [histogramKeys, uniqueKeys_member, List.mem_filterMap, cell_scalar_correct]
  · intro v
    refine ⟨m.keys.filter (fun key => cellScalar (m.read key) == some v), ?_, rfl⟩
    refine ⟨unique.sublist List.filter_sublist, ?_⟩
    intro key
    simp only [List.mem_filter, beq_iff_eq, cell_scalar_correct]

theorem map_sum_correct (m : FiniteMap) (unique : m.keys.Nodup) : SumMeaning m (mapSum m) := by
  refine ⟨fun key => cellNumber (m.read key), fun key _ => cell_number_correct (m.read key),
    m.keys, ⟨unique, fun _ => Iff.rfl⟩, ?_⟩
  simp only [mapSum, List.sum_eq_foldl]
  rw [List.foldl_map]

/-- Equal finite key sets have equal cardinalities. -/
theorem key_count_unique {P : Val → Prop} {a b : Nat}
    (ha : KeyCount P a) (hb : KeyCount P b) : a = b := by
  obtain ⟨A, ⟨na, ma⟩, rfl⟩ := ha
  obtain ⟨B, ⟨nb, mb⟩, rfl⟩ := hb
  exact ((List.perm_ext_iff_of_nodup na nb).mpr (fun x => (ma x).trans (mb x).symm)).length_eq

/-- Permuting exact integer summands preserves their total. -/
theorem sum_perm {A B : List Int} (p : A.Perm B) : A.sum = B.sum := by
  simp only [List.sum_eq_foldl]
  exact p.foldl_eq' (fun _ _ _ _ _ => by omega) 0

theorem key_total_unique {P : Val → Prop} {f : Val → Int} {a b : Int}
    (ha : KeyTotal P f a) (hb : KeyTotal P f b) : a = b := by
  obtain ⟨A, ⟨na, ma⟩, rfl⟩ := ha
  obtain ⟨B, ⟨nb, mb⟩, rfl⟩ := hb
  exact sum_perm (((List.perm_ext_iff_of_nodup na nb).mpr (fun x => (ma x).trans (mb x).symm)).map f)

/-- The independent numeric-cell graph fixes exactly one integer. -/
theorem cell_number_complete (cell : Cell) (n : Int) :
    CellNumberMeaning cell n ↔ n = cellNumber cell := by
  cases cell with
  | absent => simp [CellNumberMeaning, cellNumber]
  | value v => cases v <;> simp [CellNumberMeaning, cellNumber]
  | event signer v => cases v <;> simp [CellNumberMeaning, cellNumber, eq_comm]

/-- The independent sum graph fixes exactly one observation. -/
theorem sum_meaning_unique (m : FiniteMap) {a b : Int}
    (ha : SumMeaning m a) (hb : SumMeaning m b) : a = b := by
  obtain ⟨fa, na, A, ⟨ua, ma⟩, rfl⟩ := ha
  obtain ⟨fb, nb, B, ⟨ub, mb⟩, rfl⟩ := hb
  have numeric : ∀ k ∈ m.keys, fa k = fb k := by
    intro k hk
    exact ((cell_number_complete _ _).mp (na k hk)).trans
      ((cell_number_complete _ _).mp (nb k hk)).symm
  have same : A.map fa = A.map fb := List.map_congr_left (fun k hk => numeric k ((ma k).mp hk))
  rw [same]
  exact sum_perm (((List.perm_ext_iff_of_nodup ua ub).mpr
    (fun k => (ma k).trans (mb k).symm)).map fb)

/-- Histograms have unique counts and exact support, independently of key order. -/
theorem histogram_meaning_unique (m : FiniteMap) {a b : Val → Nat} {A B : List Val}
    (ha : HistogramMeaning m a A) (hb : HistogramMeaning m b B) :
    (∀ k, k ∈ A ↔ k ∈ B) ∧ a = b := by
  refine ⟨fun k => (ha.2.1 k).trans (hb.2.1 k).symm, ?_⟩
  funext k
  exact key_count_unique (ha.2.2 k) (hb.2.2 k)

end CBCL.StateKernelAggregates
