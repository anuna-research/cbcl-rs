import LeanCbcl.StateKernelClause
import LeanCbcl.StateRefinement

/-! SPEC-037 equal-set convergence; evidence ports are shared replica context. -/
namespace CBCL.StateKernelSEC
open CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries
open CBCL.StateKernelAggregates CBCL.StateKernelExtensions CBCL.StateKernel CBCL.StateKernelClause

/-- Observation equality disregards enumeration order and unsupported map reads. -/
def Equivalent : Observation → Observation → Prop
  | .cell a, .cell b => a = b
  | .boolean a, .boolean b => a = b
  | .integer a, .integer b => a = b
  | .values a, .values b => a = b
  | .map a, .map b => MapEquivalent a b
  | .valueMap a, .valueMap b => ValueMapEquivalent a b
  | .histogram A a, .histogram B b => (∀ k, k ∈ A ↔ k ∈ B) ∧ a = b
  | .resource a, .resource b => a = b
  | _, _ => False

/-- One shared immutable context and evidence provider for all compared replicas. -/
structure Context where
  /-- Installed opener. -/
  opener : String
  /-- Immutable clock decoding. -/
  clock : Clock
  /-- Immutable signer order. -/
  rank : SignerRank
  /-- Pinned thread. -/
  thread : Nat
  /-- Expanded protocol bounds. -/
  limit : String → Nat
  /-- Reconstructed causal evidence. -/
  causal : List Act → Repeat.Store
  /-- Delegated verifier outcomes, not assumed finalization. -/
  resource : List Act → String → ResourceInput
  /-- Reconstruction respects accepted sets. -/
  causal_ext : ∀ A B, SetEq A B → causal A = causal B
  /-- The shared verifier independently obeys set extensionality. -/
  resource_ext : ∀ A B, SetEq A B → resource A = resource B

/-- Interpret a replica history in the fixed shared context. -/
def Context.input (c : Context) (A : List Act) : Input :=
  ⟨A, c.opener, c.clock, c.rank, c.causal A, c.thread, c.limit, c.resource A⟩

/-- Domain filtering preserves set equality. -/
theorem admitted_setEq {A B : List Act} (ua : NodupAddr A) (ub : NodupAddr B)
    (same : SetEq A B) (domains : List Domain) :
    SetEq (admitted domains A) (admitted domains B) := by
  intro a
  simp only [admitted, List.mem_filter, same a, allowedOf_setEq ua ub same]

/-- Nested selections preserve source membership equality. -/
theorem select_setEq {A B : List Act} (same : SetEq A B) (s : Selection) :
    SetEq (select A s) (select B s) := by
  intro a
  rw [select_correct, select_correct]
  exact selected_congr same s a

/-- Address and HLC arbitration converge on equal eligible sets. -/
theorem choose_setEq {A B : List Act} (ub : NodupAddr B) (same : SetEq A B)
    (clock : Clock) (rank : SignerRank) (policy : Policy) :
    choose clock rank policy A = choose clock rank policy B := by
  apply (choose_correct ub clock rank policy _).mp
  exact (choice_congr same clock rank policy _).mp (choose_satisfies _ _ _ _)

/-- Scalar and event maps converge extensionally. -/
theorem map_setEq {A B : List Act} (ub : NodupAddr B) (same : SetEq A B)
    (clock : Clock) (rank : SignerRank) (plan : MapPlan) :
    MapEquivalent (evalMap clock rank A plan) (evalMap clock rank B plan) := by
  exact ((map_complete ub clock rank plan _).mp
    ((map_meaning_congr same clock rank plan _).mp (map_correct _ _ _ _))).2

/-- Conflict-preserving maps converge extensionally. -/
theorem values_map_setEq {A B : List Act} (same : SetEq A B)
    (s : Selection) (key field : String) :
    ValueMapEquivalent (evalValuesBy A s key field) (evalValuesBy B s key field) := by
  apply ((values_by_complete B s key field _).mp ?_).2
  have good := values_by_correct A s key field
  simpa only [ValueMapMeaning, selected_congr same] using good

/-- Equal exact key enumerations differ only by permutation. -/
theorem map_keys_perm {a b : FiniteMap} (ua : a.keys.Nodup) (ub : b.keys.Nodup)
    (same : MapEquivalent a b) : a.keys.Perm b.keys :=
  (List.perm_ext_iff_of_nodup ua ub).mpr same.1

/-- Histograms depend only on supported cells. -/
theorem histogram_equivalent {a b : FiniteMap} (ua : a.keys.Nodup) (ub : b.keys.Nodup)
    (same : MapEquivalent a b) :
    (∀ v, v ∈ histogramKeys a ↔ v ∈ histogramKeys b) ∧ histogram a = histogram b := by
  have perm := map_keys_perm ua ub same
  constructor
  · intro v
    simp only [histogramKeys, uniqueKeys_member, List.mem_filterMap]
    constructor
    · rintro ⟨k, hk, value⟩
      exact ⟨k, (same.1 k).mp hk, by rw [← same.2 k hk]; exact value⟩
    · rintro ⟨k, hk, value⟩
      have ha := (same.1 k).mpr hk
      exact ⟨k, ha, by rw [same.2 k ha]; exact value⟩
  · funext v
    unfold histogram
    have equal : a.keys.filter (fun k => cellScalar (a.read k) == some v) =
        a.keys.filter (fun k => cellScalar (b.read k) == some v) := by
      apply List.filter_congr
      intro k hk
      rw [same.2 k hk]
    rw [equal]
    exact (perm.filter _).length_eq

/-- Exact map sums ignore enumeration order and unsupported reads. -/
theorem sum_equivalent {a b : FiniteMap} (ua : a.keys.Nodup) (ub : b.keys.Nodup)
    (same : MapEquivalent a b) : mapSum a = mapSum b := by
  have tosum (m : FiniteMap) : mapSum m = (m.keys.map (fun k => cellNumber (m.read k))).sum := by
    simp only [mapSum, List.sum_eq_foldl, List.foldl_map]
  rw [tosum, tosum]
  have equal : a.keys.map (fun k => cellNumber (a.read k)) =
      a.keys.map (fun k => cellNumber (b.read k)) := by
    apply List.map_congr_left
    intro k hk
    rw [same.2 k hk]
  rw [equal]
  exact sum_perm ((map_keys_perm ua ub same).map _)

/-- Every expression constructor converges when accepted sets agree. -/
theorem strong_convergence (c : Context) (domains : List Domain) (expression : Expr)
    {A B : List Act} (ua : NodupAddr A) (ub : NodupAddr B) (same : SetEq A B) :
    Equivalent (evaluate (c.input A) domains expression) (evaluate (c.input B) domains expression) := by
  have data := admitted_setEq ua ub same domains
  have uniqueA := admitted_unique ua domains
  have uniqueB := admitted_unique ub domains
  have selections := select_setEq data
  cases expression with
  | scalar s p f =>
      exact congrArg (project f false)
        (choose_setEq (select_unique uniqueB s) (selections s) c.clock c.rank p)
  | existsRule s =>
      change (!(select (admitted domains A) s).isEmpty) = (!(select (admitted domains B) s).isEmpty)
      have empty : (select (admitted domains A) s).isEmpty = (select (admitted domains B) s).isEmpty := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.isEmpty_iff]
        constructor <;> intro h
        · apply List.eq_nil_iff_forall_not_mem.mpr
          intro a member
          have := (selections s a).mpr member
          simp [h] at this
        · apply List.eq_nil_iff_forall_not_mem.mpr
          intro a member
          have := (selections s a).mp member
          simp [h] at this
      rw [empty]
  | count s => exact congrArg Int.ofNat (size_setEq (select_unique uniqueA s) (select_unique uniqueB s) (selections s))
  | distinct s f => exact funext (has_setEq (selections s) f)
  | mapped plan => exact map_setEq uniqueB data c.clock c.rank plan
  | valuesBy s k f => exact values_map_setEq data s k f
  | counter inc dec f =>
      change sumField f (select (admitted domains A) inc) - sumField f (select (admitted domains A) dec) =
        sumField f (select (admitted domains B) inc) - sumField f (select (admitted domains B) dec)
      rw [sumField_setEq (select_unique uniqueA inc) (select_unique uniqueB inc) (selections inc) f,
        sumField_setEq (select_unique uniqueA dec) (select_unique uniqueB dec) (selections dec) f]
  | histogram plan =>
      exact histogram_equivalent (uniqueKeys_nodup _) (uniqueKeys_nodup _)
        (map_setEq uniqueB data c.clock c.rank plan)
  | sum plan =>
      exact sum_equivalent (uniqueKeys_nodup _) (uniqueKeys_nodup _)
        (map_setEq uniqueB data c.clock c.rank plan)
  | progress verb =>
      change Int.ofNat (protocolProgress (c.causal A) c.thread verb (c.limit verb) A) =
        Int.ofNat (protocolProgress (c.causal B) c.thread verb (c.limit verb) B)
      rw [c.causal_ext A B same]
      apply congrArg Int.ofNat
      apply progress_unique (progress_correct _ _ _ _ _)
      have good := progress_correct (c.causal B) c.thread verb (c.limit verb) B
      intro upper
      rw [good upper]
      constructor
      · intro h a ha; exact h a ((same a).mp ha)
      · intro h a ha; exact h a ((same a).mpr ha)
  | bounded name =>
      change resourceObserve (c.resource A name) = resourceObserve (c.resource B name)
      rw [c.resource_ext A B same]

/-- Arbitrary compiled clauses converge in declaration order. -/
theorem clause_strong_convergence (c : Context) (compiled : Compiled)
    {A B : List Act} (ua : NodupAddr A) (ub : NodupAddr B) (same : SetEq A B) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ Equivalent a.2 b.2)
      (evaluateFields (c.input A) compiled.domains compiled.fields)
      (evaluateFields (c.input B) compiled.domains compiled.fields) := by
  induction compiled.fields with
  | nil => exact .nil
  | cons field rest ih => exact .cons ⟨rfl, strong_convergence c compiled.domains field.2 ua ub same⟩ ih

/-- Immutable accepted-store union reuses the existing duplicate-suppressing insertion. -/
def merge (incoming current : List Act) : List Act := incoming.foldr insertAct current

/-- Store merge is exactly set union; no delivery ordering is retained semantically. -/
theorem merge_setEq (A B : List Act) : SetEq (merge A B) (A ++ B) := by
  induction A with
  | nil => intro a; rfl
  | cons a rest ih =>
      intro b
      rw [merge, List.foldr_cons, insertAct_setEq]
      simp only [List.cons_append, List.mem_cons]
      exact or_congr Iff.rfl (ih b)

/-- Membership in merged histories is membership in either input. -/
@[simp] theorem mem_merge (a : Act) (A B : List Act) :
    a ∈ merge A B ↔ a ∈ A ∨ a ∈ B := by
  rw [merge_setEq A B a, List.mem_append]

/-- Union is associative at the accepted-set boundary. -/
theorem merge_associative (A B C : List Act) :
    SetEq (merge (merge A B) C) (merge A (merge B C)) := by
  intro a
  simp only [mem_merge]
  exact or_assoc

/-- Union is commutative at the accepted-set boundary. -/
theorem merge_commutative (A B : List Act) : SetEq (merge A B) (merge B A) := by
  intro a
  simp only [mem_merge]
  exact or_comm

/-- Replaying a complete history has no additional accepted-set effect. -/
theorem merge_idempotent (A : List Act) : SetEq (merge A A) A := by
  intro a
  simp only [mem_merge, or_self]

/-- A repeated accepted act leaves every compiled observation unchanged. -/
theorem duplicate_observation (c : Context) (clause : Compiled) (A : List Act)
    (unique : NodupAddr A) (a : Act) (member : a ∈ A) :
    List.Forall₂ (fun x y => x.1 = y.1 ∧ Equivalent x.2 y.2)
      (evaluateFields (c.input (insertAct a A)) clause.domains clause.fields)
      (evaluateFields (c.input A) clause.domains clause.fields) := by
  simpa only [insertAct, if_pos member] using
    clause_strong_convergence c clause unique unique (fun _ => Iff.rfl)

end CBCL.StateKernelSEC
