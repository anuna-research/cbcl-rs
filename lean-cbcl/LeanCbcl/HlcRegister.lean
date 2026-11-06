import LeanCbcl.State

/-!
SPEC-035 ADR-3502: HLC arbitration correctness over supplied candidates.
Clock components are immutable typed evidence, not proofs of honest clocks.
Signer ranks model an order-preserving image of signer byte strings. Wire/rank
correspondence, Rust execution and full-clause coverage are separate obligations.
-/
namespace CBCL.HlcRegister

/-- Four-component immutable arbitration key. -/
structure Key where
  /-- Host supplied physical milliseconds. -/
  physical : Nat
  /-- Host supplied logical component. -/
  logical : Nat
  /-- Order-preserving signer-byte rank. -/
  signer : Nat
  /-- Order-preserving content-address rank. -/
  address : Nat
  deriving DecidableEq

/-- Independent lexicographic ordering; does not invoke selection. -/
def LE (a b : Key) : Prop :=
  a.physical < b.physical ∨ a.physical = b.physical ∧
    (a.logical < b.logical ∨ a.logical = b.logical ∧
      (a.signer < b.signer ∨ a.signer = b.signer ∧ a.address ≤ b.address))
instance (a b : Key) : Decidable (LE a b) := by unfold LE; infer_instance

theorem le_refl (a : Key) : LE a a := by simp [LE]
theorem le_total (a b : Key) : LE a b ∨ LE b a := by unfold LE; omega
theorem le_trans {a b c : Key} (ab : LE a b) (bc : LE b c) : LE a c := by
  unfold LE at *; omega
theorem le_antisymm {a b : Key} (ab : LE a b) (ba : LE b a) : a = b := by
  cases a; cases b
  simp only [Key.mk.injEq]
  unfold LE at *; simp only at *; omega

/-- A selected act payload and its arbitration evidence. -/
structure Candidate (α : Type) where
  /-- Timestamp, signer and address evidence. -/
  key : Key
  /-- Immutable selected payload. -/
  value : α

/-- A repeated address identifies one immutable body. Duplicates are allowed. -/
def Consistent (T : List (Candidate α)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, a.key.address = b.key.address → a = b
/-- Declarative maximality, independent of search or fold. -/
def Greatest (T : List (Candidate α)) (a : Candidate α) : Prop :=
  a ∈ T ∧ ∀ b ∈ T, LE b.key a.key
/-- Empty or a greatest member, not equality to an interpreter. -/
def Specification (T : List (Candidate α)) : Option (Candidate α) → Prop
  | none => T = []
  | some a => Greatest T a

/-- Executable maximum search. -/
def pick : List (Candidate α) → Option (Candidate α)
  | [] => none
  | a :: rest => match pick rest with
      | none => some a
      | some b => some (if LE a.key b.key then b else a)

theorem pick_none_iff (T : List (Candidate α)) : pick T = none ↔ T = [] := by
  cases T with
  | nil => simp [pick]
  | cons a rest => cases h : pick rest <;> simp [pick, h]

theorem pick_satisfies (T : List (Candidate α)) : Specification T (pick T) := by
  induction T with
  | nil => rfl
  | cons a rest ih =>
      cases h : pick rest with
      | none =>
          have empty := (pick_none_iff rest).mp h
          subst rest
          exact ⟨by simp, fun b hb => by simp only [List.mem_singleton] at hb; subst b; exact le_refl a.key⟩
      | some b =>
          rw [h] at ih
          change Greatest rest b at ih
          simp only [pick, h]
          split
          next ab =>
            refine ⟨List.mem_cons_of_mem a ih.1, ?_⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ab
            · exact ih.2 x hx
          next ab =>
            refine ⟨List.mem_cons_self, ?_⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_refl _
            · have ba : LE b.key a.key := (le_total a.key b.key).resolve_left ab
              exact le_trans (ih.2 x hx) ba

theorem greatest_unique {T : List (Candidate α)} (consistent : Consistent T)
    {a b : Candidate α} (ha : Greatest T a) (hb : Greatest T b) : a = b := by
  have same := le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  exact consistent a ha.1 b hb.1 (congrArg Key.address same.symm)

/-- Soundness and completeness for arbitrary finite candidate sets. -/
theorem pick_correct {T : List (Candidate α)} (consistent : Consistent T)
    (result : Option (Candidate α)) : Specification T result ↔ result = pick T := by
  constructor
  · intro spec
    cases result with
    | none => rw [spec]; rfl
    | some a =>
        cases h : pick T with
        | none =>
            have empty := (pick_none_iff T).mp h
            simp [Specification, Greatest, empty] at spec
        | some b =>
            have hb := pick_satisfies T
            rw [h] at hb
            exact congrArg some (greatest_unique consistent spec hb)
  · rintro rfl; exact pick_satisfies T

/-- Order and multiplicity do not affect the selected result. -/
theorem pick_setEq {T U : List (Candidate α)} (consistent : Consistent U)
    (same : ∀ a, a ∈ T ↔ a ∈ U) : pick T = pick U := by
  apply (pick_correct consistent (pick T)).mp
  have good := pick_satisfies T
  cases h : pick T with
  | none =>
      have empty := (pick_none_iff T).mp h
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      have := (same a).mpr ha
      simp [empty] at this
  | some a =>
      rw [h] at good
      exact ⟨(same a).mp good.1, fun b hb => good.2 b ((same b).mpr hb)⟩

/-- Decorate recognized acts with immutable physical/logical/signer rank evidence. -/
def decorate (clock : CBCL.State.Act → Nat × Nat × Nat) (a : CBCL.State.Act) : Candidate CBCL.State.Act :=
  let stamp := clock a
  ⟨⟨stamp.1, stamp.2.1, stamp.2.2, a.addr⟩, a⟩

theorem decorated_consistent {A : List CBCL.State.Act} (unique : CBCL.State.NodupAddr A)
    (clock : CBCL.State.Act → Nat × Nat × Nat) : Consistent (A.map (decorate clock)) := by
  intro a ha b hb same
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  exact congrArg (decorate clock) (unique.eq_of_addr hx hy same)

/-- Arbitration cannot reintroduce another signer's or superseded own write. -/
theorem own_candidate_scope {A : List CBCL.State.Act} {v signer : String}
    {clock : CBCL.State.Act → Nat × Nat × Nat} {winner : Candidate CBCL.State.Act}
    (chosen : pick (((CBCL.State.currentOwn v A).filter (fun a => a.signer == signer)).map
      (decorate clock)) = some winner) :
    winner.value ∈ A ∧ winner.value.verb = v ∧ winner.value.signer = signer ∧
      ∀ r ∈ CBCL.State.acts v A, r.signer = winner.value.signer → winner.value.addr ∉ r.replaces := by
  have good := pick_satisfies (((CBCL.State.currentOwn v A).filter (fun a => a.signer == signer)).map (decorate clock))
  rw [chosen] at good
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp good.1
  have filtered := List.mem_filter.mp ha
  have current := CBCL.State.mem_currentOwn_iff.mp filtered.1
  have mem := List.mem_filter.mp current.1
  exact ⟨mem.1, by simpa using mem.2, by simpa using filtered.2, current.2⟩

/-- Keyed arbitration selects a surviving write of exactly the requested key. -/
theorem keyed_candidate_scope {A : List CBCL.State.Act} {v key : String}
    {delete : Option String} {x : CBCL.State.Val}
    {clock : CBCL.State.Act → Nat × Nat × Nat} {winner : Candidate CBCL.State.Act}
    (chosen : pick (((CBCL.State.current v (some key) delete A).filter (fun a => a.get key == some x)).map
      (decorate clock)) = some winner) :
    winner.value ∈ CBCL.State.current v (some key) delete A ∧ winner.value.get key = some x := by
  have good := pick_satisfies (((CBCL.State.current v (some key) delete A).filter (fun a => a.get key == some x)).map (decorate clock))
  rw [chosen] at good
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp good.1
  have filtered := List.mem_filter.mp ha
  exact ⟨filtered.1, by simpa using filtered.2⟩

/-- Full arbitration specification for all admitted writes of the selected verb. -/
theorem register_correct {A : List CBCL.State.Act} (unique : CBCL.State.NodupAddr A)
    (v : String) (clock : CBCL.State.Act → Nat × Nat × Nat) (result) :
    Specification ((CBCL.State.acts v A).map (decorate clock)) result ↔
      result = pick ((CBCL.State.acts v A).map (decorate clock)) :=
  pick_correct (decorated_consistent (unique.acts v) clock) result

/-- Full greatest-surviving-own-write specification, not just membership. -/
theorem own_correct {A : List CBCL.State.Act} (unique : CBCL.State.NodupAddr A)
    (v signer : String) (clock : CBCL.State.Act → Nat × Nat × Nat) (result) :
    Specification (((CBCL.State.currentOwn v A).filter (fun a => a.signer == signer)).map (decorate clock)) result ↔
      result = pick (((CBCL.State.currentOwn v A).filter (fun a => a.signer == signer)).map (decorate clock)) :=
  pick_correct (decorated_consistent ((unique.currentOwn v).filter _) clock) result

/-- Full greatest-surviving-keyed-write specification, including deletion source. -/
theorem keyed_correct {A : List CBCL.State.Act} (unique : CBCL.State.NodupAddr A)
    (v key : String) (delete : Option String) (x : CBCL.State.Val)
    (clock : CBCL.State.Act → Nat × Nat × Nat) (result) :
    Specification (((CBCL.State.current v (some key) delete A).filter (fun a => a.get key == some x)).map (decorate clock)) result ↔
      result = pick (((CBCL.State.current v (some key) delete A).filter (fun a => a.get key == some x)).map (decorate clock)) :=
  pick_correct (decorated_consistent ((unique.current v (some key) delete).filter _) clock) result

end CBCL.HlcRegister
