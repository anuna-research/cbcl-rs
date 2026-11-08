import LeanCbcl.StateCausalRank

/-! Completeness of the checked Kahn witness for content-consistent finite
causal histories. No semantic address ordering or delivery-order premise.
The theorem concerns present edges; predecessor closure is checked separately. -/
namespace CBCL.StateCausalCheckComplete
open State StateLift StateCausalRank

/-- Every nonempty finite history contains a minimum-rank vertex. -/
theorem minimum_rank (history : List Act) (rank : Act → Nat) (nonempty : history ≠ []) :
    ∃ root ∈ history, ∀ act ∈ history, rank root ≤ rank act := by
  induction history with
  | nil => contradiction
  | cons head rest ih =>
    cases rest with
    | nil => exact ⟨head,by simp,by simp⟩
    | cons next tail =>
      obtain ⟨root,member,smallest⟩ := ih (by simp)
      by_cases lower : rank head ≤ rank root
      · refine ⟨head,by simp,?_⟩
        intro act inside
        rcases List.mem_cons.mp inside with same | later
        · subst act; exact Nat.le_refl _
        · exact Nat.le_trans lower (smallest act later)
      · refine ⟨root,List.mem_cons_of_mem _ member,?_⟩
        intro act inside
        rcases List.mem_cons.mp inside with same | later
        · subst act; omega
        · exact smallest act later

/-- A minimum causal rank is ready regardless of delivery order. -/
theorem ready_exists (history : List Act) (ranked : StateExecutableFreeze.Ranked history) (nonempty : history ≠ []) :
    ∃ root ∈ history, ready history root = true := by
  obtain ⟨rank,ordered⟩ := ranked
  obtain ⟨root,member,smallest⟩ := minimum_rank history rank nonempty
  refine ⟨root,member,?_⟩
  simp only [ready,List.all_eq_true]
  intro address edge
  have absent : history.any (fun parent => parent.addr == address) = false := by
    apply List.any_eq_false.mpr
    intro parent present
    intro same
    have addressEqual : parent.addr = address := by simpa using same
    have causal := ordered root member parent present (addressEqual ▸ edge)
    have minimum := smallest parent present
    omega
  simp [absent]

/-- Removing all duplicate deliveries of a selected vertex decreases fuel. -/
theorem remove_shorter (history : List Act) (root : Act) (member : root ∈ history) :
    (history.filter (fun act => act != root)).length < history.length := by
  have bound := List.length_filter_le (fun act => act != root) history
  have different : (history.filter (fun act => act != root)).length ≠ history.length := by
    intro equal
    have all := List.length_filter_eq_length_iff.mp equal
    have self := all root member
    simp at self
  omega

/-- The accumulated prefix is appended without changing the produced suffix. -/
theorem order_prefix (fuel : Nat) (pending ordered : List Act) :
    orderFuel fuel pending ordered = (orderFuel fuel pending []).map (ordered ++ ·) := by
  induction fuel generalizing pending ordered with
  | zero => cases pending <;> simp [orderFuel]
  | succ fuel ih =>
    cases pending with
    | nil => simp [orderFuel]
    | cons head tail =>
      cases selected : (head::tail).find? (ready (head::tail)) with
      | none => simp [orderFuel,selected]
      | some root =>
        simp only [orderFuel,selected]
        simp only [List.nil_append]
        rw [ih _ (ordered ++ [root]),ih _ [root]]
        simp [Option.map_map,List.append_assoc,Function.comp_def]

/-- A successful explicit position-rank proof is exactly the Boolean check. -/
theorem check_of_positions (history : List Act)
    (ordered : StateCausalRank.RankedBy history (position history)) : check history = true := by
  apply List.all_eq_true.mpr
  intro child childIn
  apply List.all_eq_true.mpr
  intro parent parentIn
  by_cases edge : parent.addr ∈ child.preds
  · simp [edge,ordered child childIn parent parentIn edge]
  · simp [edge]

/-- Ready selection forbids every edge to a vertex still pending. -/
theorem ready_no_parent (pending : List Act) (root : Act) (selected : ready pending root = true)
    (parent : Act) (member : parent ∈ pending) : parent.addr ∉ root.preds := by
  intro edge
  have forbidden := List.all_eq_true.mp selected parent.addr edge
  have present : pending.any (fun act => act.addr == parent.addr) = true :=
    List.any_eq_true.mpr ⟨parent,member,by simp⟩
  simp [present] at forbidden

/-- Prepending a fresh ready vertex preserves the explicit position checker. -/
theorem check_cons (root : Act) (rest : List Act) (fresh : root.addr ∉ rest.map Act.addr)
    (noSelf : root.addr ∉ root.preds) (noBackward : ∀ parent ∈ rest, parent.addr ∉ root.preds)
    (checked : check rest = true) : check (root::rest) = true := by
  apply check_of_positions
  intro child childIn parent parentIn edge
  rcases List.mem_cons.mp childIn with same | childIn
  · subst child
    rcases List.mem_cons.mp parentIn with same | parentIn
    · subst parent; exact False.elim (noSelf edge)
    · exact False.elim (noBackward parent parentIn edge)
  · have childDifferent : root.addr ≠ child.addr := by
      intro same
      exact fresh (List.mem_map.mpr ⟨child,childIn,same.symm⟩)
    rcases List.mem_cons.mp parentIn with same | parentIn
    · subst parent
      simp [position,List.idxOf_cons,beq_eq_false_iff_ne.mpr childDifferent]
    · have parentDifferent : root.addr ≠ parent.addr := by
        intro same
        exact fresh (List.mem_map.mpr ⟨parent,parentIn,same.symm⟩)
      have lower := check_sound rest checked child childIn parent parentIn edge
      simpa [position,List.idxOf_cons,beq_eq_false_iff_ne.mpr childDifferent,beq_eq_false_iff_ne.mpr parentDifferent] using lower

/-- The actual Kahn implementation constructs exact vertex coverage and a
checked unique-address order for every content-consistent ranked history. -/
theorem order_complete (fuel : Nat) (history : List Act)
    (ranked : StateExecutableFreeze.Ranked history)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b)
    (enough : history.length ≤ fuel) :
    ∃ order, orderFuel fuel history [] = some order ∧ SetEq order history ∧ NodupAddr order ∧ check order = true := by
  induction fuel generalizing history with
  | zero =>
    have empty : history = [] := List.length_eq_zero_iff.mp (by omega)
    subst history
    exact ⟨[],rfl,fun _ => Iff.rfl,by simp [NodupAddr],rfl⟩
  | succ fuel ih =>
    cases history with
    | nil => exact ⟨[],rfl,fun _ => Iff.rfl,by simp [NodupAddr],rfl⟩
    | cons head rest =>
      let pending := head::rest
      obtain ⟨readyRoot,readyMember,isReady⟩ := ready_exists pending ranked (by simp [pending])
      cases selected : pending.find? (ready pending) with
      | none => exact False.elim ((List.find?_eq_none.mp selected readyRoot readyMember) isReady)
      | some root =>
        have rootMember : root ∈ pending := List.mem_of_find?_eq_some selected
        have rootReady : ready pending root = true := List.find?_some selected
        let remaining := pending.filter (fun act => act != root)
        have inside : ∀ act ∈ remaining, act ∈ pending := fun _ member => (List.mem_filter.mp member).1
        have remainingRanked : StateExecutableFreeze.Ranked remaining := by
          obtain ⟨rank,ordered⟩ := ranked
          exact ⟨rank,fun child childIn parent parentIn edge => ordered child (inside child childIn) parent (inside parent parentIn) edge⟩
        have remainingConsistent : ∀ a ∈ remaining, ∀ b ∈ remaining, a.addr = b.addr → a = b := by
          intro a memberA b memberB equal
          exact consistent a (inside a memberA) b (inside b memberB) equal
        have smaller := remove_shorter pending root rootMember
        have remainingEnough : remaining.length ≤ fuel := by
          change remaining.length < pending.length at smaller
          have fullBound : pending.length ≤ fuel+1 := enough
          omega
        obtain ⟨tail,ran,same,unique,checked⟩ := ih remaining remainingRanked remainingConsistent remainingEnough
        have tailInside : ∀ act ∈ tail, act ∈ pending := fun act member => inside act ((same act).mp member)
        have fresh : root.addr ∉ tail.map Act.addr := by
          intro member
          obtain ⟨act,present,equal⟩ := List.mem_map.mp member
          have remainingMember := (same act).mp present
          have different : act ≠ root := by simpa [remaining] using (List.mem_filter.mp remainingMember).2
          exact different (consistent act (tailInside act present) root rootMember equal)
        refine ⟨root::tail,?_,?_,?_,?_⟩
        · change orderFuel (fuel+1) pending [] = some (root::tail)
          simp only [pending,orderFuel] at selected ⊢
          rw [selected]
          change orderFuel fuel remaining [root] = some (root::tail)
          rw [order_prefix fuel _ [root],ran]
          rfl
        · intro act
          constructor
          · intro member
            rcases List.mem_cons.mp member with equal | later
            · exact equal ▸ rootMember
            · exact tailInside act later
          · intro member
            by_cases equal : act = root
            · exact List.mem_cons.mpr (.inl equal)
            · apply List.mem_cons.mpr
              apply Or.inr
              apply (same act).mpr
              exact List.mem_filter.mpr ⟨member,by simpa using equal⟩
        · simpa [NodupAddr] using And.intro fresh unique
        · exact check_cons root tail fresh (ready_no_parent pending root rootReady root rootMember)
            (fun parent member => ready_no_parent pending root rootReady parent (tailInside parent member)) checked

/-- The checker accepts every content-consistent history admitting a causal
rank, including arbitrary semantic addresses and duplicate/reversed delivery. -/
theorem causalCheck_complete (history : List Act) (ranked : StateExecutableFreeze.Ranked history)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b) : causalCheck history = true := by
  obtain ⟨order,ran,same,_,checked⟩ := order_complete (history.length+1) history ranked consistent (by omega)
  simp only [causalCheck,ran,Bool.and_eq_true]
  refine ⟨⟨?_,?_⟩,checked⟩
  · apply List.all_eq_true.mpr
    intro act member
    exact List.contains_iff_mem.mpr ((same act).mpr member)
  · apply List.all_eq_true.mpr
    intro act member
    exact List.contains_iff_mem.mpr ((same act).mp member)

/-- Recognition is equivalent to a separate causal rank on consistent inputs. -/
theorem causalCheck_iff (history : List Act)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b) :
    causalCheck history = true ↔ StateExecutableFreeze.Ranked history :=
  ⟨causalCheck_sound history,fun ranked => causalCheck_complete history ranked consistent⟩

/-- Causal-rank existence depends only on accepted vertices, never delivery. -/
theorem ranked_setEq (left right : List Act) (same : SetEq left right) :
    StateExecutableFreeze.Ranked left ↔ StateExecutableFreeze.Ranked right := by
  constructor
  · rintro ⟨rank,ordered⟩
    exact ⟨rank,fun child childIn parent parentIn edge =>
      ordered child ((same child).mpr childIn) parent ((same parent).mpr parentIn) edge⟩
  · rintro ⟨rank,ordered⟩
    exact ⟨rank,fun child childIn parent parentIn edge =>
      ordered child ((same child).mp childIn) parent ((same parent).mp parentIn) edge⟩

/-- Recognition itself is invariant under duplicate and reordered delivery. -/
theorem causalCheck_setEq (left right : List Act) (same : SetEq left right)
    (leftConsistent : ∀ a ∈ left, ∀ b ∈ left, a.addr = b.addr → a = b)
    (rightConsistent : ∀ a ∈ right, ∀ b ∈ right, a.addr = b.addr → a = b) :
    causalCheck left = causalCheck right := by
  have equivalent : causalCheck left = true ↔ causalCheck right = true :=
    (causalCheck_iff left leftConsistent).trans ((ranked_setEq left right same).trans (causalCheck_iff right rightConsistent).symm)
  cases leftResult : causalCheck left <;> cases rightResult : causalCheck right <;> simp_all

end CBCL.StateCausalCheckComplete
