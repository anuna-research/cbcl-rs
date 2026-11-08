import LeanCbcl.StateFiniteCausalRank

/-! Executable finite causal queries for the live oracle and scope pool.
Finite rank compression bounds backward search independently of semantic
addresses, input order and duplicate delivery. -/
set_option autoImplicit false
namespace CBCL.StateExecutableFreeze
open State StateLift StateLVar

/-- A separate causal rank decreases on every backward present edge. -/
def RankedBy (A : List Act) (rank : Act → Nat) : Prop := ∀ child ∈ A, ∀ parent ∈ A,
  parent.addr ∈ child.preds → rank parent < rank child

/-- Finite causal histories admit a rank; semantic addresses need not rank edges.
The witness is proof-only and never renumbers acts or changes HLC tie keys. -/
def Ranked (A : List Act) : Prop := ∃ rank : Act → Nat, RankedBy A rank

/-- Input recognition checks every cited predecessor identity decreases. -/
def rankedCheck (A : List Act) : Bool := A.all (fun child => child.preds.all (fun parent => decide (parent < child.addr)))

/-- A successful executable rank check supplies the finite-search premise. -/
theorem rankedCheck_sound (A : List Act) (checked : rankedCheck A = true) : Ranked A := by
  refine ⟨Act.addr,?_⟩
  intro child member parent _ edge
  have childChecked := List.all_eq_true.mp checked child member
  exact of_decide_eq_true (List.all_eq_true.mp childChecked parent.addr edge)

/-- Transitivity of the existing immutable-world ancestor relation. -/
theorem ancestor_trans {world : Act → Prop} {a b c : Act}
    (left : Ancestor world a b) (right : Ancestor world b c) : Ancestor world a c := by
  induction left with
  | self _ => exact right
  | step valid edge _ ih => exact .step valid edge (ih right)

/-- Every nontrivial ancestor path ends at a present immediate predecessor. -/
theorem ancestor_last {A : List Act} {a f : Act} (path : Ancestor (fun act => act ∈ A) a f) :
    a = f ∨ ∃ parent ∈ A, parent.addr ∈ f.preds ∧ Ancestor (fun act => act ∈ A) a parent := by
  induction path with
  | self _ => exact Or.inl rfl
  | @step a p f valid edge path ih =>
    rcases ih with same | ⟨parent,member,last,earlier⟩
    · subst p; exact Or.inr ⟨a,valid,edge,.self valid⟩
    · exact Or.inr ⟨parent,member,last,.step valid edge earlier⟩

-- SIMPLIFY: oracle DAGs have at most 16 generated non-root nodes. Backward
-- search can revisit shared paths exponentially; memoize reachability before
-- increasing that profile bound. This reference is not the native NFR-3800 cost model.
/-- Bounded backward path enumeration, independent of Rust's topological walk. -/
def reachable : Nat → List Act → Act → Act → Bool
  | 0, _, _, _ => false
  | fuel + 1, A, a, f => A.contains f &&
      (a == f || A.any (fun parent => f.preds.contains parent.addr && reachable fuel A a parent))

/-- Every successful finite search is an actual inductive ancestor path. -/
theorem reachable_sound (fuel : Nat) (A : List Act) (a f : Act)
    (found : reachable fuel A a f = true) : Ancestor (fun act => act ∈ A) a f := by
  induction fuel generalizing f with
  | zero => simp [reachable] at found
  | succ fuel ih =>
    simp only [reachable,Bool.and_eq_true,List.contains_iff_mem,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at found
    rcases found with ⟨member,same | ⟨parent,present,edge,earlier⟩⟩
    · subst a; exact .self member
    · have edge : parent.addr ∈ f.preds := by simpa using edge
      exact ancestor_trans (ih parent earlier) (.step present edge (.self member))

/-- A separate causal rank bounds every path; no successful path is truncated. -/
theorem reachable_complete (fuel : Nat) (A : List Act) (rank : Act → Nat) (ranked : RankedBy A rank) (a f : Act)
    (member : f ∈ A) (path : Ancestor (fun act => act ∈ A) a f) (bound : rank f < fuel) :
    reachable fuel A a f = true := by
  induction fuel generalizing f with
  | zero => omega
  | succ fuel ih =>
    simp only [reachable,Bool.and_eq_true,List.contains_iff_mem,Bool.or_eq_true,beq_iff_eq,List.any_eq_true]
    refine ⟨member,?_⟩
    rcases ancestor_last path with same | ⟨parent,present,edge,earlier⟩
    · exact Or.inl same
    · have lower := ranked f member parent present edge
      exact Or.inr ⟨parent,present,by simpa using edge,ih parent present earlier (by omega)⟩

/-- History length bounds search independently of semantic address magnitude. -/
def ancestor (A : List Act) (a f : Act) : Bool := reachable (A.length + 1) A a f

/-- Executable and inductive ancestry agree on every ranked finite history. -/
theorem ancestor_iff (A : List Act) (ranked : Ranked A) (a f : Act) (member : f ∈ A) :
    ancestor A a f = true ↔ Ancestor (fun act => act ∈ A) a f := by
  constructor
  · exact reachable_sound _ _ _ _
  · intro path
    obtain ⟨rank,ordered⟩ := ranked
    let compressed := fun act => StateFiniteCausalRank.below A rank (rank act)
    have compressedRanked : RankedBy A compressed := by
      intro child childIn parent parentIn edge
      exact StateFiniteCausalRank.below_strict A rank parent parentIn (rank child)
        (ordered child childIn parent parentIn edge)
    have bound := StateFiniteCausalRank.below_bound A rank f member
    exact reachable_complete _ A compressed compressedRanked a f member path (by simpa [compressed] using Nat.lt_trans bound (Nat.lt_succ_self A.length))

/-- A directly executable exact causal cut. -/
def cut (A : List Act) (freezer : Act) : List Act := A.filter (fun a => ancestor A a freezer)

/-- The executable cut is literally the existing semantic cut, in input order. -/
theorem cut_refinement (A : List Act) (ranked : Ranked A) (freezer : Act) (member : freezer ∈ A) :
    cut A freezer = causalCut (fun act => act ∈ A) A freezer := by
  classical
  apply List.filter_congr
  intro act _
  have same := ancestor_iff A ranked act freezer member
  cases computed : ancestor A act freezer <;> simp_all

/-- Executable earliest-freezer test with exact predecessor reachability. -/
def earliest (A : List Act) (verb : String) (freezer : Act) : Bool :=
  A.contains freezer && freezer.verb == verb && A.all (fun earlier =>
    !(earlier.verb == verb && ancestor A earlier freezer) || earlier == freezer)

/-- Earliest-freezer recognition equals the existing declarative definition. -/
theorem earliest_iff (A : List Act) (ranked : Ranked A) (verb : String) (freezer : Act) :
    earliest A verb freezer = true ↔ Earliest (fun act => act ∈ A) verb A freezer := by
  simp only [earliest,Bool.and_eq_true,List.contains_iff_mem,beq_iff_eq,List.all_eq_true]
  constructor
  · rintro ⟨⟨member,verbIs⟩,first⟩
    refine ⟨member,verbIs,?_⟩
    intro earlier present verbMatch path
    have reached := (ancestor_iff A ranked earlier freezer member).mpr path
    simpa [verbMatch,reached] using first earlier present
  · rintro ⟨member,verbIs,first⟩
    refine ⟨⟨member,verbIs⟩,?_⟩
    intro earlier present
    by_cases verbMatch : earlier.verb = verb
    · by_cases reached : ancestor A earlier freezer = true
      · have same := first earlier present verbMatch ((ancestor_iff A ranked earlier freezer member).mp reached)
        simp [same]
      · cases value : ancestor A earlier freezer <;> simp_all
    · simp [verbMatch]

/-- Executable recognition of exactly the two semantic freeze conflict causes. -/
def conflict (A : List Act) (verb : String) (contributes : Act → Bool) (policy : Bool) (a b : Act) : Bool :=
  (earliest A verb a && earliest A verb b && a.addr != b.addr) ||
    (earliest A verb a && A.contains b && contributes b && !ancestor A b a && policy)

/-- Every Boolean conflict is a concrete witness, and every witness is recognized. -/
theorem conflict_iff (A : List Act) (ranked : Ranked A) (verb : String) (contributes : Act → Bool)
    (policy : Bool) (a b : Act) : conflict A verb contributes policy a b = true ↔
      FreezeConflict (fun act => act ∈ A) verb (fun act => contributes act = true) policy A a b := by
  constructor
  · intro found
    simp only [conflict,Bool.or_eq_true,Bool.and_eq_true,bne_iff_ne,List.contains_iff_mem] at found
    rcases found with ⟨⟨first,second⟩,different⟩ | ⟨⟨⟨⟨first,member⟩,contribution⟩,outside⟩,fault⟩
    · exact .concurrent ((earliest_iff A ranked verb a).mp first) ((earliest_iff A ranked verb b).mp second) different
    · have first := (earliest_iff A ranked verb a).mp first
      have outside : ¬ Ancestor (fun act => act ∈ A) b a := by
        intro path
        have reached := (ancestor_iff A ranked b a first.1).mpr path
        simp [reached] at outside
      exact .late first member contribution outside fault
  · intro witness
    cases witness with
    | concurrent first second different =>
      simp [conflict,(earliest_iff A ranked verb a).mpr first,(earliest_iff A ranked verb b).mpr second,different]
    | late first member contribution outside fault =>
      have absent : ancestor A b a = false := by
        cases result : ancestor A b a with
        | false => rfl
        | true => exact False.elim (outside ((ancestor_iff A ranked b a first.1).mp result))
      simp [conflict,(earliest_iff A ranked verb a).mpr first,member,contribution,absent,fault]

/-- Enumerate witness pairs from the finite accepted set, without a host classifier. -/
def conflicts (A : List Act) (verb : String) (contributes : Act → Bool) (policy : Bool) : List (Act × Act) :=
  A.flatMap (fun a => (A.filter (fun b => conflict A verb contributes policy a b)).map (fun b => (a,b)))

/-- Finite witness enumeration contains exactly the semantic conflict pairs. -/
theorem conflicts_member (A : List Act) (ranked : Ranked A) (verb : String) (contributes : Act → Bool)
    (policy : Bool) (a b : Act) : (a,b) ∈ conflicts A verb contributes policy ↔
      FreezeConflict (fun act => act ∈ A) verb (fun act => contributes act = true) policy A a b := by
  simp only [conflicts,List.mem_flatMap,List.mem_map,List.mem_filter,Prod.mk.injEq]
  constructor
  · rintro ⟨left,_,right,⟨_,found⟩,rfl,rfl⟩
    exact (conflict_iff A ranked verb contributes policy left right).mp found
  · intro witness
    have members := freeze_witness_accepted witness
    exact ⟨a,members.1,b,⟨members.2,(conflict_iff A ranked verb contributes policy a b).mpr witness⟩,rfl,rfl⟩

/-- Concrete address list for all freeze witnesses, including late writes for
all concurrent earliest freezers under the fault policy. -/
def evidence (A : List Act) (verb : String) (contributes : Act → Bool) (policy : Bool) : List Nat :=
  (conflicts A verb contributes policy).flatMap (fun (a,b) => [a.addr,b.addr])

/-- Executable evidence is exactly the existing semantic witness set. -/
theorem evidence_member (A : List Act) (ranked : Ranked A) (verb : String) (contributes : Act → Bool)
    (policy : Bool) (address : Nat) : address ∈ evidence A verb contributes policy ↔
      freezeEvidence (fun act => act ∈ A) verb (fun act => contributes act = true) policy A address := by
  simp only [evidence,List.mem_flatMap]
  constructor
  · rintro ⟨⟨a,b⟩,member,which⟩
    exact ⟨a,b,(conflicts_member A ranked verb contributes policy a b).mp member,by simpa using which⟩
  · rintro ⟨a,b,witness,which⟩
    exact ⟨(a,b),(conflicts_member A ranked verb contributes policy a b).mpr witness,by simpa using which⟩

/-- Nonempty executable witnesses are equivalent to an actual semantic conflict. -/
theorem has_conflict (A : List Act) (ranked : Ranked A) (verb : String) (contributes : Act → Bool) (policy : Bool) :
    (conflicts A verb contributes policy).isEmpty = false ↔
      ∃ a b, FreezeConflict (fun act => act ∈ A) verb (fun act => contributes act = true) policy A a b := by
  constructor
  · intro nonempty
    cases listed : conflicts A verb contributes policy with
    | nil => simp [listed] at nonempty
    | cons pair rest =>
      obtain ⟨a,b⟩ := pair
      exact ⟨a,b,(conflicts_member A ranked verb contributes policy a b).mp (by simp [listed])⟩
  · rintro ⟨a,b,witness⟩
    have member := (conflicts_member A ranked verb contributes policy a b).mpr witness
    cases listed : conflicts A verb contributes policy <;> simp_all

/-- Executable frozen observation with enumerable evidence and exclusions. -/
inductive Read (V : Type) where
  | snapshot (value : V)
  | frozen (freezer : Nat) (value : V) (excluded : List Act)
  | fault (evidence : List Nat)

/-- Computational freeze read; the current raw fault is checked before cutting. -/
def read {V : Type} (A : List Act) (verb : String) (contributes : Act → Bool) (policy : Bool)
    (rawFault : Option (List Nat)) (evaluate : List Act → V) : Read V :=
  if rawFault.isSome || !(conflicts A verb contributes policy).isEmpty then
    .fault (rawFault.getD [] ++ evidence A verb contributes policy)
  else match A.find? (earliest A verb) with
    | none => .snapshot (evaluate A)
    | some freezer => .frozen freezer.addr (evaluate (cut A freezer))
        (A.filter (fun a => contributes a && !ancestor A a freezer))

/-- Interpret concrete executable collections as the semantic finite sets. -/
def Read.semantic {V : Type} : Read V → FreezeRead V
  | .snapshot value => .snapshot value
  | .frozen freezer value excluded => .frozen freezer value (FinSet.mk excluded)
  | .fault evidence => .fault (fun address => address ∈ evidence)

/-- Enumerable and semantic evidence are extensionally identical. -/
theorem evidence_set (A : List Act) (ranked : Ranked A) (verb : String) (contributes : Act → Bool) (policy : Bool) :
    (fun address => address ∈ evidence A verb contributes policy) =
      freezeEvidence (fun act => act ∈ A) verb (fun act => contributes act = true) policy A := by
  funext address
  exact propext (evidence_member A ranked verb contributes policy address)

/-- Complete executable freeze-read refinement, including unioned raw faults. -/
theorem read_refinement {V : Type} (A : List Act) (ranked : Ranked A) (verb : String)
    (contributes : Act → Bool) (policy : Bool) (rawFault : Option (List Nat)) (evaluate : List Act → V) :
    (read A verb contributes policy rawFault evaluate).semantic =
      freezeRead (fun act => act ∈ A) verb (fun act => contributes act = true) policy
        (rawFault.map (fun addresses => fun address => address ∈ addresses)) evaluate A := by
  classical
  have first : earliest A verb = fun act => decide (Earliest (fun act => act ∈ A) verb A act) := by
    funext act
    have same := earliest_iff A ranked verb act
    cases computed : earliest A verb act <;> simp_all
  have conflictsEmpty : (conflicts A verb contributes policy).isEmpty = true ↔
      ¬ ∃ a b, FreezeConflict (fun act => act ∈ A) verb (fun act => contributes act = true) policy A a b := by
    have some := has_conflict A ranked verb contributes policy
    cases empty : (conflicts A verb contributes policy).isEmpty <;> simp_all
  have faultEvidence (addresses : List Nat) :
      (fun address => address ∈ addresses ++ evidence A verb contributes policy) =
        Lattice.Set.union (fun address => address ∈ addresses) (freezeEvidence (fun act => act ∈ A) verb
          (fun act => contributes act = true) policy A) := by
    funext address
    apply propext
    simp only [List.mem_append,Lattice.Set.union,← evidence_member A ranked verb contributes policy address]
  cases rawFault with
  | some addresses =>
    simp only [read,Option.isSome_some,Bool.true_or,ite_true,Read.semantic,Option.getD_some,freezeRead,
      Option.map_some,Option.isSome_some,true_or,ite_true]
    exact congrArg FreezeRead.fault (faultEvidence addresses)
  | none =>
    by_cases empty : (conflicts A verb contributes policy).isEmpty = true
    · have clear := conflictsEmpty.mp empty
      simp only [read,Option.isSome_none,Bool.false_or,empty,Bool.not_true,Bool.false_eq_true,ite_false,
        freezeRead,Option.map_none,Option.isSome_none,Bool.false_eq_true,false_or,if_neg clear,first]
      cases selected : A.find? (fun act => decide (Earliest (fun act => act ∈ A) verb A act)) with
      | none => rfl
      | some freezer =>
        have firstFreezer : Earliest (fun act => act ∈ A) verb A freezer := of_decide_eq_true (List.find?_some (p := fun act => decide (Earliest (fun act => act ∈ A) verb A act)) selected)
        have excluded : A.filter (fun a => contributes a && !ancestor A a freezer) =
            A.filter (fun a => decide (contributes a = true ∧ ¬Ancestor (fun act => act ∈ A) a freezer)) := by
          apply List.filter_congr
          intro act _
          have same := ancestor_iff A ranked act freezer firstFreezer.1
          cases c : contributes act <;> cases r : ancestor A act freezer <;> simp_all
        simp only [Read.semantic,cut_refinement A ranked freezer firstFreezer.1,excluded]
        apply congrArg (FreezeRead.frozen freezer.addr (evaluate (causalCut (fun act => act ∈ A) A freezer)))
        apply FinSet.ext
        intro act
        simp only [FinSet.mem_mk,List.mem_filter,decide_eq_true_eq]
    · have nonempty : (conflicts A verb contributes policy).isEmpty = false := by
        cases result : (conflicts A verb contributes policy).isEmpty <;> simp_all
      have bad := (has_conflict A ranked verb contributes policy).mp nonempty
      simp only [read,Option.isSome_none,Bool.false_or,nonempty,Bool.not_false,ite_true,Read.semantic,
        Option.getD_none,List.nil_append,freezeRead,Option.map_none,Option.isSome_none,Bool.false_eq_true,
        false_or,if_pos bad,Option.getD_none]
      have noRaw : (∅ : Lattice.Set Nat) ∪ freezeEvidence (fun act => act ∈ A) verb
          (fun act => contributes act = true) policy A = freezeEvidence (fun act => act ∈ A) verb
          (fun act => contributes act = true) policy A := by
        funext address
        apply propext
        change (False ∨ _) ↔ _
        simp
      rw [noRaw]
      exact congrArg FreezeRead.fault (evidence_set A ranked verb contributes policy)

end CBCL.StateExecutableFreeze
