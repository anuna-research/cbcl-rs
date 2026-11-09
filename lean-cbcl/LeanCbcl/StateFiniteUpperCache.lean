import LeanCbcl.StateFiniteRead

/-! Native finite-read compatibility uses cached maxima of non-top principal
upper sets. This module models that optimization over the checked join table;
query decoding and the authored installation gate remain explicit boundaries. -/
set_option autoImplicit false
namespace CBCL.StateFiniteUpperCache
open State StateLift StateFiniteTable

/-- Maximum of an optional numeric projection list; an empty set has no maximum. -/
def maximum : List Int → Option Int
  | [] => none
  | x :: xs => some (match maximum xs with | none => x | some y => max x y)

/-- A cached maximum passes exactly the thresholds attained by some member. -/
theorem maximum_ge (xs : List Int) (threshold : Int) :
    (∃ value, maximum xs = some value ∧ threshold ≤ value) ↔
      ∃ value ∈ xs, threshold ≤ value := by
  induction xs with
  | nil => simp [maximum]
  | cons x xs ih =>
    cases cached : maximum xs with
    | none =>
      have absent : ¬ ∃ value ∈ xs, threshold ≤ value := by simpa [cached] using not_congr ih
      simp only [maximum,cached,Option.some.injEq,List.mem_cons]
      constructor
      · rintro ⟨value,rfl,reached⟩; exact ⟨x,Or.inl rfl,reached⟩
      · rintro ⟨value,same | member,reached⟩
        · exact ⟨x,rfl,by simpa [same] using reached⟩
        · exact False.elim (absent ⟨value,member,reached⟩)
    | some y =>
      have tail : threshold ≤ y ↔ ∃ value ∈ xs, threshold ≤ value := by simpa [cached] using ih
      simp only [maximum,cached,Option.some.injEq,List.mem_cons]
      constructor
      · rintro ⟨value,rfl,reached⟩
        by_cases first : threshold ≤ x
        · exact ⟨x,Or.inl rfl,first⟩
        · obtain ⟨value,member,enough⟩ := tail.mp (by omega)
          exact ⟨value,Or.inr member,enough⟩
      · rintro ⟨value,same | member,reached⟩
        · have : threshold ≤ x := by simpa [same] using reached
          exact ⟨max x y,rfl,by omega⟩
        · have : threshold ≤ y := tail.mpr ⟨value,member,reached⟩
          exact ⟨max x y,rfl,by omega⟩

/-- Numeric values in the non-top principal upper set of one carrier element. -/
def upperValues (verified : Verified) (project : Fin verified.table.elements.length → Option Int)
    (root : Fin verified.table.elements.length) : List Int :=
  ((indices verified.table).filter (fun current =>
    current != verified.table.top && merge verified.table root current == current)).filterMap project

/-- The precomputed native upper-set maximum for one root. -/
def upperMaximum (verified : Verified) (project : Fin verified.table.elements.length → Option Int)
    (root : Fin verified.table.elements.length) : Option Int := maximum (upperValues verified project root)

/-- Cached maxima preserve exactly the non-top upper-state numeric witnesses. -/
theorem upperMaximum_ge (verified : Verified) (project : Fin verified.table.elements.length → Option Int)
    (root : Fin verified.table.elements.length) (threshold : Int) :
    (∃ value, upperMaximum verified project root = some value ∧ threshold ≤ value) ↔
      ∃ current, current ≠ verified.table.top ∧ merge verified.table root current = current ∧
        ∃ value, project current = some value ∧ threshold ≤ value := by
  rw [upperMaximum,maximum_ge]
  simp only [upperValues,List.mem_filterMap,List.mem_filter,indices,List.mem_finRange,
    Bool.and_eq_true,bne_iff_ne,beq_iff_eq,true_and]
  constructor
  · rintro ⟨value,⟨current,⟨notTop,below⟩,projected⟩,enough⟩
    exact ⟨current,notTop,below,value,projected,enough⟩
  · rintro ⟨current,notTop,below,value,projected,enough⟩
    exact ⟨value,⟨current,⟨notTop,below⟩,projected⟩,enough⟩

/-- Typed query after the native finite element admission and name resolution. -/
inductive Query (verified : Verified) where
  | named (element : Fin verified.table.elements.length)
  | numeric (threshold : Int)

/-- Successful query predicate before the separate top fault guard. -/
def succeeds (verified : Verified) (project : Fin verified.table.elements.length → Option Int) :
    Query verified → Fin verified.table.elements.length → Prop
  | .named element, current => merge verified.table element current = current
  | .numeric threshold, current => ∃ value, project current = some value ∧ threshold ≤ value

/-- Native compatibility formulas; maxima are expressed functionally here.
The Rust implementation precomputes these values in a separate cache vector. -/
def compatible (verified : Verified) (project : Fin verified.table.elements.length → Option Int) :
    Query verified → Query verified → Bool
  | .named a, .named b => merge verified.table a b != verified.table.top
  | .named a, .numeric threshold | .numeric threshold, .named a =>
      (upperMaximum verified project a).isSome &&
        decide (threshold ≤ (upperMaximum verified project a).getD 0)
  | .numeric a, .numeric b =>
      (upperMaximum verified project verified.table.bottom).isSome &&
        decide (max a b ≤ (upperMaximum verified project verified.table.bottom).getD 0)

/-- The optional cache test rejects absent maxima, including negative thresholds. -/
theorem optional_test (cached : Option Int) (threshold : Int) :
    (cached.isSome && decide (threshold ≤ cached.getD 0)) = true ↔
      ∃ value, cached = some value ∧ threshold ≤ value := by
  cases cached <;> simp

/-- Two named reads share a non-top upper state exactly when their join is non-top. -/
theorem named_common (verified : Verified) (a b : Fin verified.table.elements.length) :
    merge verified.table a b ≠ verified.table.top ↔
      ∃ current, current ≠ verified.table.top ∧ merge verified.table a current = current ∧
        merge verified.table b current = current := by
  letI := algebra verified
  constructor
  · intro clear
    exact ⟨merge verified.table a b,clear,StateLVar.below_left a b,StateLVar.below_right a b⟩
  · rintro ⟨current,clear,left,right⟩ conflict
    have bound : StateLVar.Below (a ⊔ b) current := StateLVar.join_below left right
    rw [show a ⊔ b = (⊤ : Fin verified.table.elements.length) from conflict] at bound
    exact clear (StateLVar.top_below bound)

/-- Numeric read pairs use the bottom-root cache and the maximum threshold. -/
theorem numeric_common (verified : Verified) (project : Fin verified.table.elements.length → Option Int)
    (a b : Int) :
    (∃ value, upperMaximum verified project verified.table.bottom = some value ∧ max a b ≤ value) ↔
      ∃ current, current ≠ verified.table.top ∧
        succeeds verified project (.numeric a) current ∧ succeeds verified project (.numeric b) current := by
  rw [upperMaximum_ge]
  constructor
  · rintro ⟨current,clear,_,value,projected,enough⟩
    exact ⟨current,clear,⟨value,projected,by omega⟩,⟨value,projected,by omega⟩⟩
  · rintro ⟨current,clear,⟨left,projected,leftEnough⟩,⟨right,again,rightEnough⟩⟩
    have same : left = right := Option.some.inj (projected.symm.trans again)
    letI := algebra verified
    exact ⟨current,clear,bot_join current,left,projected,by omega⟩

/-- All three optimized native branches preserve precisely the common-success
witness tested by the exhaustive finite reference checker. -/
theorem compatible_iff (verified : Verified) (project : Fin verified.table.elements.length → Option Int)
    (left right : Query verified) : compatible verified project left right = true ↔
      ∃ current, current ≠ verified.table.top ∧
        succeeds verified project left current ∧ succeeds verified project right current := by
  cases left with
  | named a =>
    cases right with
    | named b => simpa [compatible,succeeds] using named_common verified a b
    | numeric threshold =>
      simpa only [compatible,optional_test,succeeds] using upperMaximum_ge verified project a threshold
  | numeric a =>
    cases right with
    | named b =>
      rw [compatible,optional_test,upperMaximum_ge]
      constructor
      · rintro ⟨current,clear,below,reached⟩; exact ⟨current,clear,reached,below⟩
      · rintro ⟨current,clear,reached,below⟩; exact ⟨current,clear,below,reached⟩
    | numeric b => simpa only [compatible,optional_test] using numeric_common verified project a b

/-- The native numeric cache maps integer displays directly and booleans to zero/one. -/
def numericValue : Val → Option Int
  | .int value => some value
  | .bool value => some (if value then 1 else 0)
  | _ => none

/-- The exact numeric projection used to build the native maxima vector. -/
def project (field : StateInstalledFinite.Field) (current : Fin field.table.table.elements.length) : Option Int :=
  match field.projection with
  | none => none
  | some projection => numericValue (StateFiniteProjection.value projection current)

/-- Resolve the native admitted scalar query representation. -/
def decode (field : StateInstalledFinite.Field) : Val → Option (Query field.table)
  | .str name => (StateFiniteTable.index field.table.table.elements name).map Query.named
  | .int threshold => some (.numeric threshold)
  | .bool true => some (.numeric 1)
  | _ => none

/-- Every displayed projection row satisfies a kind check imposed on all rows. -/
theorem value_kind {table : StateFiniteTable.Resolved} (projection : StateFiniteProjection.Verified table)
    (kind : Val → Bool) (all : projection.projection.rows.all (fun row => kind row.2) = true)
    (current : Fin table.elements.length) : kind (StateFiniteProjection.value projection current) = true := by
  obtain ⟨before,after,rows,_⟩ := List.lookup_eq_some_iff.mp (StateFiniteProjection.value_row projection current)
  have member : (current,StateFiniteProjection.value projection current) ∈ projection.projection.rows := by
    rw [rows]; simp
  exact List.all_eq_true.mp all _ member

/-- Admitted authored query decoding preserves the actual finite reach predicate. -/
theorem decode_reaches (field : StateInstalledFinite.Field) (query : Val)
    (admitted : StateFiniteRead.admitted field query = true) :
    ∃ decoded, decode field query = some decoded ∧ ∀ current,
      StateFiniteRead.reaches field query current = true ↔ succeeds field.table (project field) decoded current := by
  cases query with
  | str name =>
    cases found : StateFiniteTable.index field.table.table.elements name with
    | none => simp [StateFiniteRead.admitted,found] at admitted
    | some element =>
      exact ⟨.named element,by simp [decode,found],by intro current; simp [StateFiniteRead.reaches,found,succeeds]⟩
  | int threshold =>
    cases projection : field.projection with
    | none => simp [StateFiniteRead.admitted,projection] at admitted
    | some p =>
      have parts : p.projection.stable = true ∧ p.projection.rows.all (fun row => match row.2 with | .int _ => true | _ => false) = true := by
        have checked := admitted
        simp only [StateFiniteRead.admitted,projection,Bool.and_eq_true] at checked
        exact checked.2
      refine ⟨.numeric threshold,rfl,?_⟩
      intro current
      have kind := value_kind p (fun value => match value with | .int _ => true | _ => false) parts.2 current
      cases displayed : StateFiniteProjection.value p current <;>
        simp [displayed] at kind <;>
        simp [StateFiniteRead.reaches,projection,parts.1,displayed,succeeds,project,numericValue]
  | bool flag =>
    cases flag with
    | false => simp [StateFiniteRead.admitted] at admitted
    | true =>
      cases projection : field.projection with
      | none => simp [StateFiniteRead.admitted,projection] at admitted
      | some p =>
        have parts : p.projection.stable = true ∧ p.projection.rows.all (fun row => match row.2 with | .bool _ => true | _ => false) = true := by
          simpa [StateFiniteRead.admitted,StateFiniteProjection.scalarCheck,projection] using admitted
        refine ⟨.numeric 1,rfl,?_⟩
        intro current
        have kind := value_kind p (fun value => match value with | .bool _ => true | _ => false) parts.2 current
        cases displayed : StateFiniteProjection.value p current <;>
          simp [displayed] at kind <;>
          simp [StateFiniteRead.reaches,projection,parts.1,displayed,succeeds,project,numericValue]
        split <;> simp_all
  | list _ => simp [StateFiniteRead.admitted,StateFiniteProjection.scalarCheck] at admitted

/-- Native cached compatibility after scalar name/threshold decoding. -/
def cachedCompatible (field : StateInstalledFinite.Field) (left right : Val) : Bool :=
  match decode field left, decode field right with
  | some a, some b => compatible field.table (project field) a b
  | _, _ => false

/-- The optimized scalar-query test agrees with actual finite read predicates. -/
theorem cached_compatible_iff (field : StateInstalledFinite.Field) (left right : Val)
    (leftAdmitted : StateFiniteRead.admitted field left = true)
    (rightAdmitted : StateFiniteRead.admitted field right = true) :
    cachedCompatible field left right = true ↔ ∃ current, current ≠ field.table.table.top ∧
      StateFiniteRead.reaches field left current = true ∧ StateFiniteRead.reaches field right current = true := by
  obtain ⟨a,decodedA,reachesA⟩ := decode_reaches field left leftAdmitted
  obtain ⟨b,decodedB,reachesB⟩ := decode_reaches field right rightAdmitted
  simp only [cachedCompatible,decodedA,decodedB]
  rw [compatible_iff]
  simp only [← reachesA,← reachesB]

/-- Exhaustive pair traversal using the native cached-maximum compatibility formula. -/
def cachedPairCheck (field : StateInstalledFinite.Field) (queries : List Val) : Bool :=
  queries.all (fun left => queries.all (fun right => left == right || !cachedCompatible field left right))

/-- Cached and exhaustive pair validators accept exactly the same admitted reads. -/
theorem cached_pair_refinement (field : StateInstalledFinite.Field) (queries : List Val)
    (admitted : queries.all (StateFiniteRead.admitted field) = true) :
    cachedPairCheck field queries = StateFiniteRead.pairCheck field queries := by
  have equivalence : cachedPairCheck field queries = true ↔ StateFiniteRead.pairCheck field queries = true := by
    rw [StateFiniteRead.pairCheck_iff]
    simp only [cachedPairCheck,List.all_eq_true,Bool.or_eq_true,beq_iff_eq]
    constructor
    · intro checked left leftMember right rightMember different current clear leftRead
      have no := (checked left leftMember right rightMember).resolve_left different
      cases reached : StateFiniteRead.reaches field right current with
      | false => rfl
      | true =>
        have yes := (cached_compatible_iff field left right
          (List.all_eq_true.mp admitted _ leftMember) (List.all_eq_true.mp admitted _ rightMember)).mpr
          ⟨current,clear,leftRead,reached⟩
        simp [yes] at no
    · intro checked left leftMember right rightMember
      by_cases same : left = right
      · exact Or.inl same
      · right
        cases result : cachedCompatible field left right with
        | false => rfl
        | true =>
          obtain ⟨current,clear,leftRead,rightRead⟩ := (cached_compatible_iff field left right
            (List.all_eq_true.mp admitted _ leftMember) (List.all_eq_true.mp admitted _ rightMember)).mp result
          have rejected := checked left leftMember right rightMember same current clear leftRead
          simp [rightRead] at rejected
  cases first : cachedPairCheck field queries <;> cases second : StateFiniteRead.pairCheck field queries <;> simp_all

/-- Complete cached gate uses the same scalar, nonempty and uniqueness checks. -/
def cachedCheck (field : StateInstalledFinite.Field) (queries : List Val) : Bool :=
  !queries.isEmpty && decide queries.Nodup && queries.all (StateFiniteRead.admitted field) && cachedPairCheck field queries

/-- The normalized cached finite gate equals the reference gate on all inputs.
The Rust unordered pair loop and diagnostic ordering are separate obligations. -/
theorem cached_check_refinement (field : StateInstalledFinite.Field) (queries : List Val) :
    cachedCheck field queries = StateFiniteRead.check field queries := by
  by_cases admitted : queries.all (StateFiniteRead.admitted field) = true
  · simp only [cachedCheck,StateFiniteRead.check,cached_pair_refinement field queries admitted]
  · have rejected : queries.all (StateFiniteRead.admitted field) = false := by
      cases result : queries.all (StateFiniteRead.admitted field) <;> simp_all
    simp [cachedCheck,StateFiniteRead.check,rejected]

end CBCL.StateFiniteUpperCache
