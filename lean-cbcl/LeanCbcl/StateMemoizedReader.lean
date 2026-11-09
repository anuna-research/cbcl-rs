import Lean

/-! Operational memoization for scoped field requests. A field body can branch
on dependency results, so calls retain their continuations rather than eagerly
collecting every possible dependency. The cache starts empty and is populated
only after a body finishes. Typed body extraction from Rust remains explicit. -/
set_option autoImplicit false
namespace CBCL.StateMemoizedReader

/-- Native cache identity retains both the accepted-history scope and field. -/
abbrev Key := Nat × String

/-- A field body either returns a value or requests another scoped field before
choosing the remainder of its computation. -/
inductive Body (V : Type) where
  | done (value : V)
  | request (key : Key) (next : V → Body V)

/-- Interpret a field body against an independent total field meaning. -/
def Body.meaning {V : Type} (read : Key → V) : Body V → V
  | .done value => value
  | .request key next => (next (read key)).meaning read

/-- Every possible continuation requests only lower-ranked field computations. -/
def Body.Below {V : Type} (rank : Key → Nat) (bound : Nat) : Body V → Prop
  | .done _ => True
  | .request key next => rank key < bound ∧ ∀ value, (next value).Below rank bound

/-- Interpret a body with only the lower-ranked field meanings in scope. -/
def Body.belowMeaning {V : Type} (rank : Key → Nat) (bound : Nat)
    (read : (key : Key) → rank key < bound → V) : (body : Body V) → body.Below rank bound → V
  | .done value, _ => value
  | .request key next, below =>
      (next (read key below.1)).belowMeaning rank bound read (below.2 _)

/-- Restricted body evaluation agrees with total evaluation whenever every
requested lower key has the same independent meaning. -/
theorem below_meaning_eq {V : Type} (meaning : Key → V) (rank : Key → Nat) (bound : Nat)
    (read : (key : Key) → rank key < bound → V) (body : Body V) (below : body.Below rank bound)
    (agree : ∀ key smaller, read key smaller = meaning key) :
    body.belowMeaning rank bound read below = body.meaning meaning := by
  induction body with
  | done _ => rfl
  | request key next ih =>
    simp only [Body.belowMeaning,Body.meaning,agree]
    exact ih (meaning key) (below.2 _)

/-- Independently recurse over ranked bodies without a cache or a fuel limit. -/
noncomputable def reference {V : Type} (body : Key → Body V) (rank : Key → Nat)
    (ranked : ∀ key, (body key).Below rank (rank key)) : Key → V :=
  (measure rank).wf.fix (fun key read => (body key).belowMeaning rank (rank key) read (ranked key))

/-- The uncached recursion constructs the body equation needed by the cache
proof; callers do not assume a pre-existing correct global field meaning. -/
theorem reference_equation {V : Type} (body : Key → Body V) (rank : Key → Nat)
    (ranked : ∀ key, (body key).Below rank (rank key)) (key : Key) :
    (body key).meaning (reference body rank ranked) = reference body rank ranked key := by
  conv => rhs; unfold reference; rw [WellFounded.fix_eq]
  exact (below_meaning_eq (reference body rank ranked) rank (rank key)
    (fun dependency _ => reference body rank ranked dependency) (body key) (ranked key) (fun _ _ => rfl)).symm

/-- Association-list model of the native exact-key map; insertion prepends the
new result and lookup uses the first matching complete scope/field key. -/
abbrev Cache (V : Type) := List (Key × V)

/-- Every stored result agrees with its independent scoped field meaning. -/
def Valid {V : Type} (meaning : Key → V) (cache : Cache V) : Prop :=
  ∀ key value, cache.lookup key = some value → value = meaning key

/-- An empty cache establishes validity without any supplied cached results. -/
theorem empty_valid {V : Type} (meaning : Key → V) : Valid meaning [] := by
  intro key value present
  simp at present

/-- Adding a completed correct result preserves the entire cache invariant. -/
theorem insert_valid {V : Type} (meaning : Key → V) (cache : Cache V) (key : Key)
    (valid : Valid meaning cache) : Valid meaning ((key,meaning key)::cache) := by
  intro other value present
  by_cases same : key = other
  · subst other
    simpa using present.symm
  · have different : (other == key) = false := by simpa using Ne.symm same
    exact valid other value (by simpa [List.lookup,different] using present)

/-- Run the body with state threaded through each dependency and continuation. -/
def Body.run {V : Type} (read : Key → Cache V → Option (V × Cache V)) :
    Body V → Cache V → Option (V × Cache V)
  | .done value, cache => some (value,cache)
  | .request key next, cache => do
      let (value,after) ← read key cache
      (next value).run read after

/-- Memoized field requests check the exact key, run a missing field body, and
insert only the completed result. Fuel failure is explicit, never a value. -/
def read {V : Type} (body : Key → Body V) : Nat → Key → Cache V → Option (V × Cache V)
  | 0, key, cache => do return (← cache.lookup key,cache)
  | fuel+1, key, cache =>
      match cache.lookup key with
      | some value => some (value,cache)
      | none => do
          let (value,after) ← (body key).run (read body fuel) cache
          return (value,(key,value)::after)

/-- Body execution preserves the cache and returns its independent meaning
when all requested lower computations satisfy that property. -/
theorem body_run_refinement {V : Type} (meaning : Key → V) (rank : Key → Nat) (bound : Nat)
    (read : Key → Cache V → Option (V × Cache V)) (body : Body V)
    (below : body.Below rank bound)
    (requests : ∀ key, rank key < bound → ∀ cache, Valid meaning cache →
      ∃ after, read key cache = some (meaning key,after) ∧ Valid meaning after) :
    ∀ cache, Valid meaning cache → ∃ after,
      body.run read cache = some (body.meaning meaning,after) ∧ Valid meaning after := by
  induction body with
  | done value => intro cache valid; exact ⟨cache,rfl,valid⟩
  | request key next ih =>
    intro cache valid
    obtain ⟨after,called,afterValid⟩ := requests key below.1 cache valid
    obtain ⟨final,continued,finalValid⟩ := ih (meaning key) (below.2 _) after afterValid
    exact ⟨final,by simp only [Body.run,called,Body.meaning]; exact continued,finalValid⟩

/-- A ranked request graph needs no assumed correct cache entries: local field
body equations suffice for every cache miss and every subsequent exact-key hit. -/
theorem read_refinement {V : Type} (meaning : Key → V) (body : Key → Body V) (rank : Key → Nat)
    (equation : ∀ key, (body key).meaning meaning = meaning key)
    (ranked : ∀ key, (body key).Below rank (rank key)) :
    ∀ fuel key, rank key < fuel → ∀ cache, Valid meaning cache → ∃ after,
      read body fuel key cache = some (meaning key,after) ∧ Valid meaning after := by
  intro fuel
  induction fuel with
  | zero => intro key impossible; omega
  | succ fuel ih =>
    intro key enough cache valid
    cases found : cache.lookup key with
    | some value =>
      have valueCorrect := valid key value found
      subst value
      exact ⟨cache,by simp [read,found],valid⟩
    | none =>
      have calls : ∀ dependency, rank dependency < rank key → ∀ cache, Valid meaning cache →
          ∃ after, read body fuel dependency cache = some (meaning dependency,after) ∧ Valid meaning after := by
        intro dependency smaller cache valid
        exact ih dependency (by omega) cache valid
      obtain ⟨after,ran,afterValid⟩ := body_run_refinement meaning rank (rank key) (read body fuel)
        (body key) (ranked key) calls cache valid
      rw [equation key] at ran
      refine ⟨(key,meaning key)::after,?_,insert_valid meaning after key afterValid⟩
      simp only [read,found,ran]
      rfl

/-- The initial native request constructs its valid cache from no stored values. -/
theorem empty_read {V : Type} (meaning : Key → V) (body : Key → Body V) (rank : Key → Nat)
    (equation : ∀ key, (body key).meaning meaning = meaning key)
    (ranked : ∀ key, (body key).Below rank (rank key)) (key : Key) :
    ∃ after, read body (rank key+1) key [] = some (meaning key,after) ∧ Valid meaning after :=
  read_refinement meaning body rank equation ranked _ key (by omega) [] (empty_valid meaning)

/-- Memoization starts empty and agrees with a separately defined uncached
recursion for every ranked, dynamically branching field-request body. -/
theorem operational_refinement {V : Type} (body : Key → Body V) (rank : Key → Nat)
    (ranked : ∀ key, (body key).Below rank (rank key)) (key : Key) :
    ∃ after, read body (rank key+1) key [] = some (reference body rank ranked key,after) ∧
      Valid (reference body rank ranked) after :=
  empty_read (reference body rank ranked) body rank (reference_equation body rank ranked) ranked key

/-- Read several top-level fields through one shared mutable-cache state. -/
def reads {V : Type} (body : Key → Body V) (rank : Key → Nat) :
    List Key → Cache V → Option (List V × Cache V)
  | [], cache => some ([],cache)
  | key::rest, cache => do
      let (value,after) ← read body (rank key+1) key cache
      let (values,final) ← reads body rank rest after
      return (value::values,final)

/-- Every successive top-level observation reuses the valid cache established
by previous fields, including results created by nested requests. -/
theorem reads_refinement {V : Type} (body : Key → Body V) (rank : Key → Nat)
    (ranked : ∀ key, (body key).Below rank (rank key)) (keys : List Key) :
    ∀ cache, Valid (reference body rank ranked) cache → ∃ after,
      reads body rank keys cache = some (keys.map (reference body rank ranked),after) ∧
      Valid (reference body rank ranked) after := by
  induction keys with
  | nil => intro cache valid; exact ⟨cache,rfl,valid⟩
  | cons key rest ih =>
    intro cache valid
    obtain ⟨after,head,afterValid⟩ := read_refinement (reference body rank ranked) body rank
      (reference_equation body rank ranked) ranked (rank key+1) key (by omega) cache valid
    obtain ⟨final,tail,finalValid⟩ := ih after afterValid
    refine ⟨final,?_,finalValid⟩
    simp only [reads,head]
    change (do let (values,final) ← reads body rank rest after
               pure (reference body rank ranked key::values,final)) = _
    rw [tail]
    rfl

/-- Typed native field operations. Source evaluation and fault/wrapper encoding
are leaf boundaries; dependency calls and freeze redirection are explicit. -/
structure Operations (V : Type) where
  /-- The earlier field needed by a histogram or sum, if any. -/
  dependency : String → Option String
  /-- Globally planned causal-cut scope for each frozen field. -/
  cut : String → Option Nat
  /-- Whether that field's freezer occurs in the requested scope. -/
  active : Key → Bool
  /-- Strip frozen presentation before passing a value to a dependency. -/
  unfrozen : V → V
  /-- Native scoped rule evaluator with its optional dependency result. -/
  normal : Key → Option V → V
  /-- Terminal raw/freeze fault combination, checked before historical reads. -/
  fault : Key → V → Option V
  /-- Add this scope's freezer and excluded-contribution metadata. -/
  frozen : Key → V → V

/-- Finish a native field after its normal scoped value is computed. A fault
returns immediately; a different planned cut triggers a same-field request. -/
def Operations.finish {V : Type} (ops : Operations V) (key : Key) (normal : V) : Body V :=
  match ops.fault key normal with
  | some fault => .done fault
  | none =>
    if ops.active key then
      match ops.cut key.2 with
      | none => .done normal
      | some scope =>
        if key.1 = scope then .done (ops.frozen key normal)
        else .request (scope,key.2) (fun value => .done (ops.frozen key (ops.unfrozen value)))
    else .done normal

/-- Dependency reads retain the caller's scope and unwrap the dependency before
normal evaluation. This is the request ordering of `freeze::Reader::field`. -/
def Operations.body {V : Type} (ops : Operations V) (key : Key) : Body V :=
  match ops.dependency key.2 with
  | none => ops.finish key (ops.normal key none)
  | some source => .request (key.1,source) (fun value => ops.finish key (ops.normal key (some (ops.unfrozen value))))

/-- Earlier fields decrease the primary rank; redirecting a field into its own
planned cut decreases the secondary phase. Scopes need no numerical ordering. -/
def requestRank (index : String → Nat) (cut : String → Option Nat) (key : Key) : Nat :=
  2 * index key.2 + if cut key.2 = some key.1 then 0 else 1

/-- Each field's cut request terminates immediately at that same planned scope. -/
theorem redirect_rank (index : String → Nat) (cut : String → Option Nat) (key : Key) (scope : Nat)
    (selected : cut key.2 = some scope) (different : key.1 ≠ scope) :
    requestRank index cut (scope,key.2) < requestRank index cut key := by
  simp [requestRank,selected,Ne.symm different]


/-- Every earlier dependency is lower ranked regardless of either field's cut. -/
theorem dependency_rank (index : String → Nat) (cut : String → Option Nat) (key : Key) (source : String)
    (earlier : index source < index key.2) :
    requestRank index cut (key.1,source) < requestRank index cut key := by
  unfold requestRank
  dsimp only
  split <;> split <;> omega

/-- Native finishing requests only its own preplanned cut, with strictly lower
rank; faults never trigger a hidden historical read. -/
theorem finish_ranked {V : Type} (ops : Operations V) (index : String → Nat) (key : Key) (normal : V) :
    (ops.finish key normal).Below (requestRank index ops.cut) (requestRank index ops.cut key) := by
  unfold Operations.finish
  split
  · trivial
  · split
    · split
      · trivial
      · rename_i scope selected
        split
        · trivial
        · rename_i different
          exact ⟨redirect_rank index ops.cut key scope selected different,fun _ => trivial⟩
    · trivial

/-- Compiler-established earlier-field ordering suffices to rank every native
request, including dynamic dependency values and same-field cut redirection. -/
theorem body_ranked {V : Type} (ops : Operations V) (index : String → Nat)
    (earlier : ∀ field source, ops.dependency field = some source → index source < index field) (key : Key) :
    (ops.body key).Below (requestRank index ops.cut) (requestRank index ops.cut key) := by
  unfold Operations.body
  split
  · exact finish_ranked ops index key _
  · rename_i source selected
    exact ⟨dependency_rank index ops.cut key source (earlier key.2 source selected),
      fun _ => finish_ranked ops index key _⟩

/-- The native dependency/cut orchestration constructs a valid shared cache
from empty and returns exactly the independent uncached observations. -/
theorem native_reads_refinement {V : Type} (ops : Operations V) (index : String → Nat)
    (earlier : ∀ field source, ops.dependency field = some source → index source < index field) (keys : List Key) :
    ∃ after, reads ops.body (requestRank index ops.cut) keys [] =
      some (keys.map (reference ops.body (requestRank index ops.cut) (body_ranked ops index earlier)),after) ∧
      Valid (reference ops.body (requestRank index ops.cut) (body_ranked ops index earlier)) after :=
  reads_refinement ops.body (requestRank index ops.cut) (body_ranked ops index earlier) keys [] (empty_valid _)

end CBCL.StateMemoizedReader
