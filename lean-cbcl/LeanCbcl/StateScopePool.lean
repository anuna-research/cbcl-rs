import LeanCbcl.StateMemoizedReader
import LeanCbcl.StateExecutableFreeze
import LeanCbcl.StateFreezeScopes

/-! Native causal-cut scope allocation. Scope zero is full history; each
freezer address is interned once, old indices stay stable, and reused or newly
allocated indices retrieve the exact address-selected causal cut. -/
set_option autoImplicit false
namespace CBCL.StateScopePool
open State StateLift StateLVar StateObservation

/-- Remove duplicate deliveries before native scope planning. Accepted identity
consistency makes full-act equality agree with native address deduplication. -/
def normalize (whole : List Act) : List Act := FinSet.dedup whole

/-- Normalization preserves exactly the accepted act set. -/
theorem normalize_setEq (whole : List Act) : SetEq (normalize whole) whole :=
  fun _ => FinSet.mem_dedup

/-- Content-address consistency is sufficient to obtain unique accepted
identities after duplicate delivery is normalized. -/
theorem normalize_unique (whole : List Act)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) : NodupAddr (normalize whole) := by
  apply List.pairwise_map.mpr
  exact (FinSet.nodup_dedup whole).imp_of_mem (fun {a b} memberA memberB different same =>
    different (consistent a (FinSet.mem_dedup.mp memberA) b (FinSet.mem_dedup.mp memberB) same))

/-- Ranking is preserved when repeated deliveries are removed. -/
theorem normalize_ranked (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole) :
    StateExecutableFreeze.Ranked (normalize whole) := by
  obtain ⟨rank,ordered⟩ := ranked
  refine ⟨rank,?_⟩
  intro child childMember parent parentMember edge
  exact ordered child (FinSet.mem_dedup.mp childMember) parent (FinSet.mem_dedup.mp parentMember) edge

/-- Concrete vector of scope values and freezer-address-to-index cache. -/
structure Pool (V : Type) where
  /-- Scope zero and appended immutable causal cuts. -/
  scopes : List V
  /-- Exact freezer identity mapped to its allocated scope. -/
  indices : List (Nat × Nat)

/-- Scope zero and every indexed cut retain their independently specified value. -/
def Valid {V : Type} (whole : V) (cut : Nat → V) (pool : Pool V) : Prop :=
  pool.scopes[0]? = some whole ∧ ∀ root scope, pool.indices.lookup root = some scope →
    pool.scopes[scope]? = some (cut root)

/-- Start with the accepted full-history scope and no cached cut indices. -/
def initial {V : Type} (whole : V) : Pool V := ⟨[whole],[]⟩

/-- A new reader constructs its initial scope invariant without supplied data. -/
theorem initial_valid {V : Type} (whole : V) (cut : Nat → V) : Valid whole cut (initial whole) := by
  constructor
  · rfl
  · intro root scope impossible; simp [initial] at impossible

/-- Intern a freezer identity, reusing an existing cut or appending exactly one
new immutable scope and recording its concrete vector index. -/
def intern {V : Type} (cut : Nat → V) (pool : Pool V) (root : Nat) : Nat × Pool V :=
  match pool.indices.lookup root with
  | some scope => (scope,pool)
  | none => (pool.scopes.length,⟨pool.scopes ++ [cut root],(root,pool.scopes.length)::pool.indices⟩)

/-- Existing indices keep the same scope value when a new cut is appended. -/
theorem lookup_append {V : Type} (scopes : List V) (scope : Nat) (value appended : V)
    (present : scopes[scope]? = some value) : (scopes ++ [appended])[scope]? = some value := by
  have bound : scope < scopes.length := by
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp present
    exact bound
  simpa [List.getElem?_append,bound] using present

/-- Scope allocation preserves all previously established scope/cache facts
and returns an index retrieving the exact requested causal cut. -/
theorem intern_refinement {V : Type} (whole : V) (cut : Nat → V) (pool : Pool V) (root : Nat)
    (valid : Valid whole cut pool) :
    Valid whole cut (intern cut pool root).2 ∧
      (intern cut pool root).2.scopes[(intern cut pool root).1]? = some (cut root) ∧
      (intern cut pool root).2.indices.lookup root = some (intern cut pool root).1 := by
  cases found : pool.indices.lookup root with
  | some scope => simpa only [intern,found] using And.intro valid (And.intro (valid.2 root scope found) found)
  | none =>
    simp only [intern,found]
    have last : (pool.scopes ++ [cut root])[pool.scopes.length]? = some (cut root) := by simp
    refine ⟨⟨lookup_append pool.scopes 0 whole (cut root) valid.1,?_⟩,last,by simp⟩
    intro other scope present
    by_cases same : other = root
    · subst other
      simp only [List.lookup_cons_self,Option.some.injEq] at present
      subst scope
      exact last
    · have selected : pool.indices.lookup other = some scope := by
        simpa [List.lookup,beq_eq_false_iff_ne.mpr same] using present
      exact lookup_append pool.scopes scope (cut other) (cut root) (valid.2 other scope selected)

/-- Re-interning a cached freezer does not allocate another scope. -/
theorem intern_reuse {V : Type} (cut : Nat → V) (pool : Pool V) (root scope : Nat)
    (found : pool.indices.lookup root = some scope) : intern cut pool root = (scope,pool) := by
  simp [intern,found]

/-- Allocate several field freezes through one shared scope pool. -/
def allocate {V : Type} (cut : Nat → V) : List (String × Nat) → Pool V → List (String × Nat) × Pool V
  | [],pool => ([],pool)
  | (name,root)::rest,pool =>
      let (scope,after) := intern cut pool root
      let (scopes,final) := allocate cut rest after
      ((name,scope)::scopes,final)

/-- Allocating a fresh scope never changes an earlier freezer's cached index. -/
theorem intern_preserves_lookup {V : Type} (cut : Nat → V) (pool : Pool V) (root other scope : Nat)
    (present : pool.indices.lookup other = some scope) :
    (intern cut pool root).2.indices.lookup other = some scope := by
  cases found : pool.indices.lookup root with
  | some _ => simpa [intern,found] using present
  | none =>
    have different : other ≠ root := by intro same; subst other; simp [found] at present
    simpa [intern,found,List.lookup,beq_eq_false_iff_ne.mpr different] using present

/-- A batch of field freezes retains all previously assigned scope identities. -/
theorem allocate_preserves_lookup {V : Type} (cut : Nat → V) (requests : List (String × Nat)) (pool : Pool V)
    (root scope : Nat) (present : pool.indices.lookup root = some scope) :
    (allocate cut requests pool).2.indices.lookup root = some scope := by
  induction requests generalizing pool with
  | nil => exact present
  | cons request rest ih =>
    obtain ⟨name,freezer⟩ := request
    cases step : intern cut pool freezer with
    | mk selected after =>
      have kept := intern_preserves_lookup cut pool freezer root scope present
      simp only [step] at kept
      simpa only [allocate,step] using ih after kept

/-- Shared scope allocation returns the exact cut for every field request,
including multiple fields using the same freezer and earlier reused scopes. -/
theorem allocate_refinement {V : Type} (whole : V) (cut : Nat → V) (requests : List (String × Nat))
    (pool : Pool V) (valid : Valid whole cut pool) :
    Valid whole cut (allocate cut requests pool).2 ∧
      List.Forall₂ (fun request output => output.1 = request.1 ∧
        (allocate cut requests pool).2.indices.lookup request.2 = some output.2 ∧
        (allocate cut requests pool).2.scopes[output.2]? = some (cut request.2))
        requests (allocate cut requests pool).1 := by
  induction requests generalizing pool with
  | nil => exact ⟨valid,.nil⟩
  | cons request rest ih =>
    obtain ⟨name,root⟩ := request
    cases step : intern cut pool root with
    | mk scope after =>
      have allocated := intern_refinement whole cut pool root valid
      simp only [step] at allocated
      have tail := ih after allocated.1
      cases more : allocate cut rest after with
      | mk outputs final =>
        simp only [more] at tail
        have retained := allocate_preserves_lookup cut rest after root scope allocated.2.2
        simp only [more] at retained
        simpa only [allocate,step,more] using And.intro tail.1
          (List.Forall₂.cons (a := (name,root)) (b := (name,scope)) ⟨rfl,retained,tail.1.2 root scope retained⟩ tail.2)

/-- Native address lookup chooses the immutable accepted freezer before
computing its exact executable causal cut. -/
def cutAt (whole : List Act) (root : Nat) : List Act :=
  match whole.find? (fun act => act.addr == root) with
  | none => []
  | some freezer => StateExecutableFreeze.cut whole freezer

/-- On unique accepted identities, address lookup returns that exact freezer. -/
theorem cutAt_refinement (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole)
    (unique : NodupAddr whole) (freezer : Act) (accepted : freezer ∈ whole) :
    cutAt whole freezer.addr = causalCut (fun act => act ∈ whole) whole freezer := by
  cases found : whole.find? (fun act => act.addr == freezer.addr) with
  | none =>
    have impossible := List.find?_eq_none.mp found freezer accepted
    simp at impossible
  | some selected =>
    have member := List.mem_of_find?_eq_some found
    have same : selected.addr = freezer.addr := by
      simpa using List.find?_some found
    have equal := unique.eq_of_addr member accepted same
    subst selected
    simp only [cutAt,found]
    exact StateExecutableFreeze.cut_refinement whole ranked freezer accepted

/-- Allocated native cut scopes are causal subhistories, rather than arbitrary
caller-provided values, and inherit closure from the accepted full history. -/
theorem native_cut_closed (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole)
    (unique : NodupAddr whole) (freezer : Act) (accepted : freezer ∈ whole)
    (closed : CausallyClosed (fun act => act ∈ whole) whole) :
    CausallyClosed (fun act => act ∈ whole) (cutAt whole freezer.addr) ∧
      ∀ act ∈ cutAt whole freezer.addr, act ∈ whole := by
  rw [cutAt_refinement whole ranked unique freezer accepted]
  exact ⟨StateFreezeScopes.causal_cut_closed closed freezer,fun _ member => (List.mem_filter.mp member).1⟩

/-- A pointwise list relation supplies a matching output for each input member. -/
theorem related_member {A B : Type} (relation : A → B → Prop) (inputs : List A) (outputs : List B)
    (related : List.Forall₂ relation inputs outputs) (input : A) (member : input ∈ inputs) :
    ∃ output ∈ outputs, relation input output := by
  induction related with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨_,by simp,head⟩
    · obtain ⟨output,present,value⟩ := ih inside
      exact ⟨output,List.mem_cons_of_mem _ present,value⟩

/-- The native scope vector and address cache are constructed from accepted
freezer identities, and each field's returned index reads its exact causal cut. -/
theorem native_scopes_refinement (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole)
    (unique : NodupAddr whole) (requests : List (String × Act))
    (accepted : ∀ request ∈ requests, request.2 ∈ whole) :
    let allocated := allocate (cutAt whole) (requests.map (fun (name,freezer) => (name,freezer.addr))) (initial whole)
    Valid whole (cutAt whole) allocated.2 ∧
      ∀ name freezer, (name,freezer) ∈ requests → ∃ scope, (name,scope) ∈ allocated.1 ∧
        allocated.2.indices.lookup freezer.addr = some scope ∧
        allocated.2.scopes[scope]? = some (causalCut (fun act => act ∈ whole) whole freezer) := by
  have result := allocate_refinement whole (cutAt whole) (requests.map (fun (name,freezer) => (name,freezer.addr)))
    (initial whole) (initial_valid whole (cutAt whole))
  refine ⟨result.1,?_⟩
  intro name freezer member
  have included : (name,freezer.addr) ∈ requests.map (fun (name,freezer) => (name,freezer.addr)) :=
    List.mem_map.mpr ⟨(name,freezer),member,rfl⟩
  obtain ⟨⟨field,scope⟩,present,same,cached,read⟩ := related_member _ _ _ result.2 (name,freezer.addr) included
  dsimp only at same read
  subst field
  exact ⟨scope,present,cached,by rw [read,cutAt_refinement whole ranked unique freezer (accepted _ member)]⟩

/-- Construct the reader's cut indices from field/freezer metadata and the
actual interned pool, rather than accepting a detached field/scope callback. -/
def cutScope {V : Type} (roots : List (String × Nat)) (pool : Pool V) (name : String) : Option Nat :=
  (roots.lookup name).bind (fun root => pool.indices.lookup root)

/-- Active freeze detection reads the selected freezer identity in the actual
scope vector, including incomparable nested cuts where it is absent. -/
def active (roots : List (String × Nat)) (pool : Pool (List Act)) (key : StateMemoizedReader.Key) : Bool :=
  match roots.lookup key.2,pool.scopes[key.1]? with
  | some root,some history => history.any (fun act => act.addr == root)
  | _,_ => false

/-- Scope-sensitive native cut and active-plan inputs are built from allocated
state; value, combined-fault and presentation operations remain typed leaves. -/
def operations {V : Type} (roots : List (String × Nat)) (pool : Pool (List Act))
    (leaves : StateMemoizedReader.Operations V) : StateMemoizedReader.Operations V :=
  { leaves with cut := cutScope roots pool, active := active roots pool }

/-- Active detection is exactly freezer membership in the indexed scope. -/
theorem active_iff (roots : List (String × Nat)) (pool : Pool (List Act)) (key : StateMemoizedReader.Key)
    (root : Nat) (history : List Act) (selected : roots.lookup key.2 = some root)
    (scope : pool.scopes[key.1]? = some history) :
    active roots pool key = true ↔ ∃ act ∈ history, act.addr = root := by
  simp [active,selected,scope,List.any_eq_true]

/-- Every selected accepted freezer receives a retrievable concrete scope
index; the constructed cut callback cannot silently omit a declared root. -/
theorem allocated_cut_complete (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole)
    (unique : NodupAddr whole) (requests : List (String × Act))
    (accepted : ∀ request ∈ requests, request.2 ∈ whole)
    (name : String) (freezer : Act) (present : (name,freezer) ∈ requests)
    (selected : (requests.map (fun (field,act) => (field,act.addr))).lookup name = some freezer.addr) :
    let pool := (allocate (cutAt whole) (requests.map (fun (field,act) => (field,act.addr))) (initial whole)).2
    ∃ scope, cutScope (requests.map (fun (field,act) => (field,act.addr))) pool name = some scope ∧
      pool.scopes[scope]? = some (causalCut (fun act => act ∈ whole) whole freezer) := by
  obtain ⟨scope,_,cached,history⟩ := (native_scopes_refinement whole ranked unique requests accepted).2 name freezer present
  exact ⟨scope,by simp [cutScope,selected,cached],history⟩

/-- Match the native no-root/single-root/concurrent-root scope allocation gate. -/
def uniqueRoot (whole : List Act) (verb : String) : Option Act :=
  match FinSet.dedup (whole.filter (StateExecutableFreeze.earliest whole verb)) with
  | [freezer] => some freezer
  | _ => none

/-- A selected single earliest freezer is an accepted act, not detached metadata. -/
theorem uniqueRoot_accepted (whole : List Act) (verb : String) (freezer : Act)
    (selected : uniqueRoot whole verb = some freezer) :
    freezer ∈ whole ∧ StateExecutableFreeze.earliest whole verb freezer = true := by
  cases found : FinSet.dedup (whole.filter (StateExecutableFreeze.earliest whole verb)) with
  | nil => simp [uniqueRoot,found] at selected
  | cons first rest =>
    cases rest with
    | nil =>
      simp [uniqueRoot,found] at selected
      subst freezer
      have member : first ∈ FinSet.dedup (whole.filter (StateExecutableFreeze.earliest whole verb)) := by simp [found]
      exact List.mem_filter.mp (FinSet.mem_dedup.mp member)
    | cons next more => simp [uniqueRoot,found] at selected

/-- A unique semantic earliest freezer is never omitted by root selection,
even when the delivery list repeats that freezer. -/
theorem uniqueRoot_complete (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole)
    (freezer : Act) (verb : String) (first : Earliest (fun act => act ∈ whole) verb whole freezer)
    (only : ∀ other, Earliest (fun act => act ∈ whole) verb whole other → other = freezer) :
    uniqueRoot whole verb = some freezer := by
  let eligible := FinSet.dedup (whole.filter (StateExecutableFreeze.earliest whole verb))
  have rootMember : freezer ∈ eligible := FinSet.mem_dedup.mpr (List.mem_filter.mpr
    ⟨first.1,(StateExecutableFreeze.earliest_iff whole ranked verb freezer).mpr first⟩)
  have allSame : ∀ other ∈ eligible, other = freezer := by
    intro other member
    have selected := (List.mem_filter.mp (FinSet.mem_dedup.mp member)).2
    exact only other ((StateExecutableFreeze.earliest_iff whole ranked verb other).mp selected)
  have unique : eligible.Nodup := FinSet.nodup_dedup _
  cases found : eligible with
  | nil => simp [found] at rootMember
  | cons head rest =>
    have headSame := allSame head (by simp [found])
    subst head
    cases rest with
    | nil =>
      have singleton : FinSet.dedup (whole.filter (StateExecutableFreeze.earliest whole verb)) = [freezer] := found
      simp only [uniqueRoot,singleton]
    | cons next more =>
      have nextSame := allSame next (by simp [found])
      have distinct := (List.nodup_cons.mp (found ▸ unique)).1
      exact False.elim (distinct (by simp [nextSame]))

/-- Resolve global scope requests from the actual typed freeze declarations. -/
def selectedRoots (whole : List Act) (freezes : List (String × FreezeSpec)) : List (String × Act) :=
  freezes.filterMap (fun (name,spec) => (uniqueRoot whole spec.verb).map (fun freezer => (name,freezer)))

/-- Every allocated root is constructed from the clause's accepted earliest
freezer selection, so pool construction needs no caller-supplied membership. -/
theorem selectedRoots_accepted (whole : List Act) (freezes : List (String × FreezeSpec)) :
    ∀ request ∈ selectedRoots whole freezes, request.2 ∈ whole := by
  intro request member
  obtain ⟨⟨name,spec⟩,_,selected⟩ := List.mem_filterMap.mp member
  cases found : uniqueRoot whole spec.verb with
  | none => simp [found] at selected
  | some freezer =>
    simp [found] at selected
    subst request
    exact (uniqueRoot_accepted whole spec.verb freezer found).1

/-- Fully constructed native scope allocation: full history, freeze declarations
and recognized causal identities determine every returned cut scope. -/
theorem declared_scopes_refinement (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole)
    (unique : NodupAddr whole) (freezes : List (String × FreezeSpec)) :
    let requests := selectedRoots whole freezes
    let allocated := allocate (cutAt whole) (requests.map (fun (name,freezer) => (name,freezer.addr))) (initial whole)
    Valid whole (cutAt whole) allocated.2 ∧
      ∀ name freezer, (name,freezer) ∈ requests → ∃ scope, (name,scope) ∈ allocated.1 ∧
        allocated.2.indices.lookup freezer.addr = some scope ∧
        allocated.2.scopes[scope]? = some (causalCut (fun act => act ∈ whole) whole freezer) :=
  native_scopes_refinement whole ranked unique (selectedRoots whole freezes) (selectedRoots_accepted whole freezes)

/-- Allocate the concrete native scope vector after delivery normalization. -/
def scopeAllocation (whole : List Act) (freezes : List (String × FreezeSpec)) : List (String × Nat) × Pool (List Act) :=
  let canonical := normalize whole
  let roots := (selectedRoots canonical freezes).map (fun (name,freezer) => (name,freezer.addr))
  allocate (cutAt canonical) roots (initial canonical)

/-- Complete scope-construction certificate for a raw delivery list. The
certificate refers to exactly the normalized pool used by readerOperations. -/
def ScopeSound (whole : List Act) (freezes : List (String × FreezeSpec)) : Prop :=
  let canonical := normalize whole
  let requests := selectedRoots canonical freezes
  let allocated := scopeAllocation whole freezes
  Valid canonical (cutAt canonical) allocated.2 ∧
    ∀ name freezer, (name,freezer) ∈ requests → ∃ scope, (name,scope) ∈ allocated.1 ∧
      allocated.2.indices.lookup freezer.addr = some scope ∧
      allocated.2.scopes[scope]? = some (causalCut (fun act => act ∈ canonical) canonical freezer)

/-- Ranked, content-consistent accepted deliveries construct the complete scope
certificate, including duplicate normalization, without supplied pool facts. -/
theorem normalized_scopes_sound (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (freezes : List (String × FreezeSpec)) : ScopeSound whole freezes :=
  declared_scopes_refinement (normalize whole) (normalize_ranked whole ranked)
    (normalize_unique whole consistent) freezes

/-- Build both native scope callbacks from the full observation and clause
freezes. Only typed value/fault/presentation leaf functions are retained. -/
def readerOperations {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (leaves : StateMemoizedReader.Operations V) : StateMemoizedReader.Operations V :=
  let roots := (selectedRoots (normalize whole) freezes).map (fun (name,freezer) => (name,freezer.addr))
  let pool := (scopeAllocation whole freezes).2
  operations roots pool leaves

/-- Semantic earliest-freezer selection follows from the checked ranked graph. -/
theorem uniqueRoot_earliest (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole) (verb : String)
    (freezer : Act) (selected : uniqueRoot whole verb = some freezer) :
    Earliest (fun act => act ∈ whole) verb whole freezer :=
  (StateExecutableFreeze.earliest_iff whole ranked verb freezer).mp (uniqueRoot_accepted whole verb freezer selected).2

/-- Repeated fields share a freezer scope without shifting previous indices. -/
theorem shared_scope_witness :
    let result := allocate (fun root => root*10) [("a",2),("b",3),("c",2)] (initial 7)
    (result.1 == [("a",1),("b",2),("c",1)] && result.2.scopes == [7,20,30]) = true := by decide

/-- A concrete sibling act is absent from the allocated freezer's exact cut. -/
theorem causal_scope_witness :
    let root : Act := ⟨0,"open","@a",[],[],[]⟩
    let freezer : Act := ⟨1,"close","@a",[0],[],[]⟩
    let sibling : Act := ⟨2,"mark","@b",[0],[],[]⟩
    ((cutAt [root,freezer,sibling] 1).map Act.addr == [0,1]) = true := by decide

/-- Duplicate delivery of the same freezer retains its unique selected root. -/
theorem duplicate_freezer_witness :
    let root : Act := ⟨0,"open","@a",[],[],[]⟩
    let freezer : Act := ⟨1,"close","@a",[0],[],[]⟩
    ((uniqueRoot [root,freezer,freezer] "close").map Act.addr == some 1) = true := by decide

end CBCL.StateScopePool
