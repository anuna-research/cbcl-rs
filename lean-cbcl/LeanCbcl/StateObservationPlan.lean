import LeanCbcl.StateObservation

/-! Typed value-dependency semantics. Unlike a free display/error pair, every
constructor fixes its required fault path. Derived maps consume the actual
source payload, including a frozen source's historical value. -/
namespace CBCL.StateObservationPlan
open State StateLift StateLVar StateObservation

/-- The pending, snapshot, contextual, reached, and frozen data observations. -/
inductive Data (V : Type) where
  | pending
  | snapshot (value : V)
  | context (value : V)
  | reached (value : V)
  | frozen (freezer : Nat) (value : V) (excluded : FinSet Act)

/-- Extract the rendered value from a data observation when available. -/
def Data.payload {V : Type} : Data V → Option V
  | .pending => none
  | .snapshot v | .context v | .reached v | .frozen _ v _ => some v

/-- A compositional observation plan retaining both data and fault channels. -/
inductive Plan : Type → Type 1 where
  | snapshot {V : Type} (display : FinSet Act → V) : Plan V
  | read {V : Type} (contextual : Bool) (value : FinSet Act → Option V) : Plan V
  | guardCertified {V : Type} (spec : ErrorSpec) (source : Plan V) : Plan V
  | context (decode : Act → Option Val) : Plan Val
  | contextAs {V : Type} (decode : Act → Option Val) (embed : Val → V) : Plan V
  | guardThreshold {V : Type} (spec : ThresholdSpec) (source : Plan V) : Plan V
  | domain {V : Type} (verb key opener field : String)
      (display : FinSet Act → V) : Plan V
  | embed {V W : Type} (function : V → W) (source : Plan V) : Plan W
  | map {V W : Type} (function : V → W) (source : Plan V) : Plan W
  | pair {V W : Type} (left : Plan V) (right : Plan W) : Plan (V × W)
  | guardDomain {V : Type} (opener field : String) (source : Plan V) : Plan V
  | resource {V : Type} (config : CheckpointEvidence.ResourceConfig)
      (decode : Act → CheckpointEvidence.ResourceData) (source : Plan V) : Plan V
  | threshold {V : Type} (spec : ThresholdSpec) (source : Plan V) : Plan spec.Carrier
  | thresholdRaw {V C Q : Type} (alternatives : List Q) (test : Q → C → Bool)
      (state : FinSet Act → C) (source : Plan V) : Plan Q
  | thresholdOn {V Q : Type} (alternatives : List Q) (test : Q → V → Bool) (source : Plan V) : Plan Q
  | freeze {V : Type} (spec : FreezeSpec) (source : Plan V) : Plan V

/-- Extract the compositional fault path of a plan. -/
def path : {V : Type} → Plan V → Path
  | _, .snapshot _ => .clear
  | _, .read _ _ => .clear
  | _, .guardCertified spec source => .join (.certified spec) (path source)
  | _, .context decode => .context decode
  | _, .contextAs decode _ => .context decode
  | _, .guardThreshold spec source => .join (.threshold spec) (path source)
  | _, .domain _ _ opener field _ => .domain opener field
  | _, .embed _ source => path source
  | _, .map _ source => path source
  | _, .pair left right => .join (path left) (path right)
  | _, .guardDomain opener field source => .join (.domain opener field) (path source)
  | _, .resource config decode source => .join (.resource config decode) (path source)
  | _, .threshold spec source => .join (.threshold spec) (path source)
  | _, .thresholdRaw _ _ _ source => path source
  | _, .thresholdOn _ _ source => path source
  | _, .freeze spec source => .freeze spec.verb spec.contributes spec.policy (path source)

/-- Render an optional value as a pending, contextual, or snapshot observation. -/
def optionalData {V : Type} (contextual : Bool) : Option V → Data V
  | none => .pending
  | some value => if contextual then .context value else .snapshot value

/-- Apply a value projection while preserving observation status. -/
def mapData {V W : Type} (f : V → W) (source : Data V) : Data W :=
  match source.payload with
  | none => .pending
  | some v => .snapshot (f v)

/-- Literal representation embedding preserves the public observation tag;
derived functions deliberately use mapData instead. -/
def embedData {V W : Type} (f : V → W) : Data V → Data W
  | .pending => .pending
  | .snapshot v => .snapshot (f v)
  | .context v => .context (f v)
  | .reached v => .reached (f v)
  | .frozen freezer v excluded => .frozen freezer (f v) excluded

/-- Pair data observations while preserving pending and fault-independent status. -/
def pairData {V W : Type} (left : Data V) (right : Data W) : Data (V × W) :=
  match left.payload, right.payload with
  | some l, some r => .snapshot (l,r)
  | _, _ => .pending

/-- Render a causal-cut observation with its freeze metadata. -/
def frozenData {V : Type} : FreezeRead (Data V) → Data V
  | .snapshot value => value
  | .fault _ => .pending -- The separate fault channel is rendered first.
  | .frozen freezer value excluded =>
    match value.payload with
    | none => .pending
    | some v => .frozen freezer v excluded

/-- Evaluate the plan's data channel on the supplied accepted history. -/
noncomputable def data (world : Act → Prop) : {V : Type} → Plan V → List Act → Data V
  | _, .snapshot display, A => .snapshot (display (rawHistory A))
  | _, .read contextual value, A => optionalData contextual (value (rawHistory A))
  | _, .guardCertified _ source, A => data world source A
  | _, .context decode, A => match StateContext.read decode A with
      | .pending | .fault _ => .pending
      | .value v => .context v
  | _, .contextAs decode embed, A => match StateContext.read decode A with
      | .pending | .fault _ => .pending
      | .value v => .context (embed v)
  | _, .guardThreshold _ source, A => data world source A
  | _, .domain verb key opener field display, A =>
      .snapshot (display (FinSet.mk (initialDomain verb key opener field A)))
  | _, .embed f source, A => embedData f (data world source A)
  | _, .map f source, A => mapData f (data world source A)
  | _, .pair left right, A => pairData (data world left A) (data world right A)
  | _, .guardDomain _ _ source, A => data world source A
  | _, .resource _ _ source, A => data world source A
  | _, .threshold spec source, A =>
      letI := spec.algebra
      match thresholdRead spec.alternatives (lift spec.contribution A)
          (errors world (path source) A).isSome (rawHistory A) with
      | .pending | .fault _ => .pending
      | .reached q => .reached q
  | _, .thresholdRaw alternatives test state _, A =>
      match alternatives.find? (fun q => test q (state (rawHistory A))) with
      | none => .pending
      | some q => .reached q
  | _, .thresholdOn alternatives test source, A =>
      match (data world source A).payload with
      | none => .pending
      | some value => match alternatives.find? (fun q => test q value) with
          | none => .pending
          | some q => .reached q
  | _, .freeze spec source, A => frozenData (freezeRead world spec.verb spec.contributes spec.policy
      (errors world (path source) A) (fun C => data world source C) A)

/-- The combined terminal-error and data channels of an observation. -/
inductive Observation (V : Type) where
  | data (value : Data V)
  | fault (evidence : Evidence)

/-- Read the plan's combined data and terminal-error channels. -/
noncomputable def observe {V : Type} (world : Act → Prop) (plan : Plan V) (A : List Act) : Observation V :=
  match errors world (path plan) A with
  | some e => .fault e
  | none => .data (data world plan A)

/-- Nested freezes need the source's invariance only on unique accepted
histories. Both cuts inherit this property from their parent histories. -/
theorem freezeRead_setEq_unique {V : Type} {world : Act → Prop} {verb : String}
    {contributes : Act → Prop} {policy : Bool} {A B : List Act}
    (same : SetEq A B) (ua : NodupAddr A) (ub : NodupAddr B)
    (read : List Act → V)
    (invariant : ∀ {X Y}, NodupAddr X → NodupAddr Y → SetEq X Y → read X = read Y)
    (rawA rawB : Error) (rawSame : rawA = rawB) :
    freezeRead world verb contributes policy rawA read A =
      freezeRead world verb contributes policy rawB read B := by
  classical
  have conflicts : (∃ a b, FreezeConflict world verb contributes policy A a b) ↔
      (∃ a b, FreezeConflict world verb contributes policy B a b) := by
    simp only [freezeConflict_setEq same]
  unfold freezeRead
  simp only [rawSame,conflicts,freezeEvidence_setEq same]
  by_cases fault : rawB.isSome ∨ ∃ a b, FreezeConflict world verb contributes policy B a b
  · simp only [if_pos fault]
  · simp only [if_neg fault]
    have noConcurrent : ∀ a b, Earliest world verb A a → Earliest world verb A b → a.addr = b.addr := by
      intro a b left right
      by_cases equal : a.addr = b.addr
      · exact equal
      · exact False.elim (fault (Or.inr ⟨a,b,.concurrent
          ((earliest_setEq same a).mp left) ((earliest_setEq same b).mp right) equal⟩))
    rw [earliest_find_setEq same ua noConcurrent]
    cases found : B.find? (fun f => decide (Earliest world verb B f)) with
    | none => exact congrArg FreezeRead.snapshot (invariant ua ub same)
    | some f =>
      have excluded : FinSet.mk (A.filter (fun a => decide (contributes a ∧ ¬Ancestor world a f))) =
          FinSet.mk (B.filter (fun a => decide (contributes a ∧ ¬Ancestor world a f))) := by
        apply FinSet.ext
        intro a
        simp only [FinSet.mem_mk,List.mem_filter,same a]
      simp only
      have ucutA : NodupAddr (causalCut world A f) := by unfold causalCut; exact ua.filter _
      have ucutB : NodupAddr (causalCut world B f) := by unfold causalCut; exact ub.filter _
      rw [invariant ucutA ucutB (causalCut_setEq (world := world) same f),excluded]

/-- Value-dependency evaluation is set-extensional, including nested frozen
sources rather than merely unioning their fault paths. -/
theorem data_setEq {V : Type} (world : Act → Prop) (plan : Plan V) {A B : List Act}
    (ua : NodupAddr A) (ub : NodupAddr B) (same : SetEq A B) : data world plan A = data world plan B := by
  classical
  induction plan generalizing A B with
  | snapshot display => simp only [data,rawHistory_setEq same]
  | read contextual value => simp only [data,rawHistory_setEq same]
  | guardCertified _ source ih => exact ih ua ub same
  | context decode => simp only [data,StateContext.read_setEq decode same]
  | contextAs decode embed => simp only [data,StateContext.read_setEq decode same]
  | guardThreshold _ source ih => exact ih ua ub same
  | domain verb key opener field display =>
    apply congrArg (fun carrier => Data.snapshot (display carrier))
    apply FinSet.ext
    intro a
    simp only [FinSet.mem_mk]
    exact initialDomain_invariant same verb key opener field a
  | embed f source ih => simp only [data,ih ua ub same]
  | map f source ih => simp only [data,ih ua ub same]
  | pair left right il ir => simp only [data,il ua ub same,ir ua ub same]
  | guardDomain _ _ source ih => exact ih ua ub same
  | resource _ _ source ih => exact ih ua ub same
  | threshold spec source ih =>
    letI := spec.algebra
    simp only [data,lift_setEq spec.contribution same,errors_setEq world (path source) same,rawHistory_setEq same]
  | thresholdRaw alternatives test state source ih => simp only [data,rawHistory_setEq same]
  | thresholdOn alternatives test source ih => simp only [data,ih ua ub same]
  | freeze spec source ih =>
    apply congrArg frozenData
    exact freezeRead_setEq_unique same ua ub (fun C => data world source C)
      (fun x y h => ih x y h) _ _ (errors_setEq world (path source) same)

theorem observe_setEq {V : Type} (world : Act → Prop) (plan : Plan V) {A B : List Act}
    (ua : NodupAddr A) (ub : NodupAddr B) (same : SetEq A B) : observe world plan A = observe world plan B := by
  unfold observe
  rw [errors_setEq world (path plan) same,data_setEq world plan ua ub same]

/-- Read every compiled field in declaration order. -/
noncomputable def observeClause {Index : Type} {Value : Index → Type}
    (world : Act → Prop) (plans : (i : Index) → Plan (Value i)) (A : List Act) :=
  fun i => observe world (plans i) A

open StateKernelDelivery AdmissionStratification StateRefinement

theorem composed_strong_eventual_consistency {adm : Admission} {auth : Act → Prop}
    {H : ValidHistory adm} (left right : Replica adm auth H)
    {Index : Type} {Value : Index → Type} (plans : (i : Index) → Plan (Value i))
    (history : List Act) (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m →
      observeClause H.contains plans (left.run n).accepted =
      observeClause H.contains plans (right.run m).accepted := by
  obtain ⟨tl,hl⟩ := finite_history_stabilizes left history complete
  obtain ⟨tr,hr⟩ := finite_history_stabilizes right history complete
  refine ⟨max tl tr,fun n m hn hm => ?_⟩
  funext i
  exact observe_setEq H.contains (plans i)
    (reachable_wellFormed (behavior_reachable left.behavior n)).accepted_unique
    (reachable_wellFormed (behavior_reachable right.behavior m)).accepted_unique
    (fun a => (hl n (by omega) a).trans (hr m (by omega) a).symm)

theorem eventual_composed_fault {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    {V : Type} (plan : Plan V) (atTime : Nat) {e : Evidence}
    (fault : observe H.contains plan (left.run atTime).accepted = .fault e) :
    ∃ t, ∀ n, t ≤ n → ∃ enlarged,
      observe H.contains plan (right.run n).accepted = .fault enlarged ∧ ∀ id ∈ e, id ∈ enlarged := by
  have original : errors H.contains (path plan) (left.run atTime).accepted = some e := by
    cases h : errors H.contains (path plan) (left.run atTime).accepted with
    | none => simp [observe,h] at fault
    | some old =>
      have equal : old = e := by simpa [observe,h] using fault
      simpa [equal] using h
  obtain ⟨t,all⟩ := witness_dissemination left right (left.run atTime).accepted atTime (by simp)
  refine ⟨t,fun n hn => ?_⟩
  obtain ⟨f,h,includes⟩ := errors_persist H.contains (path plan)
    (replica_causal_closed left admission atTime) (all n hn) e original
  exact ⟨f,by simp [observe,h],includes⟩

/-- The same exact freezer yields equal source payloads, even for derived
sources containing other freezes. Excluded metadata may still grow. -/
theorem frozen_source_agreement {V : Type} (world : Act → Prop) (source : Plan V)
    {A B : List Act} {f : Act} (ua : NodupAddr A) (ub : NodupAddr B)
    (ca : CausallyClosed world A) (cb : CausallyClosed world B) (fa : f ∈ A) (fb : f ∈ B) :
    data world source (causalCut world A f) = data world source (causalCut world B f) := by
  have uca : NodupAddr (causalCut world A f) := by classical unfold causalCut; exact ua.filter _
  have ucb : NodupAddr (causalCut world B f) := by classical unfold causalCut; exact ub.filter _
  exact data_setEq world source uca ucb (causalCut_agreement ca cb fa fb)

/-- This is the executable composed read's success, including its dependency
fault check and reached tag, rather than a detached carrier assertion. -/
theorem threshold_read_of_success {V : Type} (world : Act → Prop) (spec : ThresholdSpec)
    (source : Plan V) (A : List Act) (q : spec.Carrier)
    (success : observe world (.threshold spec source) A = .data (.reached q)) :
    (letI := spec.algebra; thresholdRead spec.alternatives (lift spec.contribution A)
      (errors world (path source) A).isSome (rawHistory A)) = .reached q := by
  letI := spec.algebra
  unfold observe at success
  split at success
  · contradiction
  · simp only [data] at success
    cases h : thresholdRead spec.alternatives (lift spec.contribution A)
      (errors world (path source) A).isSome (rawHistory A) <;> simp [h] at success
    exact congrArg ThresholdRead.reached success

theorem threshold_quasi_determinism {V : Type} (world : Act → Prop) (spec : ThresholdSpec)
    (source : Plan V) {A B : List Act} {a b : spec.Carrier}
    (left : observe world (.threshold spec source) A = .data (.reached a))
    (right : observe world (.threshold spec source) B = .data (.reached b)) :
    a = b ∨ ∃ e, observe world (.threshold spec source) (A ++ B) = .fault e := by
  classical
  letI := spec.algebra
  rcases thresholdRead_agreement spec.incompatible (threshold_read_of_success world spec source A a left)
      (threshold_read_of_success world spec source B b right) with equal | top
  · exact Or.inl equal
  · have joined : lift spec.contribution (A ++ B) = ⊤ := by simpa only [lift_append] using top
    right
    cases h : errors world (path source) (A ++ B) with
    | none => exact ⟨acceptedEvidence (A ++ B),by simp [observe,path,errors,thresholdError,joined,h,unionError]⟩
    | some e => exact ⟨acceptedEvidence (A ++ B) ∪ e,by simp [observe,path,errors,thresholdError,joined,h,unionError]⟩

/-- A derived map consumes the sealed payload, not a fresh unfrozen fold. -/
theorem derived_frozen_payload {V W : Type} (world : Act → Prop) (source : Plan V)
    (f : V → W) (A : List Act) (freezer : Nat) (v : V) (excluded : FinSet Act)
    (sealed : data world source A = .frozen freezer v excluded) :
    data world (.map f source) A = .snapshot (f v) := by
  simp [data,sealed,mapData,Data.payload]

theorem threshold_dependency_fault_first {V : Type} (world : Act → Prop) (spec : ThresholdSpec)
    (source : Plan V) (A : List Act) (e : Evidence)
    (fault : errors world (path source) A = some e) :
    ∃ enlarged, observe world (.threshold spec source) A = .fault enlarged ∧
      ∀ id ∈ e, id ∈ enlarged := by
  cases h : thresholdError spec A with
  | none => exact ⟨e,by simp [observe,path,errors,h,fault,unionError],fun _ h => h⟩
  | some f => exact ⟨f ∪ e,by simp [observe,path,errors,h,fault,unionError],fun _ h => Or.inr h⟩

theorem thresholdOn_dependency_fault_first {V Q : Type} (world : Act → Prop)
    (alternatives : List Q) (test : Q → V → Bool) (source : Plan V) (A : List Act) (e : Evidence)
    (fault : errors world (path source) A = some e) :
    observe world (.thresholdOn alternatives test source) A = .fault e := by
  simp [observe,path,fault]

/-- Embedding immutable context metadata preserves its public read tag. -/
theorem contextAs_value {V : Type} (world : Act → Prop) (decode : Act → Option Val)
    (embed : Val → V) (A : List Act) (value : Val) (read : StateContext.read decode A = .value value) :
    observe world (.contextAs decode embed) A = .data (.context (embed value)) := by
  simp [observe,path,errors,contextError,data,read]

/-- A top carrier remains a fault even when only its projection is displayed. -/
theorem guardThreshold_top_fault {V : Type} (world : Act → Prop) (spec : ThresholdSpec)
    (source : Plan V) (A : List Act) (top : letI := spec.algebra; lift spec.contribution A = ⊤) :
    ∃ evidence, observe world (.guardThreshold spec source) A = .fault evidence := by
  cases e : errors world (path source) A with
  | none => exact ⟨acceptedEvidence A,by simp [observe,path,errors,thresholdError,top,e,unionError]⟩
  | some evidence => exact ⟨acceptedEvidence A ∪ evidence,by simp [observe,path,errors,thresholdError,top,e,unionError]⟩

theorem embed_preserves_reached {V W : Type} (world : Act → Prop) (embed : V → W)
    (source : Plan V) (A : List Act) (value : V)
    (reached : observe world source A = .data (.reached value)) :
    observe world (.embed embed source) A = .data (.reached (embed value)) := by
  cases e : errors world (path source) A with
  | some evidence => simp [observe,e] at reached
  | none =>
    have read : data world source A = .reached value := by simpa [observe,e] using reached
    simp [observe,path,data,e,read,embedData]

end CBCL.StateObservationPlan
