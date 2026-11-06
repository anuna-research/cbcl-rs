import LeanCbcl.StateKernelExtensions

/-! SPEC-036 typed state kernel and independent expression denotation. -/
namespace CBCL.StateKernel
open CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries
open CBCL.StateKernelAggregates CBCL.StateKernelExtensions

/-- Immutable recognized inputs; resource classification is an explicit port. -/
structure Input where
  /-- Accepted raw history, before application-data domains. -/
  acts : List Act
  /-- Unique protocol opener name from installed static context. -/
  opener : String
  /-- Recognized physical/logical clock evidence. -/
  clock : Clock
  /-- Signer byte-order abstraction. -/
  signerRank : SignerRank
  /-- Same-thread immutable protocol-position evidence. -/
  causal : Repeat.Store
  /-- Pinned thread. -/
  thread : Nat
  /-- Installed expanded position limit per verb. -/
  limit : String → Nat
  /-- Typed resource-verifier results, outside ordinary data selection. -/
  resource : String → ResourceInput

/-- Map of distinct concurrent values; supported keys are explicit. -/
structure ValueMap where
  /-- Distinct keys with at least one current write carrying that key. -/
  keys : List Val
  /-- Membership of a value under a supported key. -/
  read : Val → Val → Bool

/-- Typed extensional observations. Enumeration order is not rendering order. -/
inductive Observation where
  | cell (value : Cell)
  | boolean (value : Bool)
  | integer (value : Int)
  | values (member : Val → Bool)
  | map (value : FiniteMap)
  | valueMap (value : ValueMap)
  | histogram (keys : List Val) (counts : Val → Nat)
  | resource (value : ResourceView)

/-- Complete compositional algebra for the fixed surface-rule vocabulary. -/
inductive Expr where
  | scalar (source : Selection) (policy : Policy) (field : String)
  | existsRule (source : Selection)
  | count (source : Selection)
  | distinct (source : Selection) (field : String)
  | mapped (plan : MapPlan)
  | valuesBy (source : Selection) (key field : String)
  | counter (increments decrements : Selection) (field : String)
  | histogram (plan : MapPlan)
  | sum (plan : MapPlan)
  | progress (verb : String)
  | bounded (resource : String)

/-- Concrete multi-value grouping. -/
def evalValuesBy (A : List Act) (source : Selection) (key field : String) : ValueMap :=
  let T := select A source
  ⟨uniqueKeys (T.filterMap (fun a => a.get key)), fun k =>
    has field (T.filter (fun a => a.get key == some k))⟩

/-- Independent support and value membership for keyed multi-value observations. -/
def ValueMapMeaning (P : Act → Prop) (source : Selection) (key field : String)
    (result : ValueMap) : Prop :=
  result.keys.Nodup ∧
  (∀ k, k ∈ result.keys ↔ ∃ a, Selected P source a ∧ a.get key = some k) ∧
  ∀ k ∈ result.keys, ∀ v, result.read k v = true ↔
    ∃ a, Selected P source a ∧ a.get key = some k ∧ a.get field = some v

/-- Every group and concurrent value is present exactly when specified. -/
theorem values_by_correct (A : List Act) (source : Selection) (key field : String) :
    ValueMapMeaning (fun a => a ∈ A) source key field (evalValuesBy A source key field) := by
  refine ⟨uniqueKeys_nodup _, ?_, ?_⟩
  · intro k
    simp only [evalValuesBy, uniqueKeys_member, List.mem_filterMap, select_correct]
  · intro k _ v
    simp only [evalValuesBy, has, List.any_eq_true, List.mem_filter, select_correct, beq_iff_eq]
    constructor
    · rintro ⟨a, ⟨selected, key⟩, value⟩; exact ⟨a, selected, key, value⟩
    · rintro ⟨a, selected, key, value⟩; exact ⟨a, ⟨selected, key⟩, value⟩

/-- Extensional equality ignores key enumeration order and reads outside support. -/
def ValueMapEquivalent (a b : ValueMap) : Prop :=
  (∀ k, k ∈ a.keys ↔ k ∈ b.keys) ∧ ∀ k ∈ a.keys, a.read k = b.read k

/-- The multi-value map denotation characterizes exactly the evaluator's observation. -/
theorem values_by_complete (A : List Act) (source : Selection) (key field : String)
    (result : ValueMap) : ValueMapMeaning (fun a => a ∈ A) source key field result ↔
      result.keys.Nodup ∧ ValueMapEquivalent result (evalValuesBy A source key field) := by
  have good := values_by_correct A source key field
  constructor
  · intro h
    refine ⟨h.1, fun k => (h.2.1 k).trans (good.2.1 k).symm, ?_⟩
    intro k hk
    funext v
    apply Bool.eq_iff_iff.mpr
    exact (h.2.2 k hk v).trans (good.2.2 k ((good.2.1 k).mpr ((h.2.1 k).mp hk)) v).symm
  · rintro ⟨unique, support, reads⟩
    refine ⟨unique, fun k => (support k).trans (good.2.1 k), ?_⟩
    intro k hk v
    rw [reads k hk]
    exact good.2.2 k ((support k).mp hk) v

/-- Pure expression evaluation. Progress and resource ports bypass data domains. -/
def evaluate (input : Input) (domains : List Domain) : Expr → Observation
  | .scalar source policy field => .cell (project field false
      (choose input.clock input.signerRank policy (select (admitted domains input.acts) source)))
  | .existsRule source => .boolean (!(select (admitted domains input.acts) source).isEmpty)
  | .count source => .integer (Int.ofNat (size (select (admitted domains input.acts) source)))
  | .distinct source field => .values (has field (select (admitted domains input.acts) source))
  | .mapped plan => .map (evalMap input.clock input.signerRank (admitted domains input.acts) plan)
  | .valuesBy source key field => .valueMap (evalValuesBy (admitted domains input.acts) source key field)
  | .counter inc dec field => .integer (sumField field (select (admitted domains input.acts) inc) -
      sumField field (select (admitted domains input.acts) dec))
  | .histogram plan =>
      let m := evalMap input.clock input.signerRank (admitted domains input.acts) plan
      .histogram (histogramKeys m) (histogram m)
  | .sum plan => .integer (mapSum (evalMap input.clock input.signerRank (admitted domains input.acts) plan))
  | .progress verb => .integer (Int.ofNat (protocolProgress input.causal input.thread verb (input.limit verb) input.acts))
  | .bounded name => .resource (resourceObserve (input.resource name))

/-- Independent expression semantics. No branch calls evaluation or selections. -/
def Meaning (input : Input) (domains : List Domain) : Expr → Observation → Prop
  | .scalar source policy field, .cell cell => CellMeaning input.clock input.signerRank policy
      (Selected (Admitted domains input.acts) source) field false cell
  | .existsRule source, .boolean value => Existence (Selected (Admitted domains input.acts) source) value
  | .count source, .integer value => ∃ n, Cardinality (Selected (Admitted domains input.acts) source) n ∧ value = Int.ofNat n
  | .distinct source field, .values member => Values (Selected (Admitted domains input.acts) source) field member
  | .mapped plan, .map m => MapMeaning input.clock input.signerRank (Admitted domains input.acts) plan m
  | .valuesBy source key field, .valueMap m => ValueMapMeaning (Admitted domains input.acts) source key field m
  | .counter inc dec field, .integer value => ∃ up down,
      Total (Selected (Admitted domains input.acts) inc) field up ∧
      Total (Selected (Admitted domains input.acts) dec) field down ∧ value = up - down
  | .histogram plan, .histogram keys counts => ∃ m,
      MapMeaning input.clock input.signerRank (Admitted domains input.acts) plan m ∧ HistogramMeaning m counts keys
  | .sum plan, .integer value => ∃ m,
      MapMeaning input.clock input.signerRank (Admitted domains input.acts) plan m ∧ SumMeaning m value
  | .progress verb, .integer value => ∃ n,
      ProgressMeaning input.causal input.thread verb (input.limit verb) input.acts n ∧ value = Int.ofNat n
  | .bounded name, .resource result => ResourceMeaning (input.resource name) result
  | _, _ => False

/-- Exact integer reduction after independent source selection. -/
theorem selected_total (input : Input) (unique : NodupAddr input.acts) (domains : List Domain)
    (source : Selection) (field : String) :
    Total (Selected (Admitted domains input.acts) source) field
      (sumField field (select (admitted domains input.acts) source)) := by
  refine ⟨select (admitted domains input.acts) source, ?_, ?_⟩
  · exact ⟨select_unique (admitted_unique unique domains) source, data_selection_correct unique domains source⟩
  · exact sumField_eq field _

/-- All expression constructors satisfy their independent denotation. -/
theorem evaluate_correct (input : Input) (unique : NodupAddr input.acts)
    (domains : List Domain) (expression : Expr) : Meaning input domains expression (evaluate input domains expression) := by
  cases expression with
  | scalar source policy field =>
      refine ⟨choose input.clock input.signerRank policy (select (admitted domains input.acts) source), ?_, project_correct _ _ _⟩
      apply (choice_congr (data_selection_correct unique domains source) _ _ _ _).mp
      exact choose_satisfies _ _ _ _
  | existsRule source =>
      have good := existence_correct (select (admitted domains input.acts) source)
      simpa only [Existence, data_selection_correct unique domains source] using good
  | count source =>
      exact ⟨size (select (admitted domains input.acts) source),
        ⟨select (admitted domains input.acts) source,
          ⟨select_unique (admitted_unique unique domains) source, data_selection_correct unique domains source⟩, rfl⟩, rfl⟩
  | distinct source field =>
      have good := values_correct (select (admitted domains input.acts) source) field
      simpa only [Values, data_selection_correct unique domains source] using good
  | mapped plan =>
      exact (map_meaning_congr (admitted_correct unique domains) _ _ _ _).mp (map_correct _ _ _ _)
  | valuesBy source key field =>
      have good := values_by_correct (admitted domains input.acts) source key field
      have same := fun a => selected_congr (admitted_correct unique domains) source a
      simpa only [ValueMapMeaning, same] using good
  | counter inc dec field =>
      exact ⟨_, _, selected_total input unique domains inc field,
        selected_total input unique domains dec field, rfl⟩
  | histogram plan =>
      refine ⟨evalMap input.clock input.signerRank (admitted domains input.acts) plan, ?_, histogram_correct _ (uniqueKeys_nodup _)⟩
      exact (map_meaning_congr (admitted_correct unique domains) _ _ _ _).mp (map_correct _ _ _ _)
  | sum plan =>
      refine ⟨evalMap input.clock input.signerRank (admitted domains input.acts) plan, ?_, map_sum_correct _ (uniqueKeys_nodup _)⟩
      exact (map_meaning_congr (admitted_correct unique domains) _ _ _ _).mp (map_correct _ _ _ _)
  | progress verb => exact ⟨_, progress_correct _ _ _ _ _, rfl⟩
  | bounded name => exact resource_correct _

end CBCL.StateKernel
