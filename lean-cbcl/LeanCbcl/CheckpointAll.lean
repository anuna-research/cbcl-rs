import LeanCbcl.CheckpointKernel
import LeanCbcl.CheckpointData
import LeanCbcl.CheckpointEvidence

/-! All native heads with finite compact rows, ordered reference resolution and
explicit protocol/resource projection ports. No executable field captures history. -/
namespace CBCL.CheckpointAll
open State StateKernelSemantics StateKernelQueries StateKernelAggregates
open StateKernel StateKernelClause StateKernelSEC CheckpointSummary

/-- Native backward-reference map sources. -/
inductive MapSource where
  | events (verb field : String)
  | lwwPerSigner (verb field clock : String)
  | lwwMap (verb key field clock : String) (delete : Option String)
  deriving DecidableEq

/-- Native source plan, including event provenance. -/
def MapSource.plan : MapSource → MapPlan
  | .events v f => ⟨.withField (.verb v) f, .address, .address, f, true⟩
  | .lwwPerSigner v f c => ⟨.own v, .signer, .hlc c, f, false⟩
  | .lwwMap v k f c d => ⟨.current v (some k) d, .key k, .hlc c, f, false⟩

/-- Map sufficient data: projected events or replacement-sensitive live rows. -/
def MapSource.Data : MapSource → Type
  | .events .. => CheckpointData.Events.Summary
  | _ => Row

/-- Empty map source state. -/
def MapSource.empty (r : MapSource) : r.Data :=
  match r with
  | .events .. => []
  | .lwwPerSigner .. | .lwwMap .. => CheckpointSummary.empty

/-- Incremental map source maintenance. -/
def MapSource.step (coverage : Nat → Bool) (r : MapSource) : r.Data → Act → r.Data :=
  match r with
  | .events v f => CheckpointData.Events.step v f coverage
  | .lwwPerSigner v .. => CheckpointSummary.step (.own v) coverage
  | .lwwMap v k _ _ d => CheckpointSummary.step (.current v (some k) d) coverage

/-- Independent selected-contribution/projection invariant. -/
def MapSource.Valid (H : List Act) (r : MapSource) : r.Data → Prop :=
  match r with
  | .events v f => CheckpointData.Events.Invariant v f H
  | .lwwPerSigner v .. => Invariant (.own v) H
  | .lwwMap v k _ _ d => Invariant (.current v (some k) d) H

theorem map_empty_valid (r : MapSource) : r.Valid [] r.empty := by
  cases r <;> first
  | exact CheckpointData.Events.empty_invariant _ _
  | exact empty_invariant _

theorem map_step_valid {H : List Act} {r : MapSource} {s : r.Data}
    (valid : r.Valid H s) (e : Act) (fresh : covered H e.addr = false) :
    r.Valid (e :: H) (r.step (covered H) s e) := by
  cases r <;> first
  | exact CheckpointData.Events.step_preserves valid fresh
  | exact step_preserves valid fresh

/-- Resolved native heads. Legacy groups the unchanged seven compact reducers;
Histogram/Sum carry a resolved native source, never an earlier history closure. -/
inductive Rule where
  | legacy (rule : CheckpointKernel.Rule)
  | existsRule (verb : String)
  | count (verb : String)
  | progress (verb : String)
  | events (verb field : String)
  | setUnion (verb field : String)
  | counter (increment decrement field : String)
  | histogram (source : MapSource)
  | sum (source : MapSource)
  | boundedCounter (name : String)
  deriving DecidableEq

/-- Native expression selected after ordered reference resolution. -/
def Rule.expression : Rule → Expr
  | .legacy r => r.expression
  | .existsRule v => .existsRule (.verb v)
  | .count v => .count (.verb v)
  | .progress v => .progress v
  | .events v f => .mapped (MapSource.events v f).plan
  | .setUnion v f => .distinct (.verb v) f
  | .counter i d f => .counter (.verb i) (.verb d) f
  | .histogram source => .histogram source.plan
  | .sum source => .sum source.plan
  | .boundedCounter name => .bounded name

/-- Fixed native metadata extraction/classification boundary. -/
structure Ports where
  /-- Recognized native protocol metadata, not a claimed position verdict. -/
  protocol : Act → Repeat.Evidence
  /-- Resource verifier and its fault/tag/authority classification port. -/
  resource : CheckpointEvidence.ResourcePort

/-- Native reference input uses the same explicit evidence port. -/
def Ports.input (ports : Ports) (input : Input) (H : List Act) : Input :=
  {input with
    acts := H
    causal := CheckpointEvidence.referenceStore ports.protocol H
    resource := ports.resource.resourceInput H}

/-- Only sufficient rule-indexed data is retained. -/
def Rule.Data : Rule → Type
  | .legacy r => r.Data
  | .existsRule _ => CheckpointData.Exists.Summary
  | .count _ => CheckpointData.Count.Summary
  | .progress _ => Unit
  | .events _ _ => CheckpointData.Events.Summary
  | .setUnion _ _ => CheckpointData.SetUnion.Summary
  | .counter _ _ _ => CheckpointData.Counter.Summary
  | .histogram source => source.Data
  | .sum source => source.Data
  | .boundedCounter _ => Unit

/-- Concrete empty state. -/
def Rule.empty (r : Rule) : r.Data :=
  match r with
  | .legacy r => r.empty
  | .existsRule _ => false
  | .count _ => CheckpointData.Count.empty
  | .progress _ => ()
  | .events _ _ => []
  | .setUnion _ _ => []
  | .counter _ _ _ => CheckpointData.Counter.empty
  | .histogram source => source.empty
  | .sum source => source.empty
  | .boundedCounter _ => ()

/-- Concrete update without a ghost history argument. -/
def Rule.step (input : Input) (coverage : Nat → Bool) (r : Rule) : r.Data → Act → r.Data :=
  match r with
  | .legacy r => r.step input coverage
  | .existsRule v => CheckpointData.Exists.step v coverage
  | .count v => CheckpointData.Count.step v coverage
  | .progress _ => fun s _ => s
  | .events v f => CheckpointData.Events.step v f coverage
  | .setUnion v f => CheckpointData.SetUnion.step v f coverage
  | .counter i d f => CheckpointData.Counter.step i d f coverage
  | .histogram source => source.step coverage
  | .sum source => source.step coverage
  | .boundedCounter _ => fun s _ => s

/-- Truth invariant, not an assumed continuation equation. -/
def Rule.Valid (input : Input) (H : List Act) (r : Rule) : r.Data → Prop :=
  match r with
  | .legacy r => r.Valid input H
  | .existsRule v => CheckpointData.Exists.Invariant v H
  | .count v => CheckpointData.Count.Invariant v H
  | .progress _ => fun _ => True
  | .events v f => CheckpointData.Events.Invariant v f H
  | .setUnion v f => CheckpointData.SetUnion.Invariant v f H
  | .counter i d f => CheckpointData.Counter.Invariant i d f H
  | .histogram source => source.Valid H
  | .sum source => source.Valid H
  | .boundedCounter _ => fun _ => True

theorem rule_empty_valid (input : Input) (r : Rule) : r.Valid input [] r.empty := by
  cases r with
  | legacy r => exact CheckpointKernel.rule_empty_valid input r
  | existsRule v => exact CheckpointData.Exists.empty_invariant v
  | count v => exact CheckpointData.Count.empty_invariant v
  | events v f => exact CheckpointData.Events.empty_invariant v f
  | setUnion v f => exact CheckpointData.SetUnion.empty_invariant v f
  | counter i d f => exact CheckpointData.Counter.empty_invariant i d f
  | histogram source | sum source => exact map_empty_valid source
  | progress _ | boundedCounter _ => trivial

theorem rule_step_valid {input : Input} {H : List Act} {r : Rule} {s : r.Data}
    (valid : r.Valid input H s) (e : Act) (fresh : covered H e.addr = false) :
    r.Valid input (e :: H) (r.step input (covered H) s e) := by
  cases r <;> first
  | exact CheckpointKernel.rule_step_valid valid e fresh
  | exact CheckpointData.Exists.step_preserves valid fresh
  | exact CheckpointData.Count.step_preserves valid fresh
  | exact CheckpointData.Events.step_preserves valid fresh
  | exact CheckpointData.SetUnion.step_preserves valid fresh
  | exact CheckpointData.Counter.step_preserves valid fresh
  | exact map_step_valid valid e fresh
  | trivial

/-- Materialized map observation from sufficient source state. -/
def MapSource.render (input : Input) (r : MapSource) : r.Data → FiniteMap :=
  match r with
  | .events .. => CheckpointData.Events.map
  | .lwwPerSigner v f c => fun s => evalMap input.clock input.signerRank s.live
      ⟨.own v, .signer, .hlc c, f, false⟩
  | .lwwMap v k f c d => fun s => evalMap input.clock input.signerRank s.live
      ⟨.current v (some k) d, .key k, .hlc c, f, false⟩

theorem map_render_unique (input : Input) (r : MapSource) (s : r.Data) :
    (r.render input s).keys.Nodup := by
  cases r <;> first
  | exact CheckpointData.Events.map_keys_nodup s
  | exact uniqueKeys_nodup _

theorem map_render_eq {input : Input} {H : List Act} {r : MapSource} {s : r.Data}
    (valid : r.Valid H s) (unique : NodupAddr H) :
    MapEquivalent (r.render input s) (evalMap input.clock input.signerRank H r.plan) := by
  cases r with
  | events v f => exact CheckpointData.Events.map_native input valid unique
  | lwwPerSigner v f c =>
      exact CheckpointRender.evalMap_selected (CheckpointRender.selected_own valid)
        (select_unique unique _) input.clock input.signerRank
  | lwwMap v k f c d =>
      exact CheckpointRender.evalMap_selected (CheckpointRender.selected_current valid)
        (select_unique unique _) input.clock input.signerRank

/-- Rule rendering consumes only retained rows and selected native evidence. -/
def Rule.render (input : Input) (protocol : List CheckpointEvidence.ProtocolFact)
    (resource : List CheckpointEvidence.ResourceFact) (port : CheckpointEvidence.ResourcePort)
    (r : Rule) : r.Data → CheckpointKernel.View :=
  match r with
  | .legacy r => r.render input
  | .existsRule _ => fun s => CheckpointKernel.view (.boolean s)
  | .count _ => fun s => CheckpointKernel.view (.integer (Int.ofNat s))
  | .progress v => fun _ => CheckpointKernel.view (.integer (Int.ofNat
      (CheckpointEvidence.progress protocol input.thread v (input.limit v))))
  | .events .. => fun s => CheckpointKernel.view (.map (CheckpointData.Events.map s))
  | .setUnion .. => fun s => CheckpointKernel.view (.values (CheckpointData.SetUnion.render s))
  | .counter .. => fun s => CheckpointKernel.view (.integer s)
  | .histogram source => fun s =>
      let m := source.render input s
      CheckpointKernel.view (.histogram (histogramKeys m) (StateKernelAggregates.histogram m))
  | .sum source => fun s => CheckpointKernel.view (.integer (mapSum (source.render input s)))
  | .boundedCounter name => fun _ => CheckpointKernel.view (.resource (port.observe resource name))

/-- Legacy data heads do not inspect the protocol/resource ports. -/
theorem legacy_fold_ports (ports : Ports) (input : Input) (H : List Act)
    (r : CheckpointKernel.Rule) :
    r.fold input H = CheckpointKernel.view (evaluate (ports.input input H) [] r.expression) := by
  cases r <;> rfl

/-- Each concrete sufficient-state invariant transfers rendering to the native fold. -/
theorem rule_render_eq (ports : Ports) {input : Input} {H : List Act} {r : Rule} {s : r.Data}
    (valid : r.Valid input H s) (unique : NodupAddr H) :
    r.render input (CheckpointEvidence.project ports.protocol H)
      (CheckpointEvidence.project ports.resource.extract H) ports.resource s =
      CheckpointKernel.view (evaluate (ports.input input H) [] r.expression) := by
  cases r with
  | legacy r =>
      exact (CheckpointKernel.rule_render_eq valid unique).trans (legacy_fold_ports ports input H r)
  | existsRule v =>
      exact congrArg CheckpointKernel.view (CheckpointData.Exists.render_eq (ports.input input H) valid)
  | count v =>
      exact congrArg CheckpointKernel.view (CheckpointData.Count.render_eq (ports.input input H) valid)
  | setUnion v f =>
      exact congrArg CheckpointKernel.view (CheckpointData.SetUnion.render_eq (ports.input input H) valid)
  | counter i d f =>
      exact congrArg CheckpointKernel.view (CheckpointData.Counter.render_eq (ports.input input H) valid)
  | events v f =>
      simp only [Rule.render, Rule.expression, evaluate, Ports.input, CheckpointRender.admitted_empty]
      apply CheckpointKernel.view_eq
      simpa [Rule.render, Rule.expression, MapSource.plan, evaluate,
        CheckpointRender.admitted_empty, Ports.input, Equivalent] using
        CheckpointData.Events.map_native input valid unique
  | progress v =>
      exact congrArg CheckpointKernel.view
        (CheckpointEvidence.progress_native ports.protocol H input [] v).symm
  | boundedCounter name => rfl
  | histogram source =>
      simp only [Rule.render, Rule.expression, evaluate, Ports.input, CheckpointRender.admitted_empty]
      apply CheckpointKernel.view_eq
      exact histogram_equivalent (map_render_unique input source s) (uniqueKeys_nodup _)
        (map_render_eq valid unique)
  | sum source =>
      simp only [Rule.render, Rule.expression, evaluate, Ports.input, CheckpointRender.admitted_empty]
      apply congrArg (fun n => CheckpointKernel.view (.integer n))
      exact sum_equivalent (map_render_unique input source s) (uniqueKeys_nodup _)
        (map_render_eq valid unique)

/-- Finite named entry; no arbitrary state function over rule indices. -/
structure Entry where
  /-- Declared output name. -/
  name : String
  /-- Resolved native reducer. -/
  rule : Rule
  /-- Only this reducer's sufficient state. -/
  data : rule.Data

/-- Erase mutable data to recover the resolved schema. -/
def Entry.schema (entry : Entry) : String × Rule := (entry.name, entry.rule)

/-- Create a named empty row. -/
def Entry.empty (field : String × Rule) : Entry := ⟨field.1, field.2, field.2.empty⟩

/-- Truth of one finite row. -/
def Entry.Valid (input : Input) (H : List Act) (entry : Entry) : Prop :=
  entry.rule.Valid input H entry.data

/-- Concrete one-row update preserving schema. -/
def Entry.step (input : Input) (coverage : Nat → Bool) (entry : Entry) (e : Act) : Entry :=
  ⟨entry.name, entry.rule, entry.rule.step input coverage entry.data e⟩

/-- Sufficient state plus identity-only membership and selected native facts.
The source history appears only in propositions, never as a snapshot field. -/
structure Snapshot where
  /-- Accepted identity membership, updated by numeric IDs alone. -/
  coverage : Nat → Bool
  /-- Finite rule-indexed entries. -/
  rows : List Entry
  /-- Selected thread/verb/predecessor evidence. -/
  protocol : List CheckpointEvidence.ProtocolFact
  /-- Selected resource verifier evidence, including native tags. -/
  resource : List CheckpointEvidence.ResourceFact

/-- Ordered resolved declarations. -/
def Snapshot.schema (s : Snapshot) : List (String × Rule) := s.rows.map Entry.schema

/-- Empty checkpoint state. -/
def Snapshot.empty (fields : List (String × Rule)) : Snapshot :=
  ⟨fun _ => false, fields.map Entry.empty, [], []⟩

/-- Native accepted identity update; replay does not replace any evidence binding. -/
def Snapshot.step (ports : Ports) (input : Input) (s : Snapshot) (e : Act) : Snapshot :=
  if s.coverage e.addr then s else
    ⟨insertCoverage s.coverage e.addr,
      s.rows.map (fun row => row.step input s.coverage e),
      ⟨e.addr, ports.protocol e⟩ :: s.protocol,
      ⟨e.addr, ports.resource.extract e⟩ :: s.resource⟩

/-- Incremental finite tail fold, without prefix body lookup. -/
def Snapshot.advance (ports : Ports) (input : Input) (s : Snapshot) (tail : List Act) : Snapshot :=
  tail.foldl (Snapshot.step ports input) s

/-- Independent truth relation: exact identity coverage, projected native facts
and each concrete sufficient-state invariant. It contains no render equality. -/
def Snapshot.Valid (ports : Ports) (input : Input) (H : List Act) (s : Snapshot) : Prop :=
  (∀ id, s.coverage id = covered H id) ∧
  s.protocol = CheckpointEvidence.project ports.protocol H ∧
  s.resource = CheckpointEvidence.project ports.resource.extract H ∧
  ∀ row ∈ s.rows, row.Valid input H

theorem snapshot_empty_valid (ports : Ports) (input : Input) (fields : List (String × Rule)) :
    (Snapshot.empty fields).Valid ports input [] := by
  refine ⟨fun _ => rfl, rfl, rfl, ?_⟩
  intro row member
  obtain ⟨field, _, rfl⟩ := List.mem_map.mp member
  exact rule_empty_valid input field.2

theorem snapshot_step_valid {ports : Ports} {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid ports input H) (e : Act) :
    (s.step ports input e).Valid ports input (ingest H e) := by
  by_cases duplicate : covered H e.addr = true
  · simpa [Snapshot.step, valid.1, ingest, duplicate] using valid
  · have fresh : covered H e.addr = false := Bool.eq_false_iff.mpr duplicate
    simp only [Snapshot.step, valid.1, fresh, Bool.false_eq_true, ↓reduceIte,
      ingest, Snapshot.Valid]
    refine ⟨fun id => by simp [insertCoverage, valid.1], ?_, ?_, ?_⟩
    · simp [CheckpointEvidence.project, valid.2.1]
    · simp [CheckpointEvidence.project, valid.2.2.1]
    · intro row member
      obtain ⟨old, oldMember, equality⟩ := List.mem_map.mp member
      subst row
      have coverage : s.coverage = covered H := funext valid.1
      simpa [Entry.step, Entry.Valid, coverage] using rule_step_valid (valid.2.2.2 old oldMember) e fresh

theorem snapshot_advance_valid {ports : Ports} {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid ports input H) (tail : List Act) :
    (s.advance ports input tail).Valid ports input (replay H tail) := by
  induction tail generalizing H s with
  | nil => exact valid
  | cons e rest ih => exact ih (snapshot_step_valid valid e)

theorem snapshot_step_schema (ports : Ports) (input : Input) (s : Snapshot) (e : Act) :
    (s.step ports input e).schema = s.schema := by
  simp only [Snapshot.step]
  split
  · rfl
  · simp [Snapshot.schema, List.map_map, Entry.step, Entry.schema]

theorem snapshot_advance_schema (ports : Ports) (input : Input) (s : Snapshot) (tail : List Act) :
    (s.advance ports input tail).schema = s.schema := by
  induction tail generalizing s with
  | nil => rfl
  | cons e rest ih => exact (ih _).trans (snapshot_step_schema ports input s e)

/-- Freeze incremental sufficient state at a covered cut. -/
def Snapshot.checkpoint (ports : Ports) (input : Input) (fields : List (String × Rule))
    (H : List Act) : Snapshot := (Snapshot.empty fields).advance ports input H

theorem snapshot_checkpoint_valid (ports : Ports) (input : Input)
    (fields : List (String × Rule)) (H : List Act) :
    (Snapshot.checkpoint ports input fields H).Valid ports input (normalize H) :=
  snapshot_advance_valid (snapshot_empty_valid ports input fields) H

theorem snapshot_checkpoint_schema (ports : Ports) (input : Input)
    (fields : List (String × Rule)) (H : List Act) :
    (Snapshot.checkpoint ports input fields H).schema = fields := by
  rw [Snapshot.checkpoint, snapshot_advance_schema]
  simp [Snapshot.schema, Snapshot.empty, Entry.empty, Entry.schema, List.map_map, Function.comp_def]

/-- Render actual compact rows and selected native facts. -/
def Snapshot.render (ports : Ports) (input : Input) (s : Snapshot) : List (String × CheckpointKernel.View) :=
  s.rows.map (fun row => (row.name, row.rule.render input s.protocol s.resource ports.resource row.data))

/-- Existing whole-history native evaluator under the explicit evidence ports. -/
def fullFoldRaw (ports : Ports) (input : Input) (fields : List (String × Rule))
    (H : List Act) : List (String × CheckpointKernel.View) :=
  (evaluateFields (ports.input input H) []
    (fields.map (fun (name, rule) => (name, rule.expression)))).map
      (fun (name, value) => (name, CheckpointKernel.view value))

/-- Native baseline with the accepted store's immutable identity deduplication. -/
def fullFold (ports : Ports) (input : Input) (fields : List (String × Rule))
    (H : List Act) : List (String × CheckpointKernel.View) := fullFoldRaw ports input fields (normalize H)

theorem render_valid {ports : Ports} {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid ports input H) (unique : NodupAddr H) :
    s.render ports input = fullFoldRaw ports input s.schema H := by
  simp only [Snapshot.render, fullFoldRaw, Snapshot.schema, evaluateFields, List.map_map]
  apply List.map_congr_left
  intro row member
  simp only [Function.comp_apply, Entry.schema]
  rw [valid.2.1, valid.2.2.1]
  exact congrArg (fun observation => (row.name, observation))
    (rule_render_eq ports (valid.2.2.2 row member) unique)

/-- Imported summaries require the truthful sufficient-state invariant;
certificate signatures are not a proof of this premise. -/
theorem resume_valid_snapshot {ports : Ports} {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid ports input H) (unique : NodupAddr H) (tail : List Act) :
    (s.advance ports input tail).render ports input =
      fullFoldRaw ports input s.schema (replay H tail) := by
  have result := render_valid (snapshot_advance_valid valid tail) (replay_unique unique tail)
  rw [snapshot_advance_schema] at result
  exact result

/-- Main all-head law: concrete updates derive truth from genesis. Native
extraction/classification are explicit ports, not assumed advance correctness. -/
theorem render_advance_checkpoint (ports : Ports) (input : Input)
    (fields : List (String × Rule)) (history tail : List Act) :
    ((Snapshot.checkpoint ports input fields history).advance ports input tail).render ports input =
      fullFold ports input fields (history ++ tail) := by
  have result := resume_valid_snapshot (snapshot_checkpoint_valid ports input fields history)
    (normalize_unique history) tail
  rw [snapshot_checkpoint_schema] at result
  simpa [fullFold, normalize_append] using result

theorem render_checkpoint (ports : Ports) (input : Input)
    (fields : List (String × Rule)) (history : List Act) :
    (Snapshot.checkpoint ports input fields history).render ports input = fullFold ports input fields history := by
  simpa [Snapshot.advance] using render_advance_checkpoint ports input fields history []

theorem snapshot_duplicate_noop (ports : Ports) (input : Input) (s : Snapshot) (e : Act)
    (duplicate : s.coverage e.addr = true) : s.step ports input e = s := by
  simp [Snapshot.step, duplicate]

/-- Native sources recognized by backward-reference elaboration. -/
def mapSourceOf : StateKernelClause.Rule → Option MapSource
  | .events v f => some (.events v f)
  | .lwwPerSigner v f c => some (.lwwPerSigner v f c)
  | .lwwMap v k f c d => some (.lwwMap v k f c d)
  | _ => none

/-- Resolve every native head, using the actual preceding declaration list.
Invalid/forward references and event histograms reject just as native compilation. -/
def resolve (earlier : List (String × StateKernelClause.Rule)) :
    StateKernelClause.Rule → Option Rule
  | .initial v f => some (.legacy (.initial v f))
  | .values v f => some (.legacy (.values v f))
  | .valuesPerKey v k f d => some (.legacy (.valuesPerKey v k f d))
  | .observedSet a r f => some (.legacy (.observedSet a r f))
  | .lwwRegister v f c => some (.legacy (.lwwRegister v f c))
  | .lwwPerSigner v f c => some (.legacy (.lwwPerSigner v f c))
  | .lwwMap v k f c d => some (.legacy (.lwwMap v k f c d))
  | .existsRule v => some (.existsRule v)
  | .count v => some (.count v)
  | .progress v => some (.progress v)
  | .events v f => some (.events v f)
  | .setUnion v f => some (.setUnion v f)
  | .counter i d f => some (.counter i d f)
  | .boundedCounter name => some (.boundedCounter name)
  | .histogram reference => do
      let raw ← earlier.lookup reference
      if histogramAllowed raw then
        let source ← mapSourceOf raw
        some (.histogram source)
      else none
  | .sum reference => do
      let raw ← earlier.lookup reference
      let source ← mapSourceOf raw
      some (.sum source)

theorem map_source_native {raw : StateKernelClause.Rule} {source : MapSource}
    (resolved : mapSourceOf raw = some source) : mapPlanOf raw = some source.plan := by
  cases raw <;> simp only [mapSourceOf, reduceCtorEq, Option.some.injEq] at resolved
  all_goals subst source; rfl

/-- Resolved expressions are the existing native elaborator's expressions. -/
theorem native_expression (earlier : List (String × StateKernelClause.Rule))
    (raw : StateKernelClause.Rule) (r : Rule) (resolved : resolve earlier raw = some r) :
    compileRule earlier raw = some r.expression := by
  cases raw with
  | histogram reference =>
      cases lookup : earlier.lookup reference with
      | none => simp [resolve, lookup] at resolved
      | some raw =>
          by_cases allowed : histogramAllowed raw = true
          · cases sourceEq : mapSourceOf raw with
            | none => simp [resolve, lookup, allowed, sourceEq] at resolved
            | some source =>
                have eq : r = .histogram source := by
                  simpa [resolve, lookup, allowed, sourceEq] using resolved.symm
                subst r
                simp [compileRule, lookup, allowed, map_source_native sourceEq,
                  Rule.expression, mapPlan_histogram]
          · simp [resolve, lookup, allowed] at resolved
  | sum reference =>
      cases lookup : earlier.lookup reference with
      | none => simp [resolve, lookup] at resolved
      | some raw =>
          cases sourceEq : mapSourceOf raw with
          | none => simp [resolve, lookup, sourceEq] at resolved
          | some source =>
              have eq : r = .sum source := by simpa [resolve, lookup, sourceEq] using resolved.symm
              subst r
              simp [compileRule, lookup, map_source_native sourceEq, Rule.expression, mapPlan_sum]
  | _ =>
      simp only [resolve, Option.some.injEq] at resolved
      subst r
      rfl

/-- Ordered clause elaboration with no forward references or reordered fields. -/
def resolveFields (earlier : List (String × StateKernelClause.Rule)) :
    List (String × StateKernelClause.Rule) → Option (List (String × Rule))
  | [] => some []
  | (name, raw) :: rest => do
      let r ← resolve earlier raw
      let tail ← resolveFields (earlier ++ [(name, raw)]) rest
      some ((name, r) :: tail)

theorem native_compile_fields (earlier rawFields)
    (fields : List (String × Rule)) (resolved : resolveFields earlier rawFields = some fields) :
    compileFields earlier rawFields =
      some (fields.map (fun (name, rule) => (name, rule.expression))) := by
  induction rawFields generalizing earlier fields with
  | nil =>
      have eq : fields = [] := by simpa [resolveFields] using resolved.symm
      subst fields
      rfl
  | cons field rest ih =>
      obtain ⟨name, raw⟩ := field
      cases headEq : resolve earlier raw with
      | none => simp [resolveFields, headEq] at resolved
      | some r =>
          cases tailEq : resolveFields (earlier ++ [(name, raw)]) rest with
          | none => simp [resolveFields, headEq, tailEq] at resolved
          | some tail =>
              have eq : fields = (name, r) :: tail := by
                simpa [resolveFields, headEq, tailEq] using resolved.symm
              subst fields
              simp [compileFields, native_expression earlier raw r headEq, ih _ _ tailEq]

/-- The successful raw declaration list compiles as the actual native clause. -/
theorem native_compile_clause (input : Input) (rawFields : List (String × StateKernelClause.Rule))
    (fields : List (String × Rule)) (resolved : resolveFields [] rawFields = some fields)
    (uniqueNames : (rawFields.map Prod.fst).Nodup) :
    compileClause input ⟨rawFields, []⟩ =
      some ⟨[], fields.map (fun (name, rule) => (name, rule.expression))⟩ := by
  simp [compileClause, compileDomains, uniqueNames, native_compile_fields [] rawFields fields resolved]

/-- All-head endpoint against the unchanged native ordered-field evaluator.
Successful resolution is a syntactic native-source condition, not a correctness premise. -/
theorem render_advance_native_clause (ports : Ports) (input : Input)
    (rawFields : List (String × StateKernelClause.Rule)) (fields : List (String × Rule))
    (expressions : List (String × Expr))
    (resolved : resolveFields [] rawFields = some fields)
    (compiled : compileFields [] rawFields = some expressions) (history tail : List Act) :
    ((Snapshot.checkpoint ports input fields history).advance ports input tail).render ports input =
      (evaluateFields (ports.input input (normalize (history ++ tail))) [] expressions).map
        (fun (name, value) => (name, CheckpointKernel.view value)) := by
  have expressionsEq := native_compile_fields [] rawFields fields resolved
  rw [compiled] at expressionsEq
  have eq := Option.some.inj expressionsEq
  rw [eq, render_advance_checkpoint]
  rfl

/-- Every native map source has a compact counterpart. -/
theorem map_source_complete {raw : StateKernelClause.Rule}
    (source : StateKernelClause.MapSource raw) : ∃ r, mapSourceOf raw = some r := by
  cases source <;> exact ⟨_, rfl⟩

/-- No well-formed head is silently omitted from the all-head adapter. -/
theorem resolve_complete (earlier : List (String × StateKernelClause.Rule))
    (raw : StateKernelClause.Rule) (wf : WellFormedRule earlier raw) :
    ∃ r, resolve earlier raw = some r := by
  cases raw with
  | histogram reference =>
      obtain ⟨source, lookup, allowed⟩ := wf
      obtain ⟨r, sourceEq⟩ := map_source_complete (histogram_source_map allowed)
      exact ⟨.histogram r, by
        simp [resolve, lookup, (histogram_allowed_correct source).mpr allowed, sourceEq]⟩
  | sum reference =>
      obtain ⟨source, lookup, map⟩ := wf
      obtain ⟨r, sourceEq⟩ := map_source_complete map
      exact ⟨.sum r, by simp [resolve, lookup, sourceEq]⟩
  | _ => exact ⟨_, rfl⟩

/-- Every well-formed ordered native field list has a compact implementation. -/
theorem resolve_fields_complete {earlier rawFields : List (String × StateKernelClause.Rule)}
    (wf : WellFormedFields earlier rawFields) : ∃ fields, resolveFields earlier rawFields = some fields := by
  induction wf with
  | nil => exact ⟨[], rfl⟩
  | cons earlier name rule rest head _ ih =>
      obtain ⟨r, resolved⟩ := resolve_complete earlier rule head
      obtain ⟨fields, tail⟩ := ih
      exact ⟨(name, r) :: fields, by simp [resolveFields, resolved, tail]⟩

/-- Query the existing native resolver against retained protocol metadata.
Admission policy/R5 interprets this result; this query does not invent a verdict. -/
def Snapshot.position (s : Snapshot) (fuel thread : Nat) (verb : String) (limit id : Nat) :
    Repeat.Result :=
  Repeat.resolve fuel (CheckpointEvidence.materialize s.protocol) thread verb limit id

/-- Truthful snapshots answer exactly the native history-derived position query. -/
theorem position_valid {ports : Ports} {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid ports input H) (fuel thread : Nat) (verb : String) (limit id : Nat) :
    s.position fuel thread verb limit id =
      Repeat.resolve fuel (CheckpointEvidence.referenceStore ports.protocol H) thread verb limit id := by
  simp only [Snapshot.position, valid.2.1, CheckpointEvidence.materialize_project]

/-- Position resumption is derived from concrete projected fact updates, with
no hypothesis that a cached progress maximum suffices for R5. -/
theorem position_advance_checkpoint (ports : Ports) (input : Input)
    (fields : List (String × Rule)) (history tail : List Act)
    (fuel thread : Nat) (verb : String) (limit id : Nat) :
    ((Snapshot.checkpoint ports input fields history).advance ports input tail).position
      fuel thread verb limit id =
      Repeat.resolve fuel
        (CheckpointEvidence.referenceStore ports.protocol (normalize (history ++ tail)))
        thread verb limit id := by
  have result := position_valid
    (snapshot_advance_valid (snapshot_checkpoint_valid ports input fields history) tail)
    fuel thread verb limit id
  simpa [normalize_append] using result

/-- Selected resource facts after continuation are exactly the reference
projection. Soundness of native extraction/classification remains an explicit port. -/
theorem resource_facts_advance_checkpoint (ports : Ports) (input : Input)
    (fields : List (String × Rule)) (history tail : List Act) :
    ((Snapshot.checkpoint ports input fields history).advance ports input tail).resource =
      CheckpointEvidence.project ports.resource.extract (normalize (history ++ tail)) := by
  have valid := snapshot_advance_valid (snapshot_checkpoint_valid ports input fields history) tail
  simpa [normalize_append] using valid.2.2.1

/-- Every well-formed domain-free native clause, across the complete head
inventory, has a compact implementation with the native continuation result.
Only native syntactic well-formedness and distinct names are required here;
no hypothesis assumes the truth or correctness of a checkpoint update. -/
theorem render_advance_wellformed_clause (ports : Ports) (input : Input)
    (rawFields : List (String × StateKernelClause.Rule))
    (wellFormed : WellFormedFields [] rawFields) (uniqueNames : (rawFields.map Prod.fst).Nodup)
    (history tail : List Act) :
    ∃ (fields : List (String × Rule)) (compiled : Compiled),
      resolveFields [] rawFields = some fields ∧
      compileClause input ⟨rawFields, []⟩ = some compiled ∧
      ((Snapshot.checkpoint ports input fields history).advance ports input tail).render ports input =
        (evaluateFields (ports.input input (normalize (history ++ tail))) compiled.domains compiled.fields).map
          (fun (name, value) => (name, CheckpointKernel.view value)) := by
  obtain ⟨fields, resolved⟩ := resolve_fields_complete wellFormed
  refine ⟨fields, ⟨[], fields.map (fun (name, rule) => (name, rule.expression))⟩,
    resolved, native_compile_clause input rawFields fields resolved uniqueNames, ?_⟩
  rw [render_advance_checkpoint]
  rfl

end CBCL.CheckpointAll
