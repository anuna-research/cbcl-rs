import LeanCbcl.CheckpointSummary
import LeanCbcl.CheckpointCompact
import LeanCbcl.CheckpointRender

/-!
Finite, rule-indexed checkpoint profiles connected to the existing native state
kernel. The semantic renderer identifies collection enumeration orders, just as
Rust's deterministic collection renderer does. No wire-code or Rust extraction
correctness is assumed or established by this typed model theorem.
-/
namespace CBCL.CheckpointKernel
open State StateKernelSemantics StateKernelQueries StateKernel
open StateKernelClause StateKernelSEC CheckpointSummary

/-- Exactly the seven runtime-supported rules; unsupported rules have no constructor. -/
inductive Rule where
  | initial (verb field : String)
  | values (verb field : String)
  | valuesPerKey (verb key field : String) (delete : Option String)
  | observedSet (add remove field : String)
  | lwwRegister (verb field clock : String)
  | lwwPerSigner (verb field clock : String)
  | lwwMap (verb key field clock : String) (delete : Option String)
  deriving DecidableEq

/-- Embed a checkpoint-supported head into the complete native surface vocabulary. -/
def Rule.native : Rule → StateKernelClause.Rule
  | .initial v f => .initial v f
  | .values v f => .values v f
  | .valuesPerKey v k f d => .valuesPerKey v k f d
  | .observedSet a r f => .observedSet a r f
  | .lwwRegister v f c => .lwwRegister v f c
  | .lwwPerSigner v f c => .lwwPerSigner v f c
  | .lwwMap v k f c d => .lwwMap v k f c d

/-- The existing native expression selected by elaboration of this supported rule. -/
def Rule.expression : Rule → Expr
  | .initial v f => .initial v f
  | .values v f => .distinct (.current v none none) f
  | .valuesPerKey v k f d => .valuesBy (.current v (some k) d) k f
  | .observedSet a r f => .distinct (.current a (some f) (some r)) f
  | .lwwRegister v f c => .scalar (.verb v) (.hlc c) f
  | .lwwPerSigner v f c => .mapped ⟨.own v, .signer, .hlc c, f, false⟩
  | .lwwMap v k f c d => .mapped ⟨.current v (some k) d, .key k, .hlc c, f, false⟩

/-- The compact profile uses the actual native elaboration, not a second fold. -/
theorem native_expression (r : Rule) (earlier : List (String × StateKernelClause.Rule)) :
    compileRule earlier r.native = some r.expression := by
  cases r <;> rfl

/-- Rule-indexed sufficient data, bounded witnesses/winner or a scoped live row. -/
def Rule.Data : Rule → Type
  | .initial .. => CheckpointCompact.Initial.Summary
  | .lwwRegister .. => CheckpointCompact.LwwRegister.Summary
  | _ => Row

/-- The executable empty sufficient state for the declared rule. -/
def Rule.empty (r : Rule) : r.Data :=
  match r with
  | .initial .. => .empty
  | .lwwRegister .. => none
  | .values .. | .valuesPerKey .. | .observedSet .. | .lwwPerSigner .. | .lwwMap .. =>
      CheckpointSummary.empty

/-- Bodies retained for native rendering; discarded history is never reconstructed. -/
def Rule.live (r : Rule) : r.Data → List Act :=
  match r with
  | .initial .. => CheckpointCompact.Initial.witnesses
  | .lwwRegister .. => CheckpointCompact.LwwRegister.liveActs
  | .values .. | .valuesPerKey .. | .observedSet .. | .lwwPerSigner .. | .lwwMap .. => Row.live

/-- Concrete compact update for one supported rule under the shared coverage oracle. -/
def Rule.step (input : Input) (coverage : Nat → Bool) (r : Rule) : r.Data → Act → r.Data :=
  match r with
  | .initial v _ => fun s e => CheckpointCompact.Initial.step v s e (coverage e.addr)
  | .lwwRegister v _ c => fun s e =>
      CheckpointCompact.LwwRegister.step input.clock input.signerRank v c s e (coverage e.addr)
  | .values v _ => CheckpointSummary.step (.current v none none) coverage
  | .valuesPerKey v k _ d => CheckpointSummary.step (.current v (some k) d) coverage
  | .observedSet a r f => CheckpointSummary.step (.current a (some f) (some r)) coverage
  | .lwwPerSigner v .. => CheckpointSummary.step (.own v) coverage
  | .lwwMap v k _ _ d => CheckpointSummary.step (.current v (some k) d) coverage

/-- Independent sufficient-state invariant for this rule and ghost accepted history. -/
def Rule.Valid (input : Input) (H : List Act) (r : Rule) : r.Data → Prop :=
  match r with
  | .initial v _ => CheckpointCompact.Initial.Invariant v H
  | .lwwRegister v _ c => CheckpointCompact.LwwRegister.Invariant input.clock input.signerRank v c H
  | .values v _ => Invariant (.current v none none) H
  | .valuesPerKey v k _ d => Invariant (.current v (some k) d) H
  | .observedSet a r f => Invariant (.current a (some f) (some r)) H
  | .lwwPerSigner v .. => Invariant (.own v) H
  | .lwwMap v k _ _ d => Invariant (.current v (some k) d) H

theorem rule_empty_valid (input : Input) (r : Rule) : r.Valid input [] r.empty := by
  cases r <;> first
  | exact CheckpointCompact.Initial.empty_invariant _
  | exact CheckpointCompact.LwwRegister.empty_invariant _ _ _ _
  | exact empty_invariant _

/-- Freshness supplies compact reducers' compatibility premise without postulating
any successful update or desired rendering result. -/
theorem fresh_compatible {H : List Act} {e : Act} (fresh : covered H e.addr = false) :
    CheckpointCompact.Compatible H e := by
  intro a member address
  have yes := (covered_iff H e.addr).mpr ⟨a, member, address⟩
  simp [fresh] at yes

theorem identity_consistent {H : List Act} (unique : NodupAddr H) :
    CheckpointCompact.IdentityConsistent H := by
  intro a ha b hb same
  exact unique.eq_of_addr ha hb same

theorem rule_step_valid {input : Input} {H : List Act} {r : Rule} {s : r.Data}
    (valid : r.Valid input H s) (e : Act) (fresh : covered H e.addr = false) :
    r.Valid input (e :: H) (r.step input (covered H) s e) := by
  have coverage : CheckpointCompact.ExactCoverage H e (covered H e.addr) := covered_iff H e.addr
  have compatible := fresh_compatible fresh
  cases r <;> first
  | exact CheckpointCompact.Initial.step_preserves valid coverage compatible
  | exact CheckpointCompact.LwwRegister.step_preserves valid coverage compatible
  | exact step_preserves valid fresh

/-- Collection observations as exact semantic values, independent of key-order. -/
inductive View where
  | cell (value : Cell)
  | boolean (value : Bool)
  | integer (value : Int)
  | values (member : Val → Bool)
  | mapped (read : Val → Option Cell)
  | valuesBy (read : Val → Option (Val → Bool))
  | histogram (support : Val → Bool) (counts : Val → Nat)
  | resource (value : StateKernelExtensions.ResourceView)

/-- Project native observations into exact, order-independent semantic values. -/
def view : Observation → View
  | .cell v => .cell v
  | .boolean v => .boolean v
  | .integer v => .integer v
  | .values f => .values f
  | .map m => .mapped (fun k => if k ∈ m.keys then some (m.read k) else none)
  | .valueMap m => .valuesBy (fun k => if k ∈ m.keys then some (m.read k) else none)
  | .histogram keys f => .histogram (fun k => decide (k ∈ keys)) f
  | .resource v => .resource v

theorem view_eq {a b : Observation} (same : Equivalent a b) : view a = view b := by
  cases a <;> cases b <;> simp only [Equivalent] at same <;> try contradiction
  all_goals try (cases same; rfl)
  case map.map a b =>
    apply congrArg View.mapped
    funext k
    by_cases hk : k ∈ a.keys
    · simp [hk, (same.1 k).mp hk, same.2 k hk]
    · have hb : k ∉ b.keys := fun hb => hk ((same.1 k).mpr hb)
      simp [hk, hb]
  case valueMap.valueMap a b =>
    apply congrArg View.valuesBy
    funext k
    by_cases hk : k ∈ a.keys
    · simp [hk, (same.1 k).mp hk, same.2 k hk]
    · have hb : k ∉ b.keys := fun hb => hk ((same.1 k).mpr hb)
      simp [hk, hb]
  case histogram.histogram A a B b =>
    obtain ⟨keys, rfl⟩ := same
    apply congrArg (fun support => View.histogram support a)
    funext k
    apply Bool.eq_iff_iff.mpr
    simpa using keys k

/-- Actual native kernel evaluation over the retained row, followed by extensional rendering. -/
def Rule.render (input : Input) (r : Rule) (s : r.Data) : View :=
  view (evaluate {input with acts := r.live s} [] r.expression)

/-- Reference rule result computed directly by the existing native evaluator. -/
def Rule.fold (input : Input) (r : Rule) (H : List Act) : View :=
  view (evaluate {input with acts := H} [] r.expression)

/-- Every supported retained row renders as the native full-history expression. -/
theorem rule_render_eq {input : Input} {H : List Act} {r : Rule} {s : r.Data}
    (valid : r.Valid input H s) (unique : NodupAddr H) : r.render input s = r.fold input H := by
  apply view_eq
  cases r with
  | initial v f =>
      change project f false (sole (acts v (CheckpointCompact.Initial.witnesses s))) =
        project f false (sole (acts v H))
      exact congrArg (project f false) (CheckpointCompact.Initial.sole_acts_eq valid)
  | lwwRegister v f c =>
      change project f false (choose input.clock input.signerRank (.hlc c)
        (select (admitted [] (CheckpointCompact.LwwRegister.liveActs s)) (.verb v))) =
        project f false (choose input.clock input.signerRank (.hlc c)
        (select (admitted [] H) (.verb v)))
      simp only [CheckpointRender.admitted_empty, select]
      rw [CheckpointCompact.LwwRegister.acts_live_eq valid]
      exact congrArg (project f false)
        (CheckpointCompact.LwwRegister.choose_live_eq (identity_consistent unique) valid)
  | values v f => exact CheckpointRender.values_render input valid f
  | valuesPerKey v k f d => exact CheckpointRender.valuesPerKey_render input valid f
  | observedSet a r f => exact CheckpointRender.observedSet_render input valid
  | lwwPerSigner v f c => exact CheckpointRender.lwwPerSigner_render input valid unique f c
  | lwwMap v k f c d => exact CheckpointRender.lwwMap_render input valid unique f c

/-- A finite entry stores only the data required by its declared rule. -/
structure Entry where
  /-- The declared field name, preserved across every compact update. -/
  name : String
  /-- The fixed supported rule governing this field. -/
  rule : Rule
  /-- Only the sufficient state allowed by the declared rule. -/
  data : rule.Data

/-- Erase runtime state to recover the immutable field declaration. -/
def Entry.schema (entry : Entry) : String × Rule := (entry.name, entry.rule)

/-- Initialize one named field with the correct rule-indexed empty state. -/
def Entry.empty (field : String × Rule) : Entry :=
  ⟨field.1, field.2, field.2.empty⟩

/-- Sufficient-state invariant for one finite profile entry. -/
def Entry.Valid (input : Input) (H : List Act) (entry : Entry) : Prop :=
  entry.rule.Valid input H entry.data

/-- Maintain one entry while preserving its field name and declared rule. -/
def Entry.step (input : Input) (coverage : Nat → Bool) (entry : Entry) (e : Act) : Entry :=
  ⟨entry.name, entry.rule, entry.rule.step input coverage entry.data e⟩

/-- Render the named retained row through its native kernel expression. -/
def Entry.render (input : Input) (entry : Entry) : String × View :=
  (entry.name, entry.rule.render input entry.data)

/-- No history field: finite declared rows plus identity-only coverage storage. -/
structure Snapshot where
  /-- Shared accepted-identity membership; its executable updates capture only numbers. -/
  coverage : Nat → Bool
  /-- The finite declared rows; no ghost history is stored here. -/
  rows : List Entry

/-- The ordered finite clause implemented by the snapshot. -/
def Snapshot.schema (s : Snapshot) : List (String × Rule) := s.rows.map Entry.schema

/-- Genesis checkpoint for an arbitrary finite supported clause. -/
def Snapshot.empty (fields : List (String × Rule)) : Snapshot :=
  ⟨fun _ => false, fields.map Entry.empty⟩

/-- Maintain coverage and every declared row after one fresh accepted identity. -/
def Snapshot.step (input : Input) (s : Snapshot) (e : Act) : Snapshot :=
  if s.coverage e.addr then s else
    ⟨insertCoverage s.coverage e.addr, s.rows.map (fun row => row.step input s.coverage e)⟩

/-- Process a finite tail incrementally without consulting the discarded prefix. -/
def Snapshot.advance (input : Input) (s : Snapshot) (tail : List Act) : Snapshot :=
  tail.foldl (Snapshot.step input) s

/-- Exact coverage plus each row invariant, indexed by ghost accepted history. -/
def Snapshot.Valid (input : Input) (H : List Act) (s : Snapshot) : Prop :=
  (∀ id, s.coverage id = covered H id) ∧ ∀ row ∈ s.rows, row.Valid input H

theorem snapshot_empty_valid (input : Input) (fields : List (String × Rule)) :
    (Snapshot.empty fields).Valid input [] := by
  refine ⟨fun _ => rfl, ?_⟩
  intro row member
  obtain ⟨field, _, rfl⟩ := List.mem_map.mp member
  exact rule_empty_valid input field.2

theorem snapshot_step_valid {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid input H) (e : Act) :
    (s.step input e).Valid input (ingest H e) := by
  by_cases duplicate : covered H e.addr = true
  · simpa [Snapshot.step, valid.1, ingest, duplicate] using valid
  · have fresh : covered H e.addr = false := Bool.eq_false_iff.mpr duplicate
    simp only [Snapshot.step, valid.1, fresh, Bool.false_eq_true, ↓reduceIte,
      ingest, Snapshot.Valid]
    refine ⟨fun id => by simp [insertCoverage, valid.1], ?_⟩
    intro row member
    obtain ⟨old, oldMember, equality⟩ := List.mem_map.mp member
    subst row
    have coverage : s.coverage = covered H := funext valid.1
    simpa [Entry.step, Entry.Valid, coverage] using rule_step_valid (valid.2 old oldMember) e fresh

theorem snapshot_advance_valid {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid input H) (tail : List Act) :
    (s.advance input tail).Valid input (replay H tail) := by
  induction tail generalizing H s with
  | nil => exact valid
  | cons e rest ih => exact ih (snapshot_step_valid valid e)

theorem snapshot_step_schema (input : Input) (s : Snapshot) (e : Act) :
    (s.step input e).schema = s.schema := by
  simp only [Snapshot.step]
  split
  · rfl
  · simp [Snapshot.schema, List.map_map, Entry.step, Entry.schema]

theorem snapshot_advance_schema (input : Input) (s : Snapshot) (tail : List Act) :
    (s.advance input tail).schema = s.schema := by
  induction tail generalizing s with
  | nil => rfl
  | cons e rest ih => exact (ih _).trans (snapshot_step_schema input s e)

/-- Freeze sufficient state obtained by incrementally observing the covered prefix. -/
def Snapshot.checkpoint (input : Input) (fields : List (String × Rule)) (H : List Act) : Snapshot :=
  (Snapshot.empty fields).advance input H

theorem snapshot_checkpoint_valid (input : Input) (fields : List (String × Rule)) (H : List Act) :
    (Snapshot.checkpoint input fields H).Valid input (normalize H) :=
  snapshot_advance_valid (snapshot_empty_valid input fields) H

theorem snapshot_checkpoint_schema (input : Input) (fields : List (String × Rule)) (H : List Act) :
    (Snapshot.checkpoint input fields H).schema = fields := by
  rw [Snapshot.checkpoint, snapshot_advance_schema]
  simp [Snapshot.schema, Snapshot.empty, Entry.empty, Entry.schema, List.map_map, Function.comp_def]

/-- Exact semantic field values obtained by native evaluation of retained rows. -/
def Snapshot.render (input : Input) (s : Snapshot) : List (String × View) :=
  s.rows.map (Entry.render input)

/-- Independent baseline: native full-history evaluation after accepted-store dedup. -/
def fullFoldRaw (input : Input) (fields : List (String × Rule)) (H : List Act) : List (String × View) :=
  fields.map (fun (name, rule) => (name, rule.fold input H))

/-- Full-history baseline: accepted-store deduplication followed by native field evaluation. -/
def fullFold (input : Input) (fields : List (String × Rule)) (H : List Act) : List (String × View) :=
  fullFoldRaw input fields (normalize H)

theorem render_valid {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid input H) (unique : NodupAddr H) :
    s.render input = fullFoldRaw input s.schema H := by
  simp only [Snapshot.render, fullFoldRaw, Snapshot.schema, List.map_map]
  apply List.map_congr_left
  intro row member
  exact congrArg (fun observation => (row.name, observation))
    (rule_render_eq (valid.2 row member) unique)

/-- Imported snapshots require a truthful invariant, not merely a verified signature. -/
theorem resume_valid_snapshot {input : Input} {H : List Act} {s : Snapshot}
    (valid : s.Valid input H) (unique : NodupAddr H) (tail : List Act) :
    (s.advance input tail).render input = fullFoldRaw input s.schema (replay H tail) := by
  have result := render_valid (snapshot_advance_valid valid tail) (replay_unique unique tail)
  rw [snapshot_advance_schema] at result
  exact result

/-- Main continuation law for every finite supported clause, history and tail.
The proof derives the invariant from genesis and each concrete compact update.
There is no assumption equating advance with full folding. -/
theorem render_advance_checkpoint (input : Input) (fields : List (String × Rule))
    (history tail : List Act) :
    ((Snapshot.checkpoint input fields history).advance input tail).render input =
      fullFold input fields (history ++ tail) := by
  have result := resume_valid_snapshot (snapshot_checkpoint_valid input fields history)
    (normalize_unique history) tail
  rw [snapshot_checkpoint_schema] at result
  simpa [fullFold, normalize_append] using result

/-- Zero-tail rendering is a corollary, not the premise of continuation. -/
theorem render_checkpoint (input : Input) (fields : List (String × Rule)) (history : List Act) :
    (Snapshot.checkpoint input fields history).render input = fullFold input fields history := by
  simpa [Snapshot.advance] using render_advance_checkpoint input fields history []

/-- Duplicate identities leave the complete compact snapshot unchanged. -/
theorem snapshot_duplicate_noop (input : Input) (s : Snapshot) (e : Act)
    (duplicate : s.coverage e.addr = true) : s.step input e = s := by
  simp [Snapshot.step, duplicate]

/-- Whole-clause baseline is literally the existing native expression evaluator. -/
theorem fullFoldRaw_native (input : Input) (fields : List (String × Rule)) (H : List Act) :
    fullFoldRaw input fields H =
      (evaluateFields {input with acts := H} []
        (fields.map (fun (name, rule) => (name, rule.expression)))).map
          (fun (name, observation) => (name, view observation)) := by
  simp [fullFoldRaw, evaluateFields, Rule.fold, List.map_map]

/-- Every primitive supported field compiles in arbitrary preceding context. -/
theorem native_compile_fields (fields : List (String × Rule))
    (earlier : List (String × StateKernelClause.Rule)) :
    compileFields earlier (fields.map (fun (name, rule) => (name, rule.native))) =
      some (fields.map (fun (name, rule) => (name, rule.expression))) := by
  induction fields generalizing earlier with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨name, rule⟩ := field
      simp [compileFields, native_expression, ih]

/-- The supported declarations compile as a whole native, domain-free clause. -/
theorem native_compile_clause (input : Input) (fields : List (String × Rule))
    (uniqueNames : (fields.map Prod.fst).Nodup) :
    compileClause input ⟨fields.map (fun (name, rule) => (name, rule.native)), []⟩ =
      some ⟨[], fields.map (fun (name, rule) => (name, rule.expression))⟩ := by
  simp [compileClause, compileDomains, native_compile_fields, List.map_map,
    Function.comp_def, uniqueNames]

/-- Expanded endpoint showing the pre-existing whole-clause evaluator directly. -/
theorem render_advance_native_clause (input : Input) (fields : List (String × Rule))
    (history tail : List Act) :
    ((Snapshot.checkpoint input fields history).advance input tail).render input =
      (evaluateFields {input with acts := normalize (history ++ tail)} []
        (fields.map (fun (name, rule) => (name, rule.expression)))).map
          (fun (name, observation) => (name, view observation)) := by
  rw [render_advance_checkpoint]
  exact fullFoldRaw_native input fields (normalize (history ++ tail))

end CBCL.CheckpointKernel
