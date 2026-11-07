import Lean
import LeanCbcl.CheckpointAll

/-!
Bounded all-sixteen Rust/Lean observational bridge, NOT extraction or a native
verifier proof. Generated input contains authenticated-act projections, never
expected outputs. CheckpointAll executes real checkpoint/advance transitions and
its native-expression fullFold is compared separately by the Rust driver.

Two explicit unproved ports are restricted to the fixture grammar:
* single-verb repeat evidence maps the known opener edge to `begin` and retains
  all subsequent tick predecessor IDs; no claimed position number is supplied;
* resource classification independently checks exact cast and allocation facts
  for a bootstrap-only account counter (floor 0, ceiling 20, rights 10/0,
  headroom 5/5). No resource operations, conflicts, malformed facts, collective
  authority, quorum finalization or arbitrary native classifier are modeled.
Initial witness serialization order and raw signature representation are not
compared. Finite output universes come from input fields/identities, not outputs.
-/
namespace CheckpointAllRustOracle
open Lean CBCL CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries
open CBCL.StateKernel CBCL.CheckpointEvidence

/-- Typed recognized input; protocol/resource metadata are explicit boundary ports. -/
structure Event where
  /-- Identity and selected application fields extracted from authenticated input. -/
  act : Act
  /-- Recognized physical/logical evidence; absent clocks remain ineligible. -/
  stamp : Option (Nat × Nat)
  /-- Single-verb causal projection, without a claimed position verdict. -/
  cause : Repeat.Cause
  /-- Whether native resource projection recognized a cast-bearing root. -/
  cast : Bool := false
  /-- Ordered role bindings extracted from that actual root. -/
  bindings : List ResourceRoleBinding := []
  /-- Whether this act is the configured resource initializer. -/
  initFlag : Bool := false
  /-- Native-parsed initialization account allocations. -/
  allocations : ResourceAccounts := []
  /-- Native-parsed headroom allocations. -/
  headroom : ResourceAccounts := []

/-- The bounded account-cast fixture, extracted independently from signed input. -/
def fixtureBindings : List ResourceRoleBinding :=
  [⟨"issuer", ["@m0"]⟩, ⟨"holder", ["@m0", "@m1"]⟩]

/-- Only selected resource fields enter the retained fact projection. -/
def resourceData (events : List Event) (a : Act) : ResourceData :=
  match events.find? (fun e => e.act.addr == a.addr) with
  | none => ⟨a.signer, .other, 0, none, [], {resource := "budget"}⟩
  | some e =>
      let selected : ResourceSelected := {
        resource := "budget"
        verb := a.verb
        bindings := if e.cast then .value e.bindings else .absent
        initialAllocations := if e.initFlag then .value e.allocations else .absent
        headroomAllocations := if e.initFlag then .value e.headroom else .absent }
      ⟨a.signer, if e.cast then .castRoot else if e.initFlag then .initialize else .other,
        0, a.preds.head?, [], selected⟩


/-- Recognize the cast required by this restricted native bootstrap subset. -/
def rootFact (f : ResourceFact) : Bool :=
  f.data.kind == .castRoot && f.data.selected.bindings == .value fixtureBindings

/-- Recognize allocation input facts; this is not an expected-outcome lookup. -/
def initialFact (f : ResourceFact) : Bool :=
  f.data.kind == .initialize &&
    f.data.selected.initialAllocations == .value [("@m0", 10), ("@m1", 0)] &&
    f.data.selected.headroomAllocations == .value [("@m0", 5), ("@m1", 5)]

/-- Any-predicate queries respect exact fact-set membership. -/
theorem any_ext (predicate : ResourceFact → Bool) (xs ys : List ResourceFact)
    (same : FactSetEq xs ys) : xs.any predicate = ys.any predicate := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨f, hf, ok⟩; exact ⟨f, (same f).mp hf, ok⟩
  · rintro ⟨f, hf, ok⟩; exact ⟨f, (same f).mpr hf, ok⟩

/-- Bounded independent classifier: empty pre-opener state, then checked bootstrap.
The Rust driver emits no resource verdict into this classifier. -/
def classify (fs : List ResourceFact) : StateKernelExtensions.ResourceInput :=
  if fs.any initialFact then
    if fs.any rootFact then .ready 0 [("@m0", ⟨10, 5⟩), ("@m1", ⟨0, 5⟩)] (some 20)
    else .fault "bounded port lacks recognized cast" []
  else .pending []

/-- Resource port is fact-extensional; classifier/native-Rust correspondence is
only checked on the explicit bounded corpus, never assumed as a theorem. -/
def resourcePort (events : List Event) : ResourcePort where
  extract := resourceData events
  classify := fun fs _ => classify fs
  classify_ext := by
    intro xs ys same
    funext name
    simp only [classify, any_ext initialFact xs ys same, any_ext rootFact xs ys same]

/-- Single-verb causal metadata uses parent IDs rather than asserted ranks. -/
def ports (events : List Event) : CheckpointAll.Ports :=
  ⟨fun a => ⟨0, a.verb, (events.find? (fun e => e.act.addr == a.addr)).map Event.cause |>.getD .absent⟩,
    resourcePort events⟩

/-- Every native head appears once; derived references resolve to earlier maps. -/
def raw : List (String × StateKernelClause.Rule) :=
  [("r0", .initial "open" "title"), ("r1", .values "put" "v"),
   ("r2", .valuesPerKey "put" "k" "v" (some "del")),
   ("r3", .observedSet "put" "del" "k"),
   ("r4", .lwwMap "put" "k" "v" "clock" (some "del")),
   ("r5", .lwwRegister "put" "v" "clock"),
   ("r6", .lwwPerSigner "put" "v" "clock"),
   ("r7", .existsRule "put"), ("r8", .count "put"),
   ("r9", .counter "put" "down" "v"), ("r10", .setUnion "put" "v"),
   ("r11", .events "put" "v"), ("r12", .histogram "r4"),
   ("r13", .sum "r11"), ("r14", .progress "tick"), ("r15", .boundedCounter "budget")]

/-- Closed successfully resolved schema used by the concrete transition system. -/
def fields : List (String × CheckpointAll.Rule) := (CheckpointAll.resolveFields [] raw).getD []
example : fields.length = 16 := by decide

/-- Stable clock/signer interpretation and installed repeat bound three. -/
def input (events : List Event) (signers : List (String × Nat)) : Input :=
  ⟨[], "open", fun field a => if field == "clock" then
    (events.find? (fun e => e.act.addr == a.addr)).bind Event.stamp else none,
    fun signer => (signers.lookup signer).getD 0, fun _ => none, 0, fun _ => 3,
    fun _ => .pending []⟩

/-- Render the bounded typed scalar/list value corpus as JSON. -/
def valJson : Val → Json
  | .str s => .str s
  | .int n => toJson n
  | .bool b => .bool b
  | .list xs => toJson (xs.map fun x => match x with
      | .str s => Json.str s | .int n => toJson n | .bool b => Json.bool b)

/-- Preserve absence and event signer provenance in the serialized observation. -/
def cellJson : Cell → Json
  | .absent => .null
  | .value v => valJson v
  | .event signer value => Json.mkObj [("by", .str signer), ("value", valJson value)]

/-- Match native scalar map-key spelling in the recognized finite corpus. -/
def keyText : Val → String
  | .str s => s | .int n => toString n | .bool b => if b then "true" else "false"
  | .list _ => "outside-bounded-scalar-keys"

/-- Enumerate a predicate over input-derived values in canonical rendering order. -/
def setJson (values : List Val) (member : Val → Bool) : Json :=
  .arr (((uniqueKeys values).filter member).map valJson |>.mergeSort
    (fun a b => decide (a.compress ≤ b.compress))).toArray

/-- Retain pending/fault tags and Ready balances without converting missing evidence to rights. -/
def resourceJson : StateKernelExtensions.ResourceView → Json
  | .pending ids => Json.mkObj [("status", .str "pending"), ("evidence", toJson ids)]
  | .fault reason ids => Json.mkObj [("status", .str "fault"), ("reason", .str reason), ("evidence", toJson ids)]
  | .ready value rights headroom =>
      Json.mkObj ([("status", .str "ready"), ("value", toJson value),
        ("rights", Json.mkObj (rights.map fun (owner,n) => (owner,toJson n)))] ++
        headroom.toList.map (fun hs => ("headroom", Json.mkObj (hs.map fun (owner,n) => (owner,toJson n)))))

/-- Exact observations over an input-derived finite scalar/key/address universe. -/
def viewJson (events : List Event) (signers : List (String × Nat)) : CheckpointKernel.View → Json :=
  let values := uniqueKeys ((events.map Event.act).filterMap (fun a => a.get "v"))
  let keys := uniqueKeys (((events.map Event.act).filterMap (fun a => a.get "k")) ++
    signers.map (fun p => Val.str p.1) ++ events.map (fun e => Val.int e.act.addr))
  fun view => match view with
  | .cell c => cellJson c
  | .boolean b => .bool b
  | .integer n => toJson n
  | .values member => setJson (values ++ keys) member
  | .mapped read => Json.mkObj (keys.filterMap fun key => (read key).map (fun cell => (keyText key,cellJson cell)))
  | .valuesBy read => Json.mkObj (keys.filterMap fun key => (read key).map (fun member => (keyText key,setJson values member)))
  | .histogram support counts => Json.mkObj (values.filterMap fun v => if support v then some (keyText v,toJson (counts v)) else none)
  | .resource resource => resourceJson resource

/-- Execute concrete snapshot/checkpoint-tail and independent full-history fold.
The driver independently checks both observations against Rust for every prefix. -/
def observations (events : List Event) (signers : List (String × Nat)) (cut upto : Nat) : Json :=
  let p := ports events
  let i := input events signers
  let acts := events.map Event.act
  let snapshot := (CheckpointAll.Snapshot.checkpoint p i fields (acts.take cut)).advance p i
    ((acts.drop cut).take (upto - cut))
  let snapshotJson := Json.mkObj ((snapshot.render p i).map fun (name,v) => (name, viewJson events signers v))
  let fullJson := Json.mkObj ((CheckpointAll.fullFold p i fields (acts.take upto)).map fun (name,v) => (name,viewJson events signers v))
  Json.mkObj [("cut", toJson cut), ("prefix", toJson upto), ("snapshot", snapshotJson), ("fullFold", fullJson)]

end CheckpointAllRustOracle
