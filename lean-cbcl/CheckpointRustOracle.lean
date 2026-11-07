import Lean
import LeanCbcl.CheckpointSummary
import LeanCbcl.CheckpointCompact
import LeanCbcl.CheckpointKernel

/-!
Bounded Rust/Lean observational correspondence runner, not an extraction proof.
Run from lean-cbcl: lake env lean --run CheckpointRustOracle.lean CORPUS.json
The Rust side authenticates actual signed messages and emits order-preserving
address and signer ranks, recognized HLC pairs, and Summary.apply observations.
This side executes the full CheckpointKernel Snapshot and its native fullFold
baseline; Snapshot dispatches to the proved Row and Compact transitions.
Only string payload/key values occur in this deliberately finite corpus. Initial
witness identities are not compared: the proof model permits any two witnesses,
while Rust canonically retains the two least addresses. Self-replacement has a
separate model-only executable check: native content IDs commit their references.
No claim about parsing, cryptography, native admission or extraction is proved.
-/
open Lean CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries CBCL.StateKernel
open CBCL.CheckpointSummary
namespace CheckpointRustOracle

abbrev Check := Except String


def field (j : Json) (k : String) : Check Json := j.getObjVal? k
def nat (j : Json) : Check Nat := j.getNat?
def str (j : Json) : Check String := j.getStr?
def array (j : Json) : Check (List Json) := j.getArr?.map Array.toList

def pair (j : Json) : Check (Json × Json) := do
  match ← array j with
  | [a,b] => return (a,b)
  | _ => throw "expected pair"

structure Event where
  act : Act
  stamp : Nat × Nat

def event (j : Json) : Check Event := do
  let addr ← nat (← field j "addr")
  let verb ← str (← field j "verb")
  let signer ← str (← field j "signer")
  let fields ← (← array (← field j "fields")).mapM fun p => do
    let (k,v) ← pair p
    return (← str k, Val.str (← str v))
  let refs ← (← array (← field j "replaces")).mapM nat
  let (physical,logical) ← pair (← field j "clock")
  return ⟨⟨addr,verb,signer,[],fields,refs⟩, (← nat physical, ← nat logical)⟩

def profile : List (String × CBCL.CheckpointKernel.Rule) :=
  [("r0", .initial "init" "v"), ("r1", .values "put" "v"),
   ("r2", .valuesPerKey "put" "k" "v" (some "del")),
   ("r3", .observedSet "put" "del" "k"),
   ("r4", .lwwMap "put" "k" "v" "clock" (some "del")),
   ("r5", .lwwRegister "put" "v" "clock"),
   ("r6", .lwwPerSigner "put" "v" "clock")]

def jnat (n : Nat) : Json := toJson n
def jlist (xs : List Json) : Json := .arr xs.toArray

def valJson : Val → Json
  | .str s => .str s
  | .int n => toJson n
  | .bool b => .bool b
  | .list _ => .null -- outside the recognized finite corpus

def cellJson : Cell → Json
  | .absent => .null
  | .value v => valJson v
  | .event _ v => valJson v

def keyString : Val → String
  | .str s => s
  | _ => "<outside-corpus>"

def sorted (xs : List Json) : Json :=
  jlist (xs.mergeSort (fun a b => decide (a.compress ≤ b.compress)))

def setJson (domainValues : List Val) (member : Val → Bool) : Json :=
  sorted ((domainValues.filter member).map valJson)

def viewJson (values keys signers : List Val) : CBCL.CheckpointKernel.View → Json
  | .cell c => cellJson c
  | .values member => setJson (uniqueKeys (values ++ keys)) member
  | .mapped read => Json.mkObj ((uniqueKeys (keys ++ signers)).filterMap fun k =>
      (read k).map (fun c => (keyString k, cellJson c)))
  | .valuesBy read => Json.mkObj (keys.filterMap fun k =>
      (read k).map (fun member => (keyString k, setJson values member)))
  | _ => .null -- the recognized seven-rule profile cannot produce other views

def pending (r : CBCL.CheckpointKernel.Rule) : r.Data → List (Scope × Nat) :=
  match r with
  | .initial .. => fun _ => []
  | .lwwRegister .. => fun _ => []
  | .values .. | .valuesPerKey .. | .observedSet .. | .lwwMap .. | .lwwPerSigner .. => Row.pending

def observation (input : Input) (values keys signers : List Val)
    (s : CBCL.CheckpointKernel.Snapshot) : Json :=
  jlist ((s.rows.zip (s.render input)).map fun (row, (_, rendered)) =>
    let acts := row.rule.live row.data
    let initial := match row.rule with | .initial .. => true | _ => false
    let ids := acts.map Act.addr |>.mergeSort (fun a b => decide (a ≤ b))
    let pendingJson := (pending row.rule row.data).map fun (scope,id) =>
      jlist [scope.map valJson |>.getD .null, jnat id]
    Json.mkObj [
      ("live", if initial then .null else jlist (ids.map jnat)),
      ("witnesses", jnat (if initial then acts.length else 0)),
      ("pending", sorted pendingJson),
      ("value", viewJson values keys signers rendered)])

def verifyCase (j : Json) : Check Nat := do
  let name ← str (← field j "name")
  let events ← (← array (← field j "acts")).mapM event
  let addresses ← (← array (← field j "addresses")).mapM fun p => do
    let (id,n) ← pair p; return (← str id, ← nat n)
  let signers ← (← array (← field j "signers")).mapM fun p => do
    let (id,n) ← pair p; return (← str id, ← nat n)
  unless addresses.map Prod.fst == (addresses.map Prod.fst).mergeSort (fun a b => decide (a ≤ b)) do
    throw "address ranks not ordered"
  unless addresses.map Prod.snd == (List.range addresses.length).map (· + 1) do
    throw "address ranks not consecutive"
  unless signers.map Prod.fst == (signers.map Prod.fst).mergeSort (fun a b => decide (a ≤ b)) do
    throw "signer ranks not byte ordered (ASCII corpus)"
  unless signers.map Prod.snd == List.range signers.length do
    throw "signer ranks not consecutive"
  for e in events do
    unless (addresses.map Prod.snd).contains e.act.addr &&
        e.act.replaces.all (fun id => (addresses.map Prod.snd).contains id) do
      throw "act/reference rank outside address table"
    unless (signers.lookup e.act.signer).isSome do throw "signer outside rank table"
    unless e.stamp.1 < 2^64 && e.stamp.2 < 2^32 do throw "HLC out of native bounds"
    for other in events do
      if other.act.addr == e.act.addr then
        unless other.act == e.act && other.stamp == e.stamp do
          throw "inconsistent duplicate identity"
  let clock : Clock := fun field a =>
    if field == "clock" then (events.find? (fun e => e.act.addr == a.addr)).map Event.stamp else none
  let rank : SignerRank := fun s => (signers.lookup s).getD 0
  let acts := events.map Event.act
  let values := uniqueKeys (acts.filterMap (fun a => a.get "v"))
  let keys := uniqueKeys (acts.filterMap (fun a => a.get "k"))
  let signerValues := signers.map (fun p => Val.str p.1)
  let input : Input := ⟨[], "init", clock, rank, fun _ => none, 0, fun _ => 0, fun _ => .pending []⟩
  let expected ← array (← field j "expected")
  unless expected.length == acts.length + 1 do throw "expected prefix count"
  let cuts ← (← array (← field j "cuts")).mapM nat
  let mut checked := 0
  for cut in cuts do
    unless cut ≤ acts.length do throw "cut beyond corpus"
    -- Real model checkpoint plus tail, including checkpoints with pending refs.
    let mut s := CBCL.CheckpointKernel.Snapshot.checkpoint input profile (acts.take cut)
    for offset in List.range (acts.length - cut + 1) do
      let got := observation input values keys signerValues s
      let wanted := expected[cut + offset]!
      unless got == wanted do
        throw s!"{name}: cut {cut}, prefix {cut+offset}\nLean: {got.compress}\nRust: {wanted.compress}"
      let baseline := jlist ((CBCL.CheckpointKernel.fullFold input profile (acts.take (cut + offset))).map
        (fun (_, v) => viewJson values keys signerValues v))
      let wantedValues ← (← array wanted).mapM (fun row => field row "value")
      unless baseline == jlist wantedValues do throw s!"{name}: native Lean fullFold mismatch at {cut+offset}"
      checked := checked + 7
      if let some a := acts[cut + offset]? then s := s.advance input [a]
  return checked

/-- Synthetic self-reference is exercised only in the abstract Row model. -/
def selfReplacementCheck : Bool := Id.run do
  let a : Act := ⟨1,"put","@m0",[],[("k",.str "x"),("v",.str "red")],[1]⟩
  let s := RowState.checkpoint (.current "put" (some "k") (some "del")) [a,a]
  return s.row.live.isEmpty && s.row.pending.isEmpty && s.coverage 1

def verify (j : Json) : Check Nat := do
  unless (← nat (← field j "version")) == 1 do throw "unsupported corpus"
  unless selfReplacementCheck do throw "model-only self replacement failed"
  let cases ← array (← field j "cases")
  unless !cases.isEmpty do throw "empty corpus"
  let counts ← cases.mapM verifyCase
  return counts.foldl (· + ·) 0

end CheckpointRustOracle

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match Json.parse text >>= CheckpointRustOracle.verify with
    | .ok n => IO.println s!"Rust/Lean parity: {n} rule-prefix-cut observations matched; 7-rule full Snapshot + native fullFold; model-only self replacement passed"; return 0
    | .error e => IO.eprintln e; return 1
  | _ => IO.eprintln "usage: lake env lean --run CheckpointRustOracle.lean CORPUS.json"; return 1
