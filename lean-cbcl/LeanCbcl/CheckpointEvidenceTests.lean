import LeanCbcl.CheckpointEvidence

/-! Kernel-checked regressions. Partial evidence is not an admission certificate.
The missing-parent examples deliberately test evidence resolution itself. -/
namespace CBCL.CheckpointEvidence.Tests
open CBCL.State CBCL.Repeat CBCL.StateKernelExtensions

private def child : ProtocolFact := ⟨2, ⟨0, "tick", .previous 1⟩⟩
private def parent : ProtocolFact := ⟨1, ⟨0, "tick", .begin⟩⟩

/-- A saved scalar maximum would be wrong after the missing predecessor arrives. -/
example : StateProgress.progress (materialize [child]) 0 "tick" 4 [2] = 0 ∧
    StateProgress.progress (materialize (advance [child] [parent])) 0 "tick" 4 [2] = 2 := by
  decide

example : Repeat.resolve 5 (materialize [child]) 0 "tick" 4 2 = .unknown ∧
    Repeat.resolve 5 (materialize (advance [child] [parent])) 0 "tick" 4 2 = .position 2 := by
  decide

example : progress [child] 0 "tick" 4 = 0 ∧
    progress (advance [child] [parent]) 0 "tick" 4 = 2 := by decide

example : progress (advance [child] [⟨1, ⟨99, "tick", .begin⟩⟩]) 0 "tick" 4 = 0 := by
  decide

example : progress (advance [child] [⟨1, ⟨0, "wrong", .begin⟩⟩]) 0 "tick" 4 = 0 := by
  decide

example : step [parent] parent = [parent] := by decide

/-- Immutability/covered identity suppresses substitution; authentication must
reject a conflicting offered binding before the accepted update is invoked. -/
example : step [parent] ⟨1, ⟨9, "substitution", .absent⟩⟩ = [parent] := by decide

private def act (id : Nat) (verb : String) (preds : List Nat := []) : Act :=
  ⟨id, verb, "@a", preds, [("ignored-body", .str "not retained")], []⟩

private def causal (a : Act) : Evidence :=
  ⟨0, a.verb, match a.preds with | [] => .begin | p :: _ => .previous p⟩

example : advance (checkpoint causal [act 2 "tick" [1]])
    (project causal [act 1 "tick", act 2 "tick" [1]]) =
    project causal (CheckpointSummary.normalize
      ([act 2 "tick" [1]] ++ [act 1 "tick", act 2 "tick" [1]])) :=
  checkpoint_tail causal _ _

example : progress (advance (checkpoint causal [act 2 "tick" [1]])
    (project causal [act 1 "tick"])) 0 "tick" 4 = 2 := by decide

/-- Application fields do not enter the causal evidence record. -/
example : project causal [act 1 "tick"] =
    project causal [{act 1 "tick" with fields := [("different", .int 999)]}] := by decide

private def resourceData (a : Act) : ResourceData :=
  ⟨a.signer, if a.verb = "legacy-collective" then .checkpoint else .other,
    0, a.preds.head?, a.preds, { resource := "budget" }⟩

private def hasId (fs : List ResourceFact) (id : Nat) : Bool :=
  fs.any (fun f => f.id == id)

private theorem hasId_ext (xs ys : List ResourceFact) (same : FactSetEq xs ys) (id : Nat) :
    hasId xs id = hasId ys id := by
  apply Bool.eq_iff_iff.mpr
  simp only [hasId, List.any_eq_true]
  constructor
  · rintro ⟨f, hf, eq⟩; exact ⟨f, (same f).mp hf, eq⟩
  · rintro ⟨f, hf, eq⟩; exact ⟨f, (same f).mpr hf, eq⟩

/-- Toy verifier port for exercising transport of native pending/fault results.
It does not implement or certify a new resource protocol. -/
private def classify (fs : List ResourceFact) (_ : String) : ResourceInput :=
  if hasId fs 7 then .fault "native legacy collective unsupported" [7]
  else if hasId fs 9 then .ready 0 [] none
  else .pending [9]

private def port : ResourcePort where
  extract := resourceData
  classify := classify
  classify_ext := by
    intro xs ys same
    funext name
    simp only [classify, hasId_ext xs ys same]

example : port.observe (checkpoint port.extract []) "budget" = .pending [9] := by decide

example : port.observe (advance (checkpoint port.extract [])
    (project port.extract [act 9 "available"])) "budget" = .ready 0 [] none := by decide

/-- Object certificate endorsements cannot erase a native resource fault. -/
example : port.observe (advance (checkpoint port.extract [act 7 "legacy-collective"])
    (project port.extract [act 11 "endorse", act 12 "endorse", act 13 "endorse"])) "budget" =
    .fault "native legacy collective unsupported" [7] := by decide

example : port.observe (advance (checkpoint port.extract [act 7 "legacy-collective"])
    (project port.extract [act 9 "available"])) "budget" =
    resourceObserve (port.resourceInput (CheckpointSummary.normalize
      ([act 7 "legacy-collective"] ++ [act 9 "available"])) "budget") :=
  resource_checkpoint_tail port _ _ _

example : port.observe (project port.extract [act 9 "available", act 7 "legacy-collective"])
    "budget" = port.observe (project port.extract [act 7 "legacy-collective", act 9 "available"])
    "budget" := by
  apply resource_observe_setEq
  apply project_setEq
  intro a
  simp [or_comm]

/-- The richer native footprint does not collapse distinct casts or allocations
to the same owner/floor/amount scalar projection. No Act body is retained. -/
private def nativeFields : ResourceSelected := {
  resource := "budget", verb := "open", predecessors := [0],
  language := some "resource", thread := some 0,
  authenticatedFrom := .value "@a", bindings := .value [⟨"issuer", ["@a", "@b"]⟩],
  initialAllocations := .value [("@a", 10), ("@b", 0)],
  headroomAllocations := .value [("@a", 5), ("@b", 5)],
  identity := 123, castIdentity := some 456 }

example : nativeFields ≠ {nativeFields with initialAllocations := .value [("@a", 9), ("@b", 1)]} := by
  decide

example : nativeFields ≠ {nativeFields with bindings := .value [⟨"member", ["@a", "@b"]⟩]} := by
  decide

example : (ResourceField.absent : ResourceField ResourceAccounts) ≠ .value [] ∧
    (ResourceField.malformed .wrongType : ResourceField ResourceAccounts) ≠ .absent := by decide

private def counterConfig : ResourceConfig := {
  ownership := .account, certification := .legacy, floor := 0, ceiling := some 20,
  initialVerb := "open", initialKey := "rights", headroomKey := some "room",
  issuerRole := "issuer", increment := ⟨"inc", "amount", none⟩,
  decrement := ⟨"dec", "amount", none⟩, transfer := some ⟨"give", "amount", some "to"⟩,
  transferHeadroom := some ⟨"give-room", "amount", some "to"⟩ }

private def configuredClassify (config : ResourceConfig) (fs : List ResourceFact) : ResourceInput :=
  if config.ownership = .collective then
    .fault "collective counter requires the certificate runtime" []
  else match config.certification with
  | .quorum _ => .fault "quorum-budget requires an explicit certificate runtime; legacy fold cannot prove finality" []
  | .legacy => classify fs "budget"

private def nativePort (config : ResourceConfig) : ResourcePort :=
  ResourcePort.fromClassifier (fun _ => config) resourceData configuredClassify (by
    intro config xs ys same
    unfold configuredClassify
    split
    · rfl
    · cases config.certification with
      | quorum _ => rfl
      | legacy => exact congrFun (port.classify_ext xs ys same) "budget")

/-- Object endorsements never override the actual native configuration mode. -/
example : (nativePort {counterConfig with ownership := .collective}).observe
    (project resourceData [act 9 "available", act 11 "endorse", act 12 "endorse", act 13 "endorse"])
    "budget" = .fault "collective counter requires the certificate runtime" [] := by decide

example : (nativePort {counterConfig with certification := .quorum 3}).observe
    (project resourceData [act 9 "available", act 11 "endorse", act 12 "endorse", act 13 "endorse"])
    "budget" = .fault "quorum-budget requires an explicit certificate runtime; legacy fold cannot prove finality" [] := by decide

#print axioms project_ingest
#print axioms project_replay
#print axioms checkpoint_tail
#print axioms materialize_checkpoint_tail
#print axioms resolve_checkpoint_tail
#print axioms progress_checkpoint_tail
#print axioms progress_checkpoint_tail_native
#print axioms resource_checkpoint_tail
#print axioms resourceInput_checkpoint_tail
#print axioms resource_checkpoint_tail_native
#print axioms resourceInput_setEq

end CBCL.CheckpointEvidence.Tests
