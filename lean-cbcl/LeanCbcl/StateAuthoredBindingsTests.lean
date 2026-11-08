import LeanCbcl.StateAuthoredBindings

/-! Concrete whole-clause binding regressions. The immutable causal/clock
context remains an arbitrary typed input; no source display or read policy is
provided by the fixture. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredBindingsTests
open State StateLift StateLVar StateObservation StateAuthoredBindings

/-- Recognized installed metadata for a review dialect. -/
def environment (context : StateKernelSEC.Context) : Environment := {
  context := context
  profile := {
    definition := ⟨"review","dialect-address","body-address",some "@author",
      [⟨"chair",false⟩,⟨"reviewer",true⟩],⟨64,64,1000000,4096⟩,some "open"⟩
    metadata := fun _ => ⟨some "thread",.absent,.absent⟩
    address := fun _ => "act" }
  schema := ⟨["open","vote","close","mark"],
    [(("open","targets"),.list),(("vote","target"),.string),(("mark","phase"),.string)]⟩
  shapes := []
  resources := []
  fromRoles := [("close","chair")] }

/-- A threshold and a separately frozen source retain distinct read guarantees. -/
def review : List Entry := [
  .field "reviewers" (.context ["thread","roles","reviewer"]),
  .field "votes" (.legacy (.count "vote")),
  .threshold "enough" "votes" [.element (.count 3)],
  .field "sealed" (.legacy (.count "vote")),
  .freeze "sealed" "close" false]

theorem rendered_bound_counts_thresholds (context : StateKernelSEC.Context) :
    metadataCheck {environment context with profile := { (environment context).profile with
      definition := { (environment context).profile.definition with bounds := ⟨3,64,1000000,4096⟩ } }} review = false := by rfl

theorem lattice_and_field_namespace_shared (context : StateKernelSEC.Context) :
    metadataCheck (environment context) [.field "phase" (.legacy (.count "mark")),
      .lattice ⟨"phase",["zero","top"],"zero","top",[]⟩] = false := by rfl

theorem unicode_field_name_rejected : nameCheck "éligible" = false := by rfl

theorem upper_case_field_name_rejected : nameCheck "Eligible" = false := by rfl

/-- Domain source lookup uses the whole clause, rather than only earlier fields. -/
theorem domain_can_reference_later_initializer (context : StateKernelSEC.Context) :
    (domains (environment context) [.domain ⟨"vote","target","allowed"⟩,
      .field "allowed" (.legacy (.initial "open" "targets"))]).isSome = true := by rfl

theorem domain_unknown_role_rejected (context : StateKernelSEC.Context) :
    domains (environment context) [.domain ⟨"vote","target","reviewers"⟩,
      .field "reviewers" (.context ["thread","roles","stranger"])] = none := by rfl

/-- A role-bearing full-clause freeze can target a field declared before it. -/
theorem review_prepares (context : StateKernelSEC.Context) (A : List Act) :
    (prepare (environment context) review A).isSome = true := by rfl

/-- The concrete mixed context/count/threshold/freeze example compiles. -/
theorem review_compiles (context : StateKernelSEC.Context) (A : List Act) :
    (compile (environment context) review A).isSome = true := by rfl

/-- A full context freeze retains domain-excluded accepted acts as contributors. -/
theorem whole_context_contributor (context : StateKernelSEC.Context) (domains : List StateInstalledDomains.Domain)
    (A : List Act) (act : Act) (member : act ∈ A) :
    contributes domains A (contextFootprint (environment context) []) act := by
  simp only [contextFootprint,List.isEmpty_nil,Bool.true_or,ite_true,contributes]
  exact List.mem_map.mpr ⟨act,member,rfl⟩

theorem role_projection_has_no_write_contributors (context : StateKernelSEC.Context)
    (domains : List StateInstalledDomains.Domain) (A : List Act) (act : Act) :
    ¬contributes domains A (contextFootprint (environment context) ["thread","roles","reviewer"]) act := by
  simp [contextFootprint,contributes,StateInstalledDomains.support]

/-- Domain filters cannot erase a raw progress contributor from freeze evidence. -/
theorem progress_raw_contributor (context : StateKernelSEC.Context) (domains : List StateInstalledDomains.Domain)
    (A : List Act) (act : Act) (member : act ∈ A) (verb : act.verb = "tick") :
    contributes domains A (legacyFootprint (environment context) [] (.progress "tick")) act := by
  exact ⟨act,member,by simp [verb],rfl⟩

theorem forward_threshold_rejected (context : StateKernelSEC.Context) :
    (compile (environment context)
      [.threshold "enough" "votes" [.element (.count 1)],.field "votes" (.legacy (.count "vote"))] []).isNone = true := by rfl

theorem supersede_threshold_source_rejected (context : StateKernelSEC.Context) :
    (compile (environment context)
      [.field "votes" (.legacy (.count "vote")),.threshold "enough" "votes" [.element (.count 1)],
       .freeze "votes" "close" false] []).isNone = true := by rfl

theorem threshold_output_cannot_be_frozen (context : StateKernelSEC.Context) :
    (prepare (environment context)
      [.field "votes" (.legacy (.count "vote")),.threshold "enough" "votes" [.element (.count 1)],
       .freeze "enough" "close" false] []).isNone = true := by rfl

/-- Resource domain rejection precedes source evaluation, matching native installation. -/
theorem resource_operation_domain_rejected (context : StateKernelSEC.Context) (resource : Resource) :
    domains {environment context with resources := [("coins",resource)]}
      [.field "coins" (.legacy (.boundedCounter "coins")),
       .domain ⟨resource.profile.config.increment.verb,"target","allowed"⟩] = none := by
  simp [domains,rawFields,resourceVerbs,StateResourcePreflight.operationNames]

theorem freeze_without_sender_role_rejected (context : StateKernelSEC.Context) :
    (prepare {environment context with fromRoles := [("close","")]}
      [.field "votes" (.legacy (.count "vote")),.freeze "votes" "close" true] []).isNone = true := by rfl

/-- Specialization uses the full observation, not an empty history or a nested cut. -/
theorem materialized_progress_contributor
    (domains : List StateInstalledDomains.Domain) (A : List Act) (act : Act)
    (member : act ∈ A) (verb : act.verb = "tick") :
    ∃ spec, (materialize domains A [⟨"stage","close",.rawVerbs ["tick"],true⟩]).lookup "stage" = some spec ∧
      spec.contributes act := by
  exact ⟨⟨"close",contributes domains A (.rawVerbs ["tick"]),true⟩,rfl,
    ⟨act,member,by simp [verb],rfl⟩⟩

/-- Forward references reject during complete preparation, before plan construction. -/
theorem forward_threshold_preparation_rejected (context : StateKernelSEC.Context) :
    (prepareStatic (environment context)
      [.threshold "enough" "votes" [.element (.count 1)],.field "votes" (.legacy (.count "vote"))]).isNone = true := by rfl

/-- Revisable supersede sources cannot install a stable threshold policy. -/
theorem supersede_threshold_preparation_rejected (context : StateKernelSEC.Context) :
    (prepareStatic (environment context)
      [.field "votes" (.legacy (.count "vote")),.threshold "enough" "votes" [.element (.count 1)],
       .freeze "votes" "close" false]).isNone = true := by rfl

/-- Empty alternatives reject during source-relative policy admission. -/
theorem empty_threshold_preparation_rejected (context : StateKernelSEC.Context) :
    (prepareStatic (environment context)
      [.field "votes" (.legacy (.count "vote")),.threshold "enough" "votes" []]).isNone = true := by rfl

end CBCL.StateAuthoredBindingsTests
