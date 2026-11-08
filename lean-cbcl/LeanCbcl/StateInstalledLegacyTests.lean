import LeanCbcl.StateInstalledResource

namespace CBCL.StateInstalledLegacyTests
open State StateLift StateInstalledLegacy StateInstalledCompiler

/-- Test whether the installed legacy query policy admits the supplied alternatives. -/
def queryAccepted (shapes : List WriterShape) (rule : StateKernelClause.Rule) (elements : List Value) : Bool :=
  (queryPolicy shapes rule).any (fun policy => policy.check elements)

theorem revisable_values_member_rejected : queryAccepted [] (.values "write" "value")
    [.element (.member (.str "x"))] = false := by decide

theorem observed_set_member_rejected : queryAccepted [] (.observedSet "add" "remove" "value")
    [.element (.member (.str "x"))] = false := by decide

theorem arrival_member_accepted : queryAccepted [] (.setUnion "add" "value")
    [.element (.member (.str "x"))] = true := by decide

theorem duplicate_count_alternatives_rejected : queryAccepted [] (.count "vote")
    [.element (.count 1),.element (.count 1)] = false := by decide

theorem structured_member_rejected : queryAccepted [] (.setUnion "add" "value")
    [.element (.member (.list [.str "x"]))] = false := by decide

theorem signed_events_sum_rejected : queryAccepted [] (.events "pay" "amount")
    [.element (.sum 10)] = false := by decide

theorem optional_nonnegative_sum_rejected : queryAccepted [⟨"pay","amount",false,true⟩] (.events "pay" "amount")
    [.element (.sum 10)] = false := by decide

theorem mandatory_nonnegative_sum_accepted : queryAccepted [⟨"pay","amount",true,true⟩] (.events "pay" "amount")
    [.element (.sum 10)] = true := by decide

theorem oversized_count_rejected : queryAccepted [] (.count "vote") [.element (.count (2^63))] = false := by decide

theorem negative_event_sum_bound_accepted : queryAccepted [⟨"pay","amount",true,true⟩] (.events "pay" "amount")
    [.element (.sum (-1))] = true := by decide

/-- A real finite registry, including an empty one for a resource-free clause,
can instantiate the concrete completeness theorem. -/
theorem empty_registry_clause_compiles (context : StateKernelSEC.Context) :
    ∃ plans, StateInstalledLegacy.compile context [] (fun _ => none) []
      [("votes",StateKernelClause.Rule.count "vote"),("seen",.existsRule "vote")] [] = some plans := by
  apply concrete_installed_complete
  · repeat' constructor
  · intro fieldName resource member
    simp at member
  · decide
  · decide
  · simp

end CBCL.StateInstalledLegacyTests
