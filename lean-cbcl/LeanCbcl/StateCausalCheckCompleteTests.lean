import LeanCbcl.StateCausalCheckComplete
import LeanCbcl.StateCausalRankIntegrationTests

/-! Completeness constructs rank from an independent order witness, rather
than assuming the causal check under test already succeeds. -/
namespace CBCL.StateCausalCheckCompleteTests
open State StateCausalRank StateCausalCheckComplete

/-- Descending, reversed, duplicate delivery is accepted via the general proof. -/
theorem duplicate_delivery_complete : causalCheck StateCausalRankIntegrationTests.history = true := by
  have inside : ∀ act ∈ StateCausalRankIntegrationTests.history, act ∈ descending := by
    intro act member
    simpa [StateCausalRankIntegrationTests.history] using member
  have ranked : StateExecutableFreeze.Ranked StateCausalRankIntegrationTests.history :=
    ranked_from_order _ descending descending_check inside
  have unique : NodupAddr descending := by unfold NodupAddr descending; decide
  exact causalCheck_complete _ ranked (fun a memberA b memberB equal =>
    unique.eq_of_addr (inside a memberA) (inside b memberB) equal)

/-- Empty history needs no ready vertex and passes recognition. -/
theorem empty_complete : causalCheck [] = true := by rfl

/-- Rank recognition deliberately leaves missing-predecessor rejection to the
outer validator; this input has no edge between two present vertices. -/
theorem closure_is_separate : causalCheck [⟨7,"open","@a",[99],[],[]⟩] = true := by decide

end CBCL.StateCausalCheckCompleteTests
