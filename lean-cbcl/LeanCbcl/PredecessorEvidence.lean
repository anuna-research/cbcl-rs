import LeanCbcl.ConcreteProjection
import LeanCbcl.R5

/-!
# Minimal evidence for one resolved predecessor

The verifier knows the query. The observation is fixed before query selection.
Authentication, thread resolution, and other admission gates are premises.
The observable result here is the yes/no predecessor-type decision.
-/

namespace LeanCbcl.PredecessorEvidence

variable {Pred Query Evidence : Type}

/-- A single decoder answers every required query using only the observation. -/
def Sufficient (test : Query → Pred → Bool) (observe : Pred → Evidence) : Prop :=
  ∃ run : Query → Evidence → Bool, ∀ q p, run q (observe p) = test q p

/-- The function assigning this predecessor's correct answer to every query. -/
def answers (test : Query → Pred → Bool) (p : Pred) : Query → Bool :=
  fun q => test q p

theorem answers_sufficient (test : Query → Pred → Bool) :
    Sufficient test (answers test) :=
  ⟨fun q profile => profile q, fun _ _ => rfl⟩

/-- Every sufficient observation can produce the complete answer profile.
    The conversion uses the given decoder; it need not enumerate the queries. -/
theorem sufficient_iff_recovers_answers (test : Query → Pred → Bool)
    (observe : Pred → Evidence) :
    Sufficient test observe ↔
      ∃ recover : Evidence → Query → Bool, ∀ p, recover (observe p) = answers test p := by
  constructor
  · rintro ⟨run, correct⟩
    exact ⟨fun e q => run q e, fun p => funext (fun q => correct q p)⟩
  · rintro ⟨recover, correct⟩
    exact ⟨fun q e => recover e q, fun q p => congrFun (correct p) q⟩

/-- Merging two attainable answer profiles with different verdicts loses sufficiency. -/
theorem collision_loses_sufficiency (test : Query → Pred → Bool)
    (observe : Pred → Evidence) {left right : Pred} (same : observe left = observe right)
    (different : answers test left ≠ answers test right) : ¬ Sufficient test observe := by
  intro sufficient
  obtain ⟨recover, correct⟩ := (sufficient_iff_recovers_answers test observe).mp sufficient
  exact different ((correct left).symm.trans ((congrArg recover same).trans (correct right)))

/-- The exact type supports every computable predecessor-type test in this model. -/
theorem type_sufficient (test : Query → Pred → Bool) : Sufficient test id :=
  ⟨test, fun _ _ => rfl⟩

/-- The query family may consist only of permitted (dialect, step) pairs.
    The premise says that each individual name can be tested in that family. -/
theorem separates_names [DecidableEq Pred] (test : Query → Pred → Bool)
    (singleton : ∀ p, ∃ q, ∀ x, test q x = decide (x = p))
    (observe : Pred → Evidence) (sufficient : Sufficient test observe) :
    ∀ ⦃x y⦄, observe x = observe y → x = y := by
  obtain ⟨run, correct⟩ := sufficient
  intro x y same
  obtain ⟨q, accepts⟩ := singleton x
  have equal : test q x = test q y :=
    (correct q x).symm.trans ((congrArg (run q) same).trans (correct q y))
  rw [accepts x, accepts y] at equal
  simpa [eq_comm] using equal

open LeanCbcl.ConcreteProjection (NodeRef)

/-- Single-message lookup for a named clause or a disjunction, with the
    predecessor present. Fan-in clauses have a separate runtime path. -/
def singleOrAny (names : List String) (actual : String) : Bool :=
  names.contains actual

theorem singleton_matches_cbcl (wanted actual : String) :
    singleOrAny [wanted] actual = true ↔
      (NodeRef.single wanted).holds (fun n => n = actual) := by
  simp [singleOrAny, NodeRef.holds, eq_comm]

theorem alternatives_match_cbcl (names : List String) (actual : String) :
    singleOrAny names actual = true ↔
      (NodeRef.any names).holds (fun n => n = actual) := by
  simp [singleOrAny, NodeRef.holds]

/-- In the unrestricted clause language, all singleton lists are witnesses. -/
theorem sufficient_clause_evidence_separates_names (observe : String → Evidence)
    (sufficient : Sufficient singleOrAny observe) :
    ∀ ⦃x y⦄, observe x = observe y → x = y := by
  apply separates_names singleOrAny _ observe sufficient
  intro p
  exact ⟨[p], fun x => by simp [singleOrAny, eq_comm]⟩

/-- For a finite vocabulary, run the verifier on each singleton until it accepts. -/
def recoverName (vocabulary : List String) (run : List String → Evidence → Bool)
    (e : Evidence) : Option String :=
  vocabulary.find? (fun name => run [name] e)

theorem recoverName_correct (observe : String → Evidence)
    (run : List String → Evidence → Bool)
    (correct : ∀ name actual, run [name] (observe actual) = singleOrAny [name] actual)
    (vocabulary : List String) (actual : String) (present : actual ∈ vocabulary) :
    recoverName vocabulary run (observe actual) = some actual := by
  induction vocabulary with
  | nil => cases present
  | cons candidate rest ih =>
    by_cases same : actual = candidate
    · subst candidate
      simp [recoverName, correct, singleOrAny]
    · have later := (List.mem_cons.mp present).resolve_left same
      simpa [recoverName, List.find?_cons, correct, singleOrAny, same, Ne.symm same]
        using ih later

/-- A known clause has a smaller sufficient observation: its one Boolean answer.
    This statement assumes the answer is verifiably available to the receiver. -/
theorem fixed_clause_sufficient (names : List String) :
    Sufficient (fun (_ : Unit) => singleOrAny names) (singleOrAny names) :=
  ⟨fun _ result => result, fun _ _ => rfl⟩

/-- The evidence sufficient for the permissive shipping rule loses a decision
    once the strict rule is also available. -/
theorem shipping_counterexample :
    ¬ Sufficient singleOrAny (singleOrAny ["approve", "waive"]) := by
  apply collision_loses_sufficiency singleOrAny _ (left := "approve") (right := "waive") rfl
  intro same
  have impossible := congrFun same ["approve"]
  exact Bool.noConfusion impossible

section CheckedGraphs

open CBCL (ProtocolGraph StepDecl dfsNoCycle dfsReaches graphNeighbors)

/-- The four protocol-graph checks in CBCL's Lean R5 model. -/
def PassesR5 (graph : ProtocolGraph) (declared : List String) : Prop :=
  graph.checkAcyclicity = [] ∧ graph.checkReachability = [] ∧
  graph.checkStepUniqueness = [] ∧ graph.checkPerformativeDefinedness declared = []

/-- Each edge here is a separate, single-name edge. A query designates one
    declared step in a checked graph. All comparisons use the same query in
    both histories, so the known graph cannot distinguish them by itself. -/
structure CheckedStep where
  /-- The causal protocol whose step is queried. -/
  graph : ProtocolGraph
  /-- Performative names available when checking the protocol. -/
  declared : List String
  checked : PassesR5 graph declared
  /-- The step whose predecessor clause is being evaluated. -/
  step : StepDecl
  member : step ∈ graph.steps

private def chain (first second target : String) : ProtocolGraph :=
  ⟨[⟨"begin", [], [first]⟩, ⟨first, ["begin"], [second]⟩,
    ⟨second, [first], [target]⟩, ⟨target, [second], []⟩]⟩

/-- The chain begin → a → b → t passes all four checks for arbitrary fresh names. -/
private theorem chain_checked (a b t : String)
    (ha : a ≠ "begin") (hb : b ≠ "begin") (ht : t ≠ "begin")
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    PassesR5 (chain a b t) [a, b, t] := by
  have := Ne.symm ha
  have := Ne.symm hb
  have := Ne.symm ht
  have := Ne.symm hab
  have := Ne.symm hat
  have := Ne.symm hbt
  simp [PassesR5, chain, ProtocolGraph.checkAcyclicity, ProtocolGraph.checkReachability,
    ProtocolGraph.checkStepUniqueness, ProtocolGraph.checkPerformativeDefinedness,
    ProtocolGraph.stepNames, ProtocolGraph.successorGraph, ProtocolGraph.referencedPerformatives,
    List.find?_cons, graphNeighbors, dfsNoCycle, dfsReaches, Bool.beq_eq_decide_eq, *]

/-- A performative name distinct from the reserved protocol root. -/
abbrev NonBeginName := {s : String // s ≠ "begin"}

/-- Whether the selected step permits the resolved predecessor type. -/
def checkedTest (q : CheckedStep) (actual : NonBeginName) : Bool :=
  singleOrAny q.step.predecessors actual.val

/-- Correctness is required only for predecessor names present in the queried
    graph. The decoder is free to behave arbitrarily on out-of-dialect inputs. -/
def SufficientForCheckedSteps (observe : NonBeginName → Evidence) : Prop :=
  ∃ run : CheckedStep → Evidence → Bool, ∀ q p, p.val ∈ q.graph.stepNames →
    run q (observe p) = checkedTest q p

/-- Both candidates are declared and reachable in the same witness graph.
    Its last step accepts a citation of one and rejects a citation of the other. -/
theorem checked_separator (x y : NonBeginName) (different : x ≠ y) :
    ∃ q : CheckedStep, x.val ∈ q.graph.stepNames ∧ y.val ∈ q.graph.stepNames ∧
      checkedTest q x = true ∧ checkedTest q y = false := by
  have distinct : y.val ≠ x.val := fun h => different (Subtype.ext h.symm)
  let t := x.val ++ y.val ++ "-probe"
  have fresh : t ≠ "begin" ∧ y.val ≠ t ∧ x.val ≠ t := by
    have suffixLength : "-probe".length = 6 := by decide
    have beginLength : "begin".length = 5 := by decide
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have lengthEq := congrArg String.length h <;>
      simp only [t, String.length_append, suffixLength, beginLength] at lengthEq <;> omega
  let graph := chain y.val x.val t
  let q : CheckedStep :=
    ⟨graph, [y.val, x.val, t],
      chain_checked _ _ _ y.property x.property fresh.1 distinct fresh.2.1 fresh.2.2,
      ⟨t, [x.val], []⟩, by simp [graph, chain]⟩
  exact ⟨q, by simp [q, graph, chain, ProtocolGraph.stepNames],
    by simp [q, graph, chain, ProtocolGraph.stepNames], by simp [checkedTest, q, singleOrAny],
    by simp [checkedTest, q, singleOrAny, distinct]⟩

/-- Even this checked fragment forces any reusable evidence to separate names. -/
theorem checked_evidence_separates_names (observe : NonBeginName → Evidence)
    (sufficient : SufficientForCheckedSteps observe) :
    ∀ ⦃x y⦄, observe x = observe y → x = y := by
  intro x y same
  apply Decidable.byContradiction
  intro different
  obtain ⟨q, xPresent, yPresent, accepts, rejects⟩ := checked_separator x y different
  obtain ⟨run, correct⟩ := sufficient
  have equal := (correct q x xPresent).symm.trans
    ((congrArg (run q) same).trans (correct q y yPresent))
  simp [accepts, rejects] at equal

/-- Exact type information is sufficient; every observation that merges two
    types fails. The ordering here is coarsening observations of the name. -/
theorem checked_type_minimal :
    SufficientForCheckedSteps id ∧
      ∀ (observe : NonBeginName → Evidence) (x y : NonBeginName),
        x ≠ y → observe x = observe y → ¬ SufficientForCheckedSteps observe := by
  constructor
  · exact ⟨checkedTest, fun _ _ _ => rfl⟩
  · intro observe x y different same sufficient
    exact different (checked_evidence_separates_names observe sufficient same)

end CheckedGraphs

end LeanCbcl.PredecessorEvidence
