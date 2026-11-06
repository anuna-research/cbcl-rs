import LeanCbcl.StateKernelSEC

/-! SPEC-037 eventual acceptance from receive/pending execution and weak fairness. -/
namespace CBCL.StateKernelDelivery
open CBCL.State CBCL.AdmissionStratification CBCL.StateRefinement
open CBCL.StateKernel CBCL.StateKernelClause CBCL.StateKernelSEC

/-- A valid possibly infinite history with finite well-founded funding/causal dependencies.
The contract is on protocol admission, not derived from state arithmetic. -/
structure ValidHistory (adm : Admission) where
  /-- Common intended valid history, possibly infinite. -/
  contains : Act → Prop
  /-- Finite prerequisite evidence for one act. -/
  dependencies : Act → List Act
  /-- Natural rank excludes dependency cycles and infinite backwards chains. -/
  rank : Act → Nat
  /-- Prerequisites belong to the same intended history. -/
  closed : ∀ a, contains a → ∀ b ∈ dependencies a, contains b
  /-- Every prerequisite has strictly smaller rank. -/
  lower : ∀ a, contains a → ∀ b ∈ dependencies a, rank b < rank a
  /-- A valid act is never rejected while waiting for dependencies. -/
  no_reject : ∀ A, (∀ b ∈ A, contains b) → ∀ a, contains a → adm.admit A a ≠ .rejected
  /-- Admission is enabled in every history containing its prerequisite evidence. -/
  enabled : ∀ A, (∀ b ∈ A, contains b) → ∀ a, contains a →
    (∀ b ∈ dependencies a, b ∈ A) → adm.admit A a = .accepted

/-- A real execution with eventual receipt and acceptance-transition weak fairness. -/
structure Replica (adm : Admission) (auth : Act → Prop) (H : ValidHistory adm) where
  /-- Execution states. -/
  run : Nat → Execution
  /-- Actual acceptance labels from the existing transition relation. -/
  events : Nat → Option Act
  /-- Every transition is receive, duplicate, accept, reject, wait or idle. -/
  behavior : Behavior adm auth run events
  /-- No extraneous receipts in this common-history profile. -/
  valid_receipts : ∀ n a, a ∈ (run n).received → H.contains a
  /-- Every valid act is eventually received. -/
  delivery : ∀ a, H.contains a → ∃ n, a ∈ (run n).received
  /-- Continuously enabled pending work is eventually scheduled on every suffix. -/
  fair : ∀ a t, (∀ n, t ≤ n → a ∈ (run n).pending ∧ adm.admit (run n).accepted a = .accepted) →
    ∃ n, t ≤ n ∧ events n = some a

/-- Receipt persists across every execution step. -/
theorem step_received {adm : Admission} {auth : Act → Prop} {s t : Execution}
    {event : Option Act} (step : Step adm auth s event t) {a : Act}
    (member : a ∈ s.received) : a ∈ t.received := by
  cases step <;> simp_all

/-- Accepted acts are never retracted, including duplicate insertion. -/
theorem step_accepted {adm : Admission} {auth : Act → Prop} {s t : Execution}
    {event : Option Act} (step : Step adm auth s event t) {a : Act}
    (member : a ∈ s.accepted) : a ∈ t.accepted := by
  cases step with
  | accept b => exact (insertAct_setEq b _ a).mpr (by simp [member])
  | receive => exact member
  | duplicate => exact member
  | reject => exact member
  | wait => exact member
  | idle => exact member

/-- Persistence over any finite time interval, used for acceptance and receipt. -/
theorem persistent (P : Nat → Prop) (step : ∀ n, P n → P (n + 1))
    {n m : Nat} (le : n ≤ m) (h : P n) : P m := by
  induction m with
  | zero =>
      have eq : n = 0 := by omega
      simpa [eq] using h
  | succ m ih =>
      by_cases eq : n = m + 1
      · simpa [eq] using h
      · exact step m (ih (by omega))

/-- Accepted acts persist at later times. -/
theorem accepted_persistent {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) {a : Act} {n m : Nat} (le : n ≤ m)
    (member : a ∈ (R.run n).accepted) : a ∈ (R.run m).accepted :=
  persistent _ (fun k hk => step_accepted (R.behavior.2 k) hk) le member

/-- Received acts persist at later times. -/
theorem received_persistent {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) {a : Act} {n m : Nat} (le : n ≤ m)
    (member : a ∈ (R.run n).received) : a ∈ (R.run m).received :=
  persistent _ (fun k hk => step_received (R.behavior.2 k) hk) le member

/-- Every reachable accepted act belongs to the intended common history. -/
theorem accepted_valid {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) (n : Nat) (a : Act) (member : a ∈ (R.run n).accepted) : H.contains a :=
  R.valid_receipts n a ((reachable_wellFormed (behavior_reachable R.behavior n)).accepted_received a member)

/-- A valid receipt remains pending until accepted; false rejection cannot discard it. -/
theorem pending_or_accepted {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) (n : Nat) (a : Act) (member : a ∈ (R.run n).received) :
    a ∈ (R.run n).pending ∨ a ∈ (R.run n).accepted := by
  have invariant : ∀ n a, a ∈ (R.run n).received →
      a ∈ (R.run n).pending ∨ a ∈ (R.run n).accepted := by
    intro n
    induction n with
    | zero => rw [R.behavior.1]; simp [initial]
    | succ n ih =>
        intro a member
        have step := R.behavior.2 n
        generalize eventEq : R.events n = event at step
        generalize beforeEq : R.run n = before at step ih
        generalize afterEq : R.run (n + 1) = after at step member ⊢
        cases step with
        | receive b hb fresh =>
            simp only [List.mem_cons] at member
            rcases member with rfl | old
            · exact Or.inl (by simp)
            · rcases ih a old with hp | ha
              · exact Or.inl (by simp [hp])
              · exact Or.inr ha
        | accept b hp hv =>
            rcases ih a member with pending | accepted
            · by_cases eq : a = b
              · subst a; exact Or.inr ((insertAct_setEq b _ b).mpr (by simp))
              · exact Or.inl ((List.mem_erase_of_ne eq).mpr pending)
            · exact Or.inr ((insertAct_setEq b _ a).mpr (by simp [accepted]))
        | reject b hp hv =>
            have valid := R.valid_receipts n b (by
              exact (reachable_wellFormed (behavior_reachable R.behavior n)).pending_received b (by simpa [beforeEq] using hp))
            have impossible := H.no_reject before.accepted (fun b hb => by
              apply accepted_valid R n b
              simpa [beforeEq] using hb) b valid
            exact False.elim (impossible hv)
        | duplicate => exact ih a member
        | wait => exact ih a member
        | idle => exact ih a member
  exact invariant n a member

/-- An acceptance label in Step actually inserts the labelled act. -/
theorem label_accepted {adm : Admission} {auth : Act → Prop} {s t : Execution} {a : Act}
    (step : Step adm auth s (some a) t) : a ∈ t.accepted := by
  cases step
  exact (insertAct_setEq a _ a).mpr (by simp)

/-- Eventual receipt plus eventual continuous enabling implies acceptance under weak fairness. -/
theorem enabled_eventually_accepted {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) (a : Act) (valid : H.contains a)
    (enabled : ∃ t, ∀ n, t ≤ n → adm.admit (R.run n).accepted a = .accepted) :
    ∃ n, a ∈ (R.run n).accepted := by
  classical
  apply Classical.byContradiction
  intro never
  have absent : ∀ n, a ∉ (R.run n).accepted := by simpa using never
  obtain ⟨receipt, received⟩ := R.delivery a valid
  obtain ⟨ready, enabled⟩ := enabled
  obtain ⟨n, hn, scheduled⟩ := R.fair a (max receipt ready) (by
    intro n hn
    refine ⟨?_, enabled n (by omega)⟩
    exact (pending_or_accepted R n a (received_persistent R (by omega) received)).resolve_right (absent n))
  have step := R.behavior.2 n
  rw [scheduled] at step
  exact absent (n + 1) (label_accepted step)

/-- Finite conjunction of eventually permanent facts holds after one common time. -/
theorem eventually_all (xs : List Act) (P : Nat → Act → Prop)
    (eventual : ∀ a ∈ xs, ∃ t, ∀ n, t ≤ n → P n a) :
    ∃ t, ∀ n, t ≤ n → ∀ a ∈ xs, P n a := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a rest ih =>
      obtain ⟨headTime, head⟩ := eventual a (by simp)
      obtain ⟨tailTime, tail⟩ := ih (fun b hb => eventual b (by simp [hb]))
      refine ⟨max headTime tailTime, ?_⟩
      intro n hn b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact head n (by omega)
      · exact tail n (by omega) b hb

/-- Every valid act is eventually accepted, even for a possibly infinite history. -/
theorem eventual_acceptance {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) (a : Act) (valid : H.contains a) :
    ∃ t, ∀ n, t ≤ n → a ∈ (R.run n).accepted := by
  have allRanks : ∀ rank a, H.rank a = rank → H.contains a → ∃ n, a ∈ (R.run n).accepted := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro a equal valid
        apply enabled_eventually_accepted R a valid
        obtain ⟨t, allDeps⟩ := eventually_all (H.dependencies a) (fun n b => b ∈ (R.run n).accepted) (by
          intro b hb
          obtain ⟨n, hn⟩ := ih (H.rank b) (by rw [← equal]; exact H.lower a valid b hb) b rfl (H.closed a valid b hb)
          exact ⟨n, fun m hm => accepted_persistent R hm hn⟩)
        exact ⟨t, fun n hn => H.enabled _ (accepted_valid R n) a valid (allDeps n hn)⟩
  obtain ⟨n, member⟩ := allRanks (H.rank a) a rfl valid
  exact ⟨n, fun m hm => accepted_persistent R hm member⟩

/-- Any act accepted by one compliant replica eventually reaches every other replica. -/
theorem eventual_dissemination {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (a : Act) (n : Nat)
    (accepted : a ∈ (left.run n).accepted) :
    ∃ t, ∀ m, t ≤ m → a ∈ (right.run m).accepted :=
  eventual_acceptance right a (accepted_valid left n a accepted)

/-- A finite complete valid history eventually equals each replica's accepted set. -/
theorem finite_history_stabilizes {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) (history : List Act)
    (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n, t ≤ n → SetEq (R.run n).accepted history := by
  obtain ⟨t, all⟩ := eventually_all history (fun n a => a ∈ (R.run n).accepted)
    (fun a ha => eventual_acceptance R a ((complete a).mpr ha))
  exact ⟨t, fun n hn a => ⟨fun ha => (complete a).mp (accepted_valid R n a ha), all n hn a⟩⟩

/-- Strong eventual consistency: two fair replicas permanently agree after finite completion. -/
theorem strong_eventual_consistency {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (context : Context) (clause : Compiled)
    (history : List Act) (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m →
      List.Forall₂ (fun a b => a.1 = b.1 ∧ Equivalent a.2 b.2)
        (evaluateFields (context.input (left.run n).accepted) clause.domains clause.fields)
        (evaluateFields (context.input (right.run m).accepted) clause.domains clause.fields) := by
  obtain ⟨tl, hl⟩ := finite_history_stabilizes left history complete
  obtain ⟨tr, hr⟩ := finite_history_stabilizes right history complete
  refine ⟨max tl tr, ?_⟩
  intro n m hn hm
  apply clause_strong_convergence context clause
    (reachable_wellFormed (behavior_reachable left.behavior n)).accepted_unique
    (reachable_wellFormed (behavior_reachable right.behavior m)).accepted_unique
  intro a
  exact (hl n (by omega) a).trans (hr m (by omega) a).symm

end CBCL.StateKernelDelivery
