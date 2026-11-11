import LeanCbcl.StateLVar

/-!
# SPEC-038: operational quasi-determinism for concurrent threshold programs

`StateLVar.threshold_quasi_determinism` is a statement about two carrier
values. This module lifts it to *programs*: any number of agents, each running
an arbitrary sequential program that contributes to a shared carrier and
branches on the results of threshold reads, interleaved by an arbitrary
scheduler with arbitrary partial delivery.

## Model

* A program (`Proc`) is `done r`, `put d k` (contribute `d`, continue as `k`),
  or `get Q k` (block until an alternative `q` of the query `Q` is reached,
  continue as `k q`). The continuation of a read is an arbitrary function of
  the result, so control flow may depend on what was read.
* A configuration holds the joint `evidence` (the join of everything issued),
  one local `view` per agent, and one program state per agent.
* A step is a `put` by one agent (joined into the evidence and into its own
  view), a `get` by one agent against **its own view**, or a `deliver` that
  joins any element below the joint evidence into one agent's view.
* A run is any finite sequence of steps. No fairness, delivery order or
  delivery completeness is assumed.

## Results

* `operational_quasi_determinism`: two runs of the same programs in which
  every agent has finished return the same results and hold the same joint
  evidence, or the joint evidence of both is the conflict top.
* `clean_run_dominates`: if some finished run ends with non-conflicting
  evidence, then in every configuration reachable under any schedule the
  evidence is below that run's evidence and every agent is still on the
  finished run's path.
* `Sharp.results_can_differ_under_conflict`: the conflict disjunct is
  inhabited, so the theorem cannot be strengthened to plain determinism.
* `Sharp.solo_is_deterministic`: the clean disjunct is inhabited too.

## Boundaries

The theorem is a safety statement about finished runs. Delivery and fairness
are what make a blocked `get` proceed, so they bear on termination and not on
agreement, which is why they do not appear as premises. The model sits at the
carrier, after admission: causal dependencies and address consistency are
premises of the results that connect accepted histories to carrier values
(`StateLift.lift_setEq`, `StateAuthoredQuasiDeterminism`), not of this one.
The agent set is fixed and each program is well founded. Snapshot reads and
freezes are outside the model: a snapshot is not stable under growth, and two
schedules can select different causal cuts for a freeze without any conflict,
so neither satisfies this statement. Nothing here is inherited from the
LVish calculus theorem, and no correspondence with the Rust runtime is
claimed.
-/

set_option autoImplicit false

namespace CBCL.StateOperational
open State StateLift StateLVar

universe u v

/-! ## Order facts used below -/

section Order
variable {L : Type u} [BoundedJoinSemilattice L]

theorem bot_below (a : L) : Below (⊥ : L) a := by
  unfold Below
  exact bot_join a

theorem below_antisymm {a b : L} (ab : Below a b) (ba : Below b a) : a = b := by
  unfold Below at *
  calc a = b ⊔ a := ba.symm
       _ = a ⊔ b := join_comm b a
       _ = b := ab

/-- Anything below a non-conflicting value is non-conflicting. -/
theorem ordinary_of_below {x y : L} (below : Below x y) (ordinary : y ≠ ⊤) : x ≠ ⊤ := by
  intro top
  rw [top] at below
  exact ordinary (top_below below)

end Order

/-! ## Programs -/

/-- A threshold query: its alternatives and the pairwise incompatibility that
installation checks. -/
structure Query (L : Type u) [BoundedJoinSemilattice L] where
  /-- The readable alternatives. -/
  alternatives : L → Prop
  /-- Distinct alternatives join to the conflict top. -/
  incompatible : Incompatible alternatives

/-- A sequential agent program over carrier `L` returning a result in `R`. -/
inductive Proc (L : Type u) [BoundedJoinSemilattice L] (R : Type v) : Type (max u v) where
  /-- Finished, with a result. -/
  | done (result : R) : Proc L R
  /-- Contribute to the carrier, then continue. -/
  | put (contribution : L) (next : Proc L R) : Proc L R
  /-- Threshold read: wait for an alternative, then continue with it. -/
  | get (query : Query L) (next : L → Proc L R) : Proc L R

section Programs
variable {L : Type u} [BoundedJoinSemilattice L] {R : Type v}

/-- In a non-conflicting state a query has at most one successful alternative. -/
theorem successful_unique (Q : Query L) {x a b : L}
    (left : Successful Q.alternatives x a) (right : Successful Q.alternatives x b) : a = b := by
  rcases threshold_quasi_determinism Q.incompatible left right with equal | conflict
  · exact equal
  · rw [join_idem] at conflict
    exact absurd conflict left.1

/-- Progress of one program that the carrier value `x` justifies: every
contribution made is below `x`, and every read returned the alternative that
is successful at `x`. -/
inductive Along (x : L) : Proc L R → Proc L R → Prop where
  /-- No progress. -/
  | refl (p : Proc L R) : Along x p p
  /-- A contribution below `x`. -/
  | put {d : L} {k p : Proc L R} (below : Below d x) (rest : Along x k p) :
      Along x (.put d k) p
  /-- A read returning the alternative successful at `x`. -/
  | get {Q : Query L} {k : L → Proc L R} {q : L} {p : Proc L R}
      (reached : Successful Q.alternatives x q) (rest : Along x (k q) p) :
      Along x (.get Q k) p

theorem Along.trans {x : L} {p q r : Proc L R} (first : Along x p q) (second : Along x q r) :
    Along x p r := by
  induction first with
  | refl _ => exact second
  | put below _ ih => exact .put below (ih second)
  | get reached _ ih => exact .get reached (ih second)

/-- A finished program makes no further progress. -/
theorem Along.done_eq {x : L} {r : R} {p : Proc L R} (h : Along x (.done r) p) : p = .done r := by
  cases h
  rfl

/-- **Paths are linear.** Two justified progressions of one program lie on a
single path: at a fixed non-conflicting carrier value a program has no choice. -/
theorem Along.linear {x : L} {p a b : Proc L R} (first : Along x p a) (second : Along x p b) :
    Along x a b ∨ Along x b a := by
  induction first generalizing b with
  | refl _ => exact Or.inl second
  | put below rest ih =>
    cases second with
    | refl => exact Or.inr (.put below rest)
    | put _ rest' => exact ih rest'
  | get reached rest ih =>
    cases second with
    | refl => exact Or.inr (.get reached rest)
    | get reached' rest' =>
      have same := successful_unique _ reached reached'
      subst same
      exact ih rest'

/-- Justified progress survives growth of the carrier value short of conflict. -/
theorem Along.mono {x y : L} {p q : Proc L R} (growth : Below x y) (ordinary : y ≠ ⊤)
    (h : Along x p q) : Along y p q := by
  induction h with
  | refl p => exact .refl p
  | put below _ ih => exact .put (below_trans below growth) ih
  | get reached _ ih => exact .get (success_persists reached growth ordinary) ih

end Programs

/-! ## Configurations, steps and runs -/

/-- A configuration of agents indexed by `ι`. -/
structure Config (ι : Type) (L : Type u) [BoundedJoinSemilattice L] (R : Type v) where
  /-- The join of every contribution issued so far, by any agent. -/
  evidence : L
  /-- What each agent has received, its own contributions included. -/
  view : ι → L
  /-- Each agent's remaining program. -/
  proc : ι → Proc L R

section Semantics
variable {ι : Type} {L : Type u} [BoundedJoinSemilattice L] {R : Type v}

/-- All agents start with an empty view and nothing has been issued. -/
def initial (prog : ι → Proc L R) : Config ι L R :=
  { evidence := ⊥, view := fun _ => ⊥, proc := prog }

/-- One scheduler step. Each case states the effect on the acting agent and
that every other agent is unchanged. -/
inductive Step : Config ι L R → Config ι L R → Prop where
  /-- Agent `i` issues `d`: it joins the evidence and the agent's own view. -/
  | put {c c' : Config ι L R} (i : ι) (d : L) (k : Proc L R)
      (at_put : c.proc i = .put d k)
      (proc_self : c'.proc i = k)
      (proc_other : ∀ j, j ≠ i → c'.proc j = c.proc j)
      (view_self : c'.view i = c.view i ⊔ d)
      (view_other : ∀ j, j ≠ i → c'.view j = c.view j)
      (evidence_eq : c'.evidence = c.evidence ⊔ d) : Step c c'
  /-- Agent `i` reads against its own view and continues with the result. -/
  | get {c c' : Config ι L R} (i : ι) (Q : Query L) (k : L → Proc L R) (q : L)
      (at_get : c.proc i = .get Q k)
      (reached : Successful Q.alternatives (c.view i) q)
      (proc_self : c'.proc i = k q)
      (proc_other : ∀ j, j ≠ i → c'.proc j = c.proc j)
      (view_eq : c'.view = c.view)
      (evidence_eq : c'.evidence = c.evidence) : Step c c'
  /-- Agent `i` receives `e`, any element below the joint evidence. -/
  | deliver {c c' : Config ι L R} (i : ι) (e : L)
      (available : Below e c.evidence)
      (view_self : c'.view i = c.view i ⊔ e)
      (view_other : ∀ j, j ≠ i → c'.view j = c.view j)
      (proc_eq : c'.proc = c.proc)
      (evidence_eq : c'.evidence = c.evidence) : Step c c'

/-- Finite runs from a fixed start, under any schedule. -/
inductive Run (start : Config ι L R) : Config ι L R → Prop where
  /-- The empty run. -/
  | refl : Run start start
  /-- A run extended by one step. -/
  | step {b c : Config ι L R} (earlier : Run start b) (last : Step b c) : Run start c

/-- The joint evidence only grows. -/
theorem Step.evidence_grows {b c : Config ι L R} (step : Step b c) :
    Below b.evidence c.evidence := by
  cases step with
  | put i d k _ _ _ _ _ evidence_eq => rw [evidence_eq]; exact below_left _ _
  | get i Q k q _ _ _ _ _ evidence_eq => rw [evidence_eq]; exact below_refl _
  | deliver i e _ _ _ _ evidence_eq => rw [evidence_eq]; exact below_refl _

/-- No agent's view exceeds the joint evidence. -/
theorem Run.view_below_evidence {prog : ι → Proc L R} {c : Config ι L R}
    (run : Run (initial prog) c) : ∀ i, Below (c.view i) c.evidence := by
  induction run with
  | refl => intro i; exact below_refl _
  | step _ last ih =>
    intro j
    cases last with
    | put i d k _ _ _ view_self view_other evidence_eq =>
      rcases Classical.em (j = i) with same | other
      · subst same
        rw [view_self, evidence_eq]
        exact join_below (below_trans (ih j) (below_left _ _)) (below_right _ _)
      · rw [view_other j other, evidence_eq]
        exact below_trans (ih j) (below_left _ _)
    | get i Q k q _ _ _ _ view_eq evidence_eq =>
      rw [view_eq, evidence_eq]
      exact ih j
    | deliver i e available view_self view_other _ evidence_eq =>
      rcases Classical.em (j = i) with same | other
      · subst same
        rw [view_self, evidence_eq]
        exact join_below (ih j) available
      · rw [view_other j other, evidence_eq]
        exact ih j

/-- **A run justifies itself.** If the evidence of a reachable configuration
is not in conflict, each agent's progress is justified by that evidence: its
contributions are below it, and its reads, made against smaller views, still
return the same alternatives there. -/
theorem Run.self_justified {prog : ι → Proc L R} {c : Config ι L R}
    (run : Run (initial prog) c) (ordinary : c.evidence ≠ ⊤) :
    ∀ i, Along c.evidence (prog i) (c.proc i) := by
  induction run with
  | refl => intro i; exact .refl _
  | @step b c earlier last ih =>
    have grows := last.evidence_grows
    have lifted : ∀ i, Along c.evidence (prog i) (b.proc i) :=
      fun i => (ih (ordinary_of_below grows ordinary) i).mono grows ordinary
    have views := earlier.view_below_evidence
    intro j
    cases last with
    | put i d k at_put proc_self proc_other _ _ evidence_eq =>
      rcases Classical.em (j = i) with same | other
      · subst same
        have here := lifted j
        rw [at_put] at here
        rw [proc_self]
        exact here.trans (.put (by rw [evidence_eq]; exact below_right _ _) (.refl k))
      · rw [proc_other j other]
        exact lifted j
    | get i Q k q at_get reached proc_self proc_other _ evidence_eq =>
      rcases Classical.em (j = i) with same | other
      · subst same
        have here := lifted j
        rw [at_get] at here
        rw [proc_self]
        have atEvidence : Successful Q.alternatives c.evidence q :=
          success_persists reached (by rw [evidence_eq]; exact views j) ordinary
        exact here.trans (.get atEvidence (.refl _))
      · rw [proc_other j other]
        exact lifted j
    | deliver i e _ _ _ proc_eq _ =>
      rw [proc_eq]
      exact lifted j

/-- **Every schedule stays inside a clean outcome.** Suppose the carrier value
`x` is not in conflict and justifies running every agent's program to
completion. Then in every reachable configuration, under any schedule and any
delivery, the joint evidence is below `x` and every agent's progress is
justified by `x`. -/
theorem Run.dominated {prog : ι → Proc L R} {x : L} (ordinary : x ≠ ⊤)
    (clean : ∀ i, ∃ r, Along x (prog i) (.done r)) {c : Config ι L R}
    (run : Run (initial prog) c) :
    Below c.evidence x ∧ ∀ i, Along x (prog i) (c.proc i) := by
  induction run with
  | refl => exact ⟨bot_below x, fun i => .refl _⟩
  | @step b c earlier last ih =>
    obtain ⟨below, along⟩ := ih
    have views := earlier.view_below_evidence
    cases last with
    | put i d k at_put proc_self proc_other _ _ evidence_eq =>
      have here := along i
      rw [at_put] at here
      obtain ⟨r, finish⟩ := clean i
      have contribution : Below d x := by
        rcases here.linear finish with forward | backward
        · cases forward with
          | put below' _ => exact below'
        · cases backward
      refine ⟨by rw [evidence_eq]; exact join_below below contribution, fun j => ?_⟩
      rcases Classical.em (j = i) with same | other
      · subst same
        rw [proc_self]
        exact here.trans (.put contribution (.refl k))
      · rw [proc_other j other]
        exact along j
    | get i Q k q at_get reached proc_self proc_other _ evidence_eq =>
      refine ⟨by rw [evidence_eq]; exact below, fun j => ?_⟩
      rcases Classical.em (j = i) with same | other
      · subst same
        have here := along j
        rw [at_get] at here
        rw [proc_self]
        exact here.trans
          (.get (success_persists reached (below_trans (views j) below) ordinary) (.refl _))
      · rw [proc_other j other]
        exact along j
    | deliver i e _ _ _ proc_eq evidence_eq =>
      exact ⟨by rw [evidence_eq]; exact below, fun j => by rw [proc_eq]; exact along j⟩

/-! ## The theorems -/

/-- A finished run whose evidence is not in conflict fixes the outcome of
every other finished run of the same programs. -/
theorem clean_run_decides {prog : ι → Proc L R} {c₁ c₂ : Config ι L R} {r₁ r₂ : ι → R}
    (run₁ : Run (initial prog) c₁) (run₂ : Run (initial prog) c₂)
    (done₁ : ∀ i, c₁.proc i = .done (r₁ i)) (done₂ : ∀ i, c₂.proc i = .done (r₂ i))
    (ordinary : c₁.evidence ≠ ⊤) : r₁ = r₂ ∧ c₁.evidence = c₂.evidence := by
  have path₁ : ∀ i, Along c₁.evidence (prog i) (.done (r₁ i)) := fun i => by
    have h := run₁.self_justified ordinary i
    rw [done₁ i] at h
    exact h
  obtain ⟨below₂, along₂⟩ := Run.dominated ordinary (fun i => ⟨r₁ i, path₁ i⟩) run₂
  have ordinary₂ : c₂.evidence ≠ ⊤ := ordinary_of_below below₂ ordinary
  have path₂ : ∀ i, Along c₂.evidence (prog i) (.done (r₂ i)) := fun i => by
    have h := run₂.self_justified ordinary₂ i
    rw [done₂ i] at h
    exact h
  obtain ⟨below₁, _⟩ := Run.dominated ordinary₂ (fun i => ⟨r₂ i, path₂ i⟩) run₁
  refine ⟨funext fun i => ?_, below_antisymm below₁ below₂⟩
  have other := along₂ i
  rw [done₂ i] at other
  rcases (path₁ i).linear other with forward | backward
  · exact (Proc.done.inj forward.done_eq).symm
  · exact Proc.done.inj backward.done_eq

/-- **Operational quasi-determinism.** Take any agents, any programs, and any
two runs, under any schedules and any delivery, in which every agent has
finished. Either the two runs return the same results and hold the same joint
evidence, or the joint evidence of both is the conflict top. -/
theorem operational_quasi_determinism {prog : ι → Proc L R} {c₁ c₂ : Config ι L R}
    {r₁ r₂ : ι → R}
    (run₁ : Run (initial prog) c₁) (run₂ : Run (initial prog) c₂)
    (done₁ : ∀ i, c₁.proc i = .done (r₁ i)) (done₂ : ∀ i, c₂.proc i = .done (r₂ i)) :
    (r₁ = r₂ ∧ c₁.evidence = c₂.evidence) ∨ (c₁.evidence = ⊤ ∧ c₂.evidence = ⊤) := by
  rcases Classical.em (c₁.evidence = ⊤) with top₁ | ordinary₁
  · rcases Classical.em (c₂.evidence = ⊤) with top₂ | ordinary₂
    · exact Or.inr ⟨top₁, top₂⟩
    · obtain ⟨results, evidence⟩ := clean_run_decides run₂ run₁ done₂ done₁ ordinary₂
      exact Or.inl ⟨results.symm, evidence.symm⟩
  · exact Or.inl (clean_run_decides run₁ run₂ done₁ done₂ ordinary₁)

/-- Different results are evidence of conflict in both runs. -/
theorem different_results_expose_conflict {prog : ι → Proc L R} {c₁ c₂ : Config ι L R}
    {r₁ r₂ : ι → R}
    (run₁ : Run (initial prog) c₁) (run₂ : Run (initial prog) c₂)
    (done₁ : ∀ i, c₁.proc i = .done (r₁ i)) (done₂ : ∀ i, c₂.proc i = .done (r₂ i))
    (different : r₁ ≠ r₂) : c₁.evidence = ⊤ ∧ c₂.evidence = ⊤ := by
  rcases operational_quasi_determinism run₁ run₂ done₁ done₂ with ⟨same, _⟩ | conflict
  · exact absurd same different
  · exact conflict

/-- **No schedule leaves the clean path.** If one finished run ends with
evidence that is not in conflict, then every configuration reachable under
any schedule has evidence below it, and every agent in that configuration can
still reach its result in the finished run. No agent has read anything the
finished run did not read. -/
theorem clean_run_dominates {prog : ι → Proc L R} {c₁ c : Config ι L R} {r₁ : ι → R}
    (run₁ : Run (initial prog) c₁) (done₁ : ∀ i, c₁.proc i = .done (r₁ i))
    (ordinary : c₁.evidence ≠ ⊤) (run : Run (initial prog) c) :
    Below c.evidence c₁.evidence ∧ ∀ i, Along c₁.evidence (c.proc i) (.done (r₁ i)) := by
  have path₁ : ∀ i, Along c₁.evidence (prog i) (.done (r₁ i)) := fun i => by
    have h := run₁.self_justified ordinary i
    rw [done₁ i] at h
    exact h
  obtain ⟨below, along⟩ := Run.dominated ordinary (fun i => ⟨r₁ i, path₁ i⟩) run
  refine ⟨below, fun i => ?_⟩
  rcases (along i).linear (path₁ i) with forward | backward
  · exact forward
  · rw [backward.done_eq]
    exact .refl _

end Semantics

/-! ## Sharpness: results can differ when the evidence conflicts -/

namespace Sharp

/-- The four-element carrier: nothing, one of two incompatible choices, or
both, which is the conflict top. -/
inductive Fork where
  /-- No choice made: the bottom. -/
  | none
  /-- The first choice. -/
  | left
  /-- The second choice. -/
  | right
  /-- Both choices: the conflict top. -/
  | both
  deriving DecidableEq

/-- Join in the diamond. -/
def Fork.join : Fork → Fork → Fork
  | .none, x => x
  | x, .none => x
  | .left, .left => .left
  | .right, .right => .right
  | _, _ => .both

instance : BoundedJoinSemilattice Fork where
  join := Fork.join
  join_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  join_comm := by intro a b; cases a <;> cases b <;> rfl
  join_idem := by intro a; cases a <;> rfl
  bot := .none
  bot_join := by intro a; cases a <;> rfl
  top := .both
  join_top := by intro a; cases a <;> rfl

/-- Two writers and one reader. -/
inductive Agent where
  /-- Issues `left`. -/
  | first
  /-- Issues `right`. -/
  | second
  /-- Reads the choice. -/
  | reader
  deriving DecidableEq

/-- Read whichever choice has been made. -/
def choice : Query Fork where
  alternatives q := q = .left ∨ q = .right
  incompatible := by
    intro a b ha hb different
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl different
    · rfl
    · rfl
    · exact absurd rfl different

/-- The writers issue incompatible choices; the reader returns what it reads. -/
def program : Agent → Proc Fork Fork
  | .first => .put .left (.done .none)
  | .second => .put .right (.done .none)
  | .reader => .get choice (fun q => .done q)

/-- A configuration given agent by agent. -/
def config (evidence : Fork) (v₁ v₂ v₃ : Fork) (p₁ p₂ p₃ : Proc Fork Fork) :
    Config Agent Fork Fork where
  evidence := evidence
  view
    | .first => v₁
    | .second => v₂
    | .reader => v₃
  proc
    | .first => p₁
    | .second => p₂
    | .reader => p₃

/-- A writer that has finished. -/
def writerDone : Proc Fork Fork := .done .none
/-- The first writer before it issues. -/
def firstTodo : Proc Fork Fork := .put .left (.done .none)
/-- The second writer before it issues. -/
def secondTodo : Proc Fork Fork := .put .right (.done .none)
/-- The reader before it reads. -/
def readerTodo : Proc Fork Fork := .get choice (fun q => .done q)

theorem initial_eq :
    initial program = config .none .none .none .none firstTodo secondTodo readerTodo := by
  unfold initial config
  congr 1 <;> funext i <;> cases i <;> rfl

/-- Results when the reader sees `left`. -/
def resultsLeft : Agent → Fork
  | .reader => .left
  | _ => .none

/-- Results when the reader sees `right`. -/
def resultsRight : Agent → Fork
  | .reader => .right
  | _ => .none

/-- The first writer goes first and the reader sees `left`. -/
theorem run_left : Run (initial program)
    (config .both .left .right .left writerDone writerDone (.done .left)) := by
  rw [initial_eq]
  have s₁ : Step (config .none .none .none .none firstTodo secondTodo readerTodo)
      (config .left .left .none .none writerDone secondTodo readerTodo) :=
    .put .first .left (.done .none) rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
  have s₂ : Step (config .left .left .none .none writerDone secondTodo readerTodo)
      (config .left .left .none .left writerDone secondTodo readerTodo) :=
    .deliver .reader .left rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl rfl
  have s₃ : Step (config .left .left .none .left writerDone secondTodo readerTodo)
      (config .left .left .none .left writerDone secondTodo (.done .left)) :=
    .get .reader choice (fun q => .done q) .left rfl
      ⟨by decide, Or.inl rfl, rfl⟩ rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl rfl
  have s₄ : Step (config .left .left .none .left writerDone secondTodo (.done .left))
      (config .both .left .right .left writerDone writerDone (.done .left)) :=
    .put .second .right (.done .none) rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
  exact (((Run.refl.step s₁).step s₂).step s₃).step s₄

/-- The second writer goes first and the reader sees `right`. -/
theorem run_right : Run (initial program)
    (config .both .left .right .right writerDone writerDone (.done .right)) := by
  rw [initial_eq]
  have s₁ : Step (config .none .none .none .none firstTodo secondTodo readerTodo)
      (config .right .none .right .none firstTodo writerDone readerTodo) :=
    .put .second .right (.done .none) rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
  have s₂ : Step (config .right .none .right .none firstTodo writerDone readerTodo)
      (config .right .none .right .right firstTodo writerDone readerTodo) :=
    .deliver .reader .right rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl rfl
  have s₃ : Step (config .right .none .right .right firstTodo writerDone readerTodo)
      (config .right .none .right .right firstTodo writerDone (.done .right)) :=
    .get .reader choice (fun q => .done q) .right rfl
      ⟨by decide, Or.inr rfl, rfl⟩ rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl rfl
  have s₄ : Step (config .right .none .right .right firstTodo writerDone (.done .right))
      (config .both .left .right .right writerDone writerDone (.done .right)) :=
    .put .first .left (.done .none) rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
  exact (((Run.refl.step s₁).step s₂).step s₃).step s₄

/-- **The conflict disjunct is inhabited.** Two finished runs of one program
return different results. Both hold conflicting evidence, as
`operational_quasi_determinism` requires, and neither reader ever saw a
conflict in its own view. -/
theorem results_can_differ_under_conflict :
    ∃ (c₁ c₂ : Config Agent Fork Fork) (r₁ r₂ : Agent → Fork),
      Run (initial program) c₁ ∧ Run (initial program) c₂ ∧
      (∀ i, c₁.proc i = .done (r₁ i)) ∧ (∀ i, c₂.proc i = .done (r₂ i)) ∧
      r₁ ≠ r₂ ∧ c₁.evidence = ⊤ ∧ c₂.evidence = ⊤ ∧
      c₁.view .reader ≠ ⊤ ∧ c₂.view .reader ≠ ⊤ := by
  refine ⟨_, _, resultsLeft, resultsRight, run_left, run_right, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · intro same
    have at_reader := congrFun same .reader
    exact absurd at_reader (by decide)
  · show Fork.left ≠ Fork.both
    decide
  · show Fork.right ≠ Fork.both
    decide

/-- One writer and one reader: no conflict is possible. -/
def solo : Agent → Proc Fork Fork
  | .first => .put .left (.done .none)
  | .second => .done .none
  | .reader => .get choice (fun q => .done q)

theorem solo_initial_eq :
    initial solo = config .none .none .none .none firstTodo writerDone readerTodo := by
  unfold initial config
  congr 1 <;> funext i <;> cases i <;> rfl

/-- One finished run of `solo`, ending with evidence `left`. -/
theorem solo_run : Run (initial solo)
    (config .left .left .none .left writerDone writerDone (.done .left)) := by
  rw [solo_initial_eq]
  have s₁ : Step (config .none .none .none .none firstTodo writerDone readerTodo)
      (config .left .left .none .none writerDone writerDone readerTodo) :=
    .put .first .left (.done .none) rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl
  have s₂ : Step (config .left .left .none .none writerDone writerDone readerTodo)
      (config .left .left .none .left writerDone writerDone readerTodo) :=
    .deliver .reader .left rfl rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl rfl
  have s₃ : Step (config .left .left .none .left writerDone writerDone readerTodo)
      (config .left .left .none .left writerDone writerDone (.done .left)) :=
    .get .reader choice (fun q => .done q) .left rfl
      ⟨by decide, Or.inl rfl, rfl⟩ rfl
      (by intro j h; cases j <;> first | rfl | exact absurd rfl h) rfl rfl
  exact ((Run.refl.step s₁).step s₂).step s₃

/-- **The clean disjunct is inhabited.** Every finished run of `solo`, under
every schedule and delivery, returns the same results as the one above. -/
theorem solo_is_deterministic {c : Config Agent Fork Fork} {r : Agent → Fork}
    (run : Run (initial solo) c) (finished : ∀ i, c.proc i = .done (r i)) :
    r = resultsLeft ∧ c.evidence = .left := by
  have ordinary : (config .left .left .none .left writerDone writerDone
      (.done .left) : Config Agent Fork Fork).evidence ≠ ⊤ := by
    show Fork.left ≠ Fork.both
    decide
  obtain ⟨results, evidence⟩ := clean_run_decides solo_run run
    (r₁ := resultsLeft) (by intro i; cases i <;> rfl) finished ordinary
  exact ⟨results.symm, evidence.symm⟩

end Sharp

end CBCL.StateOperational
