import LeanCbcl.ConsensusFree.Coverage

namespace CBCL.ConsensusFree
variable {A T P R f : Nat}

inductive Command (A T P : Nat) where
  | sign (tx : Fin T) (w : Nat)
  | freeze (e : Epoch A P) (w : Nat)
  | release (tx : Fin T) (w : Nat)
  | endorse (p : Fin P) (w : Nat)
  | record (p : Fin P) (w : Nat)
  | install (p : Fin P) (w : Nat)
  | receiveOperation (tx : Fin T) (w : Nat)
  | receiveFinal (tx : Fin T) (w : Nat)
  | effect (tx : Fin T) (w : Nat)
  | fence (tx : Fin T) (w : Nat)
  | wait
  deriving DecidableEq, Repr

def perform (c : Config A T P R f) (s : State A T P R) (command : Command A T P) :
    Option (Option (Fin T) × State A T P R) :=
  match command with
  | .sign tx w =>
      if Member c w then
        if s.signatures tx w = true then some (none, s)
        else if SignAllowed c s tx w then some (none, signed s tx w) else none
      else none
  | .freeze e w => if Member c w then some (none, freeze s e w) else none
  | .release tx w =>
      if Member c w ∧ s.signatures tx w = true ∧ cancelCert c s tx = true then
        some (none, release s tx w) else none
  | .endorse p w =>
      if Member c w ∧ EndorseAllowed c s p w then some (none, endorse c s p w) else none
  | .record p w =>
      if Member c w ∧ checkpointCert c s p = true ∧ ManifestLive c s p then some (none, record c s p w) else none
  | .install p w =>
      if Member c w then
        if s.active w (c.checkpoints p).owner = .checkpoint p then some (none, s)
        else if s.seenCheckpoint p w = true ∧ s.active w (c.checkpoints p).owner = (c.checkpoints p).parent ∧
            (∀ tx, (c.checkpoints p).credited tx = true → s.seenFinal tx w = true) then
          some (none, install c s p w) else none
      else none
  | .receiveOperation tx w =>
      if Member c w ∧ operationCert c s tx = true then some (none, receiveOperation s tx w) else none
  | .receiveFinal tx w =>
      if Member c w ∧ finalCert c s tx = true then some (none, receiveFinal s tx w) else none
  | .effect tx w =>
      if Member c w ∧ EffectAllowed c s tx w then
        some ((if newlyFinal c s tx w then some tx else none), effect c s tx w) else none
  | .fence tx w =>
      if Member c w ∧ FenceAllowed c s tx w then some (none, fence s tx w) else none
  | .wait => some (none, s)

theorem perform_sound (c : Config A T P R f) (s : State A T P R) (command : Command A T P)
    (result : perform c s command = some (label, t)) : Step c s label t := by
  cases command with
  | sign tx w =>
      simp only [perform] at result
      split at result
      next member =>
        split at result
        next => cases result; exact Step.replay _
        next notSigned =>
          split at result
          next allowed =>
            have fresh : s.signatures tx w = false := by cases bit : s.signatures tx w <;> simp_all
            cases result; exact Step.sign s tx w member fresh allowed
          next => simp at result
      next => simp at result
  | freeze e w =>
      simp only [perform] at result
      split at result
      next member => cases result; exact Step.freeze s e w member
      next => simp at result
  | release tx w =>
      simp only [perform] at result
      split at result
      next guard => cases result; exact Step.release s tx w guard.1 guard.2.1 guard.2.2
      next => simp at result
  | endorse p w =>
      simp only [perform] at result
      split at result
      next guard => cases result; exact Step.endorse s p w guard.1 guard.2
      next => simp at result
  | record p w =>
      simp only [perform] at result
      split at result
      next guard => cases result; exact Step.record s p w guard.1 guard.2.1 guard.2.2
      next => simp at result
  | install p w =>
      simp only [perform] at result
      split at result
      next member =>
        split at result
        next => cases result; exact Step.replay _
        next =>
          split at result
          next guard => cases result; exact Step.install s p w member guard.1 guard.2.1 guard.2.2
          next => simp at result
      next => simp at result
  | receiveOperation tx w =>
      simp only [perform] at result
      split at result
      next guard => cases result; exact Step.receiveOperation s tx w guard.1 guard.2
      next => simp at result
  | receiveFinal tx w =>
      simp only [perform] at result
      split at result
      next guard => cases result; exact Step.receiveFinal s tx w guard.1 guard.2
      next => simp at result
  | effect tx w =>
      simp only [perform] at result
      split at result
      next guard => cases result; exact Step.effect s tx w guard.1 guard.2
      next => simp at result
  | fence tx w =>
      simp only [perform] at result
      split at result
      next guard => cases result; exact Step.fence s tx w guard.1 guard.2
      next => simp at result
  | wait => cases result; exact Step.replay _

def execute (c : Config A T P R f) (s : State A T P R) (command : Command A T P) : Option (Fin T) × State A T P R :=
  (perform c s command).getD (none, s)

theorem execute_sound (c : Config A T P R f) (s : State A T P R) (command : Command A T P) :
    Step c s (execute c s command).1 (execute c s command).2 := by
  unfold execute
  cases result : perform c s command with
  | none => exact Step.replay _
  | some pair => exact perform_sound c s command result

inductive Trace (c : Config A T P R f) : State A T P R → List (Option (Fin T)) → State A T P R → Prop where
  | nil (s) : Trace c s [] s
  | cons : Step c s label mid → Trace c mid labels t → Trace c s (label :: labels) t

def run (c : Config A T P R f) (s : State A T P R) : List (Command A T P) → List (Option (Fin T)) × State A T P R
  | [] => ([], s)
  | command :: rest =>
      let next := execute c s command
      let tailResult := run c next.2 rest
      (next.1 :: tailResult.1, tailResult.2)

theorem run_trace (c : Config A T P R f) (s : State A T P R) (commands : List (Command A T P)) :
    Trace c s (run c s commands).1 (run c s commands).2 := by
  induction commands generalizing s with
  | nil => exact Trace.nil s
  | cons command rest ih => exact Trace.cons (execute_sound c s command) (ih _)

theorem trace_invariant {c : Config A T P R f} {s t : State A T P R} {labels}
    (h : Invariant c s) (trace : Trace c s labels t) : Invariant c t := by
  revert h
  induction trace with
  | nil => intro h; exact h
  | cons step rest ih => intro h; exact ih (step_invariant h step)

def BusinessStep (c : Config A T P R f) (before : Fin R → Int) (tx : Fin T) (after : Fin R → Int) : Prop :=
  c.authorized tx = true ∧ (∀ d, (c.cost tx d : Int) ≤ before d) ∧
    after = fun d => before d + c.credit tx d - c.cost tx d

def Simulates (c : Config A T P R f) (s : State A T P R) (label : Option (Fin T)) (t : State A T P R) : Prop :=
  match label with
  | none => t.balance = s.balance
  | some tx => BusinessStep c s.balance tx t.balance

/-- Funding is derived from cross-epoch bounds and disjoint business vectors.
It is neither a signing guard nor a per-step resource-safety premise. -/
theorem step_simulation {c : Config A T P R f} {s t : State A T P R} {label}
    (h : Invariant c s) (step : Step c s label t) : Simulates c s label t := by
  have newer := step_invariant h step
  cases step with
  | sign => rfl
  | freeze => rfl
  | release => rfl
  | endorse => rfl
  | record => rfl
  | install => rfl
  | receiveOperation => rfl
  | receiveFinal => rfl
  | fence => rfl
  | replay => rfl
  | effect tx w member allowed =>
      by_cases new : newlyFinal c s tx w = true
      · have finalNow : finalCert c (effect c s tx w) tx = true := by
          simpa [effect, new, finalCert] using (newly_final_data new).2
        have op := final_operation newer.evidence tx finalNow
        obtain ⟨v, hv, signature⟩ := quorum_has_core c _ op
        have auth := newer.evidence.signature_auth tx v hv signature
        simp only [new, ↓reduceIte, Simulates, effect]
        refine ⟨auth, ?_, rfl⟩
        intro d
        have before := resource_nonnegative h d
        have after := resource_nonnegative newer d
        rw [effect, if_pos new] at after
        change 0 ≤ s.balance d + (c.credit tx d : Int) - (c.cost tx d : Int) at after
        rcases c.disjoint tx d with noCost | noCredit
        · rw [noCost]; omega
        · rw [noCredit] at after; omega
      · simp only [new, Bool.false_eq_true, ↓reduceIte, Simulates, effect]
        simp [emit]

inductive BusinessRun (c : Config A T P R f) : (Fin R → Int) → List (Fin T) → (Fin R → Int) → Prop where
  | nil (balance) : BusinessRun c balance [] balance
  | cons : BusinessStep c before tx mid → BusinessRun c mid txs after → BusinessRun c before (tx :: txs) after

theorem trace_simulation {c : Config A T P R f} {s t : State A T P R} {labels}
    (h : Invariant c s) (trace : Trace c s labels t) : BusinessRun c s.balance (labels.filterMap id) t.balance := by
  revert h
  induction trace with
  | nil => intro _; exact BusinessRun.nil _
  | @cons s label mid labels t step rest ih =>
      intro h
      have tailRun := ih (step_invariant h step)
      have simulation := step_simulation h step
      cases label with
      | none =>
          change mid.balance = s.balance at simulation
          simpa only [List.filterMap_cons, id_eq, List.filterMap_cons_none, simulation] using tailRun
      | some tx => exact BusinessRun.cons simulation tailRun

/-- Consensus-free refinement for every executable finite asynchronous schedule. -/
theorem full_async_refinement (c : Config A T P R f) (commands : List (Command A T P)) :
    BusinessRun c (initial c).balance ((run c (initial c) commands).1.filterMap id)
      (run c (initial c) commands).2.balance :=
  trace_simulation (initial_invariant c) (run_trace c (initial c) commands)

theorem all_schedules_nonnegative (c : Config A T P R f) (commands : List (Command A T P)) :
    ∀ d, 0 ≤ (run c (initial c) commands).2.balance d :=
  resource_nonnegative (trace_invariant (initial_invariant c) (run_trace c (initial c) commands))

theorem trace_journals {c : Config A T P R f} {s t : State A T P R} {labels}
    (trace : Trace c s labels t) : JournalExtension s t := by
  induction trace with
  | nil => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | cons step rest ih =>
      have one := step_journals step
      exact ⟨fun tx w vote => ih.signatures tx w (one.signatures tx w vote),
        fun tx w vote => ih.effects tx w (one.effects tx w vote),
        fun tx w vote => ih.fences tx w (one.fences tx w vote),
        fun p w vote => ih.votes p w (one.votes p w vote),
        fun e w vote => ih.seals e w (one.seals e w vote)⟩

/-- Local release cannot be spent again by any late old effects certificate. -/
theorem released_never_finalizes {c : Config A T P R f} {s t : State A T P R} {labels}
    (h : Invariant c s) (trace : Trace c s labels t) (tx : Fin T) (w : Nat)
    (honest : w ∈ c.committee.core) (released : s.released tx w = true) : finalCert c t tx = false := by
  have oldCancel := h.evidence.released_cancel tx w honest released
  have cancel := quorum_mono c _ _ ((trace_journals trace).fences tx) oldCancel
  have newer := trace_invariant h trace
  have impossible := final_cancel_exclusive newer.evidence tx
  cases final : finalCert c t tx with
  | false => rfl
  | true => exact False.elim (impossible ⟨final, cancel⟩)

theorem infinite_async_refinement (c : Config A T P R f) (states : Nat → State A T P R)
    (labels : Nat → Option (Fin T)) (start : states 0 = initial c)
    (steps : ∀ n, Step c (states n) (labels n) (states (n+1))) :
    (∀ n, Invariant c (states n)) ∧
    (∀ n, Simulates c (states n) (labels n) (states (n+1))) ∧
    (∀ n d, 0 ≤ (states n).balance d) := by
  have valid : ∀ n, Invariant c (states n) := by
    intro n
    induction n with
    | zero => rw [start]; exact initial_invariant c
    | succ n ih => exact step_invariant ih (steps n)
  exact ⟨valid, (fun n => step_simulation (valid n) (steps n)), (fun n => resource_nonnegative (valid n))⟩

end CBCL.ConsensusFree
