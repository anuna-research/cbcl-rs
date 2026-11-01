import LeanCbcl.ConsensusFree.MultiParent

/-! Conditional asynchronous liveness for the existing model. Fairness schedules
actual enabled actions, never assumes certificates. Network/crypto/Rust refinement
and contention resolution are outside this theorem. No Byzantine cooperation. -/
namespace CBCL.ConsensusFree.MultiParent.Liveness
open CBCL.ValidatorBudget
variable {V T R f : Nat}

structure Execution (c : Config V T R f) where
  state : Nat → State V T
  command : Nat → Command V T
  starts : state 0 = initial
  accepted : ∀ n, perform c (state n) (command n) = some (state (n+1))

variable {c : Config V T R f}

def Execution.step (e : Execution c) (n : Nat) : Step c (e.state n) (e.state (n+1)) :=
  perform_sound (e.accepted n)

/-- Weak action fairness: continuously enabled work is eventually scheduled. -/
def WeakFair (commands : Nat → Command V T) (enabled : Nat → Prop)
    (action : Command V T) : Prop :=
  ∀ start, (∀ n, start ≤ n → enabled n) → ∃ n, start ≤ n ∧ commands n = action

def SignEnabled (c : Config V T R f) (s : State V T) (tx : Fin T) (w : Nat) : Prop :=
  s.signatures tx w = false ∧ SignAllowed c s tx w

def EffectEnabled (c : Config V T R f) (s : State V T) (tx : Fin T) (w : Nat) : Prop :=
  s.effects tx w = false ∧ operationCert c s tx = true ∧ s.fences tx w = false

/-- Combine finitely many eventual persistent facts without a bounded delay. -/
theorem finite_eventually (xs : List Nat) (p : Nat → Nat → Prop)
    (each : ∀ w ∈ xs, ∃ start, ∀ n, start ≤ n → p n w) :
    ∃ start, ∀ n, start ≤ n → ∀ w ∈ xs, p n w := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons w ws ih =>
    obtain ⟨a, ha⟩ := each w (by simp)
    obtain ⟨b, hb⟩ := ih (fun u hu => each u (by simp [hu]))
    refine ⟨max a b, ?_⟩
    intro n hn u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ha n (by omega)
    · exact hb n (by omega) u hu

theorem persists (p : Nat → Bool) (next : ∀ n, p n = true → p (n+1) = true)
    {start : Nat} (atStart : p start = true) : ∀ n, start ≤ n → p n = true := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hs : start = 0 := by omega
    simpa [hs] using atStart
  | succ n ih =>
    intro hn
    by_cases hs : start ≤ n
    · exact next n (ih hs)
    · have hs : start = n+1 := by omega
      simpa [hs] using atStart

/-- This generic scheduler lemma assumes action enabling, not action completion. -/
theorem fair_bit (commands : Nat → Command V T) (p : Nat → Bool) (enabled : Nat → Prop)
    (action : Command V T) (fair : WeakFair commands enabled action)
    (ready : ∃ start, ∀ n, start ≤ n → p n = false → enabled n)
    (sets : ∀ n, commands n = action → enabled n → p (n+1) = true)
    (mono : ∀ n, p n = true → p (n+1) = true) :
    ∃ start, ∀ n, start ≤ n → p n = true := by
  classical
  by_cases done : ∃ n, p n = true
  · obtain ⟨n, hn⟩ := done
    exact ⟨n, persists p mono hn⟩
  · have absent : ∀ n, p n = false := by
      intro n; cases h : p n <;> simp_all
    obtain ⟨start, ready⟩ := ready
    obtain ⟨n, hn, chosen⟩ := fair start (fun n hn => ready n hn (absent n))
    exact False.elim (done ⟨n+1, sets n chosen (ready n hn (absent n))⟩)

/-- All 2f+1 honest-core members alone suffice; the other f may remain silent. -/
theorem core_forms_quorum (c : Config V T R f) (votes : Nat → Bool)
    (all : ∀ w ∈ c.committee.core, votes w = true) : quorum c votes = true := by
  have full : ∀ xs : List Nat, (∀ w ∈ xs, votes w = true) → voteCount xs votes = xs.length := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons w ws ih =>
      intro h
      have hw := h w (by simp)
      have ht := ih (fun u hu => h u (by simp [hu]))
      change (if votes w then 1 else 0) + voteCount ws votes = ws.length + 1
      simp only [hw, ite_true]
      omega
  apply decide_eq_true
  have count := full c.committee.core all
  unfold voteCount at count ⊢
  rw [sumOn_append, count, c.committee.core_size]
  omega

theorem eventually_signature (e : Execution c) (tx : Fin T) (w : Nat)
    (fair : WeakFair e.command (fun n => SignEnabled c (e.state n) tx w) (.sign tx w))
    (admission : ∃ start, ∀ n, start ≤ n →
      (e.state n).signatures tx w = false → SignAllowed c (e.state n) tx w) :
    ∃ start, ∀ n, start ≤ n → (e.state n).signatures tx w = true := by
  apply fair_bit e.command _ _ (.sign tx w) fair
  · obtain ⟨start, allowed⟩ := admission
    exact ⟨start, fun n hn absent => ⟨absent, allowed n hn absent⟩⟩
  · intro n chosen enabled
    have accepted := e.accepted n
    rw [chosen] at accepted
    have result : e.state (n+1) = signed (e.state n) tx w := by
      simpa [perform, enabled.2] using accepted.symm
    simp [result, signed, CBCL.ConsensusFree.two, CBCL.ConsensusFree.setAt]
  · intro n
    exact (step_journals (e.step n)).signatures tx w

/-- Cancellation is excluded by actor authorization, not by trusting Byzantine nodes. -/
theorem no_fence_step (c : Config V T R f) (tx : Fin T) (w : Nat)
    (honest : w ∈ c.committee.core) (noCancel : c.cancelAuthorized tx = false)
    {s t : State V T} (old : s.fences tx w = false) (step : Step c s t) :
    t.fences tx w = false := by
  cases step with
  | fence u v allowed =>
    by_cases ht : tx = u
    · subst u
      by_cases hw : w = v
      · subst v
        have bad := (allowed honest).1
        simp [noCancel] at bad
      · simpa [fenced, CBCL.ConsensusFree.two, CBCL.ConsensusFree.setAt, hw] using old
    · simpa [fenced, CBCL.ConsensusFree.two, CBCL.ConsensusFree.setAt, ht] using old
  | sign => exact old
  | release => exact old
  | effect => exact old
  | record => exact old
  | adopt => exact old
  | replay => exact old

theorem no_honest_fence (e : Execution c) (tx : Fin T) (w : Nat)
    (honest : w ∈ c.committee.core) (noCancel : c.cancelAuthorized tx = false) :
    ∀ n, (e.state n).fences tx w = false := by
  intro n
  induction n with
  | zero => simp [e.starts, initial]
  | succ n ih => exact no_fence_step c tx w honest noCancel ih (e.step n)

theorem eventually_effect (e : Execution c) (tx : Fin T) (w : Nat)
    (honest : w ∈ c.committee.core) (noCancel : c.cancelAuthorized tx = false)
    (fair : WeakFair e.command (fun n => EffectEnabled c (e.state n) tx w) (.effect tx w))
    (operation : ∃ start, ∀ n, start ≤ n → operationCert c (e.state n) tx = true) :
    ∃ start, ∀ n, start ≤ n → (e.state n).effects tx w = true := by
  apply fair_bit e.command _ _ (.effect tx w) fair
  · obtain ⟨start, ready⟩ := operation
    exact ⟨start, fun n hn absent =>
      ⟨absent, ready n hn, no_honest_fence e tx w honest noCancel n⟩⟩
  · intro n chosen enabled
    have accepted := e.accepted n
    rw [chosen] at accepted
    have result : e.state (n+1) = emitted (e.state n) tx w := by
      simp only [perform] at accepted
      split at accepted
      · exact Option.some.inj accepted.symm
      · contradiction
    simp [result, emitted, CBCL.ConsensusFree.two, CBCL.ConsensusFree.setAt]
  · intro n
    exact (step_journals (e.step n)).effects tx w

/-- Conditional liveness for any infinite accepted schedule, including arbitrary
Byzantine steps. Persistent admission is stronger than an adequate global balance.
This proves permanent certificate existence, not client receipt or a time bound. -/
theorem eventual_honest_effects (e : Execution c) (tx : Fin T)
    (noCancel : c.cancelAuthorized tx = false)
    (admission : ∀ w ∈ c.committee.core, ∃ start, ∀ n, start ≤ n →
      (e.state n).signatures tx w = false → SignAllowed c (e.state n) tx w)
    (signFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => SignEnabled c (e.state n) tx w) (.sign tx w))
    (effectFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => EffectEnabled c (e.state n) tx w) (.effect tx w)) :
    ∃ start, ∀ n, start ≤ n → ∀ w ∈ c.committee.core,
      (e.state n).effects tx w = true := by
  obtain ⟨opStart, allSigned⟩ := finite_eventually c.committee.core
    (fun n w => (e.state n).signatures tx w = true)
    (fun w hw => eventually_signature e tx w (signFair w hw) (admission w hw))
  have operation : ∃ start, ∀ n, start ≤ n → operationCert c (e.state n) tx = true :=
    ⟨opStart, fun n hn => core_forms_quorum c _ (allSigned n hn)⟩
  obtain ⟨effectStart, allEffects⟩ := finite_eventually c.committee.core
    (fun n w => (e.state n).effects tx w = true)
    (fun w hw => eventually_effect e tx w hw noCancel (effectFair w hw) operation)
  exact ⟨effectStart, allEffects⟩

/-- Conditional liveness for any infinite accepted schedule, including arbitrary
Byzantine steps. Persistent admission is stronger than an adequate global balance.
This proves permanent certificate existence, not client receipt or a time bound. -/
theorem eventual_finality (e : Execution c) (tx : Fin T)
    (noCancel : c.cancelAuthorized tx = false)
    (admission : ∀ w ∈ c.committee.core, ∃ start, ∀ n, start ≤ n →
      (e.state n).signatures tx w = false → SignAllowed c (e.state n) tx w)
    (signFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => SignEnabled c (e.state n) tx w) (.sign tx w))
    (effectFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => EffectEnabled c (e.state n) tx w) (.effect tx w)) :
    ∃ start, ∀ n, start ≤ n → finalCert c (e.state n) tx = true := by
  obtain ⟨start, allEffects⟩ := eventual_honest_effects e tx noCancel admission signFair effectFair
  exact ⟨start, fun n hn => core_forms_quorum c _ (allEffects n hn)⟩

/-- Reachability invariants for the actual command execution, not an assumed state. -/
theorem Execution.invariant (e : Execution c) : ∀ n, Invariant c (e.state n) := by
  intro n
  induction n with
  | zero => rw [e.starts]; exact initial_invariant c
  | succ n ih => exact step_invariant ih (e.step n)

/-- No forged Byzantine-only quorum can cancel an uncancelled transaction. -/
theorem no_cancel_certificate (e : Execution c) (tx : Fin T)
    (noCancel : c.cancelAuthorized tx = false) (n : Nat) :
    cancelCert c (e.state n) tx = false := by
  have empty : voteCount c.committee.core ((e.state n).fences tx) = 0 := by
    have zero : ∀ xs : List Nat, (∀ w ∈ xs, (e.state n).fences tx w = false) →
        voteCount xs ((e.state n).fences tx) = 0 := by
      intro xs
      induction xs with
      | nil => intro _; rfl
      | cons w ws ih =>
        intro h
        have hw := h w (by simp)
        have ht := ih (fun u hu => h u (by simp [hu]))
        simpa [voteCount, sumOn, hw] using ht
    exact zero _ (fun w hw => no_honest_fence e tx w hw noCancel n)
  cases h : cancelCert c (e.state n) tx with
  | false => rfl
  | true =>
    have covered := quorum_coverage c.committee _ (of_decide_eq_true h)
    rw [empty] at covered
    omega

/-- A concrete sufficient envelope: all candidate debits in this version fit
inside every honest validator's scaled local capacity. This is stricter than
sufficient global balance and permits concurrent work within that envelope. -/
def FitsEnvelope (c : Config V T R f) (v : Version V) : Prop :=
  ∀ d, sumOn (List.finRange T) (fun u =>
    if c.opVersion u = v then (2*f+1)*c.cost u d else 0) ≤ (f+1)*allowance c v d

theorem admission_from_envelope (e : Execution c) (tx : Fin T)
    (authorized : c.authorized tx = true) (noCancel : c.cancelAuthorized tx = false)
    (stable : ∀ n w, w ∈ c.committee.core → (e.state n).active w = c.opVersion tx)
    (budget : FitsEnvelope c (c.opVersion tx)) :
    ∀ w ∈ c.committee.core, ∃ start, ∀ n, start ≤ n →
      (e.state n).signatures tx w = false → SignAllowed c (e.state n) tx w := by
  intro w hw
  refine ⟨0, ?_⟩
  intro n _ _ _
  refine ⟨authorized, stable n w hw, ?_, ?_⟩
  · cases released : (e.state n).released tx w with
    | false => rfl
    | true =>
      have cancel := (e.invariant n).release_cancel tx w hw released
      rw [no_cancel_certificate e tx noCancel n] at cancel
      contradiction
  · intro d
    apply Nat.le_trans _ (budget d)
    apply sumOn_mono
    intro u _
    split <;> split <;> simp_all

/-- Nonvacuous sufficient-condition capstone: fixed local version, authorized
uncancelled work, an explicit arithmetic envelope, and weak action fairness. -/
theorem envelope_eventual_finality (e : Execution c) (tx : Fin T)
    (authorized : c.authorized tx = true) (noCancel : c.cancelAuthorized tx = false)
    (stable : ∀ n w, w ∈ c.committee.core → (e.state n).active w = c.opVersion tx)
    (budget : FitsEnvelope c (c.opVersion tx))
    (signFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => SignEnabled c (e.state n) tx w) (.sign tx w))
    (effectFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => EffectEnabled c (e.state n) tx w) (.effect tx w)) :
    ∃ start, ∀ n, start ≤ n → finalCert c (e.state n) tx = true :=
  eventual_finality e tx noCancel
    (admission_from_envelope e tx authorized noCancel stable budget) signFair effectFair

/-- Client observation is a separate reliable-delivery premise: durable votes
are eventually delivered and retained, not certificates assumed into existence. -/
structure Observer (e : Execution c) (tx : Fin T) where
  seen : Nat → Nat → Bool
  authentic : ∀ n w, seen n w = true → (e.state n).effects tx w = true
  retained : ∀ n w, seen n w = true → seen (n+1) w = true
  delivered : ∀ w, w ∈ c.committee.core → ∀ n,
    (e.state n).effects tx w = true → ∃ m, n ≤ m ∧ seen m w = true

theorem observed_eventual_finality (e : Execution c) (tx : Fin T)
    (observer : Observer e tx)
    (effects : ∀ w ∈ c.committee.core, ∃ start, ∀ n, start ≤ n →
      (e.state n).effects tx w = true) :
    ∃ start, ∀ n, start ≤ n → quorum c (observer.seen n) = true := by
  apply Exists.elim (finite_eventually c.committee.core
    (fun n w => observer.seen n w = true) ?_)
  · intro start ready
    exact ⟨start, fun n hn => core_forms_quorum c _ (ready n hn)⟩
  · intro w hw
    obtain ⟨n, hn⟩ := effects w hw
    obtain ⟨m, _, delivered⟩ := observer.delivered w hw n (hn n (Nat.le_refl n))
    exact ⟨m, persists _ (fun n => observer.retained n w) delivered⟩

/-- Reliable observation of individual honest votes completes the client-facing
liveness statement. Fair scheduling still abstracts requests/operation-QC delivery. -/
theorem client_eventual_finality (e : Execution c) (tx : Fin T) (observer : Observer e tx)
    (noCancel : c.cancelAuthorized tx = false)
    (admission : ∀ w ∈ c.committee.core, ∃ start, ∀ n, start ≤ n →
      (e.state n).signatures tx w = false → SignAllowed c (e.state n) tx w)
    (signFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => SignEnabled c (e.state n) tx w) (.sign tx w))
    (effectFair : ∀ w ∈ c.committee.core,
      WeakFair e.command (fun n => EffectEnabled c (e.state n) tx w) (.effect tx w)) :
    ∃ start, ∀ n, start ≤ n → quorum c (observer.seen n) = true := by
  obtain ⟨start, votes⟩ := eventual_honest_effects e tx noCancel admission signFair effectFair
  exact observed_eventual_finality e tx observer (fun w hw => ⟨start, fun n hn => votes n hn w hw⟩)

theorem observed_certificate_sound (e : Execution c) (tx : Fin T) (observer : Observer e tx)
    (n : Nat) (observed : quorum c (observer.seen n) = true) :
    finalCert c (e.state n) tx = true :=
  quorum_mono c _ _ (fun w hw => observer.authentic n w hw) observed

end CBCL.ConsensusFree.MultiParent.Liveness
