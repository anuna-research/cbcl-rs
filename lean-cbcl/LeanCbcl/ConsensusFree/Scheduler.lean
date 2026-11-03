import LeanCbcl.ConsensusFree.Liveness

/-! A concrete FIFO retry queue and executable round-robin dispatcher.
Each completed worker tick tries the head, then puts it behind the queued work
and finite new arrivals. A disabled head does not block the next job. Fairness
is proved from this algorithm, not assumed. This is a reference model, not a
Rust scheduler or network/OS refinement. -/
namespace CBCL.ConsensusFree.MultiParent.Liveness.Scheduler
open CBCL.ValidatorBudget
variable {V T R f : Nat}

/-- Retry the serviced head at the tail, behind finite new arrivals. -/
def advance (pending arrivals : List α) : List α :=
  match pending with
  | [] => arrivals
  | head :: rest => rest ++ arrivals ++ [head]

/-- A FIFO retry queue with finite arrivals at each completed worker tick. -/
structure QueueTrace (α : Type) where
  /-- Retained jobs awaiting service at each worker tick. -/
  pending : Nat → List α
  /-- Finite new jobs appended at each worker tick. -/
  arrivals : Nat → List α
  next : ∀ n, pending (n+1) = advance (pending n) (arrivals n)

/-- Finite arrivals cannot overtake an already queued occurrence. -/
theorem position_serviced (q : QueueTrace α) (start : Nat) (before suffix : List α) (job : α)
    (position : q.pending start = before ++ job :: suffix) :
    (q.pending (start + before.length)).head? = some job := by
  induction before generalizing start suffix with
  | nil => simp [position]
  | cons head rest ih =>
    have next : q.pending (start+1) = rest ++ job :: (suffix ++ q.arrivals start ++ [head]) := by
      rw [q.next, position]
      simp [advance, List.append_assoc]
    have result := ih (start+1) (suffix ++ q.arrivals start ++ [head]) next
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem retained_next (q : QueueTrace α) (n : Nat) (job : α)
    (present : job ∈ q.pending n) : job ∈ q.pending (n+1) := by
  rw [q.next]
  cases h : q.pending n with
  | nil => simp [h] at present
  | cons head rest =>
    simp only [h, List.mem_cons] at present
    simp only [advance, List.mem_append, List.mem_singleton]
    rcases present with rfl | tail
    · exact Or.inr rfl
    · exact Or.inl (Or.inl tail)

theorem retained (q : QueueTrace α) (job : α) {start : Nat}
    (present : job ∈ q.pending start) : ∀ n, start ≤ n → job ∈ q.pending n := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hs : start = 0 := by omega
    simpa [hs] using present
  | succ n ih =>
    intro hn
    by_cases hs : start ≤ n
    · exact retained_next q n job (ih hs)
    · have hs : start = n+1 := by omega
      simpa [hs] using present

theorem arrival_admitted (q : QueueTrace α) (n : Nat) (job : α)
    (arrived : job ∈ q.arrivals n) : job ∈ q.pending (n+1) := by
  rw [q.next]
  cases q.pending n <;> simp_all [advance]

/-- Every admitted job is tried again on every suffix, even with unbounded total
arrivals, provided each individual worker tick and arrival list is finite. -/
theorem admitted_revisited (q : QueueTrace α) (job : α)
    (admitted : ∃ n, job ∈ q.pending n) (start : Nat) :
    ∃ n, start ≤ n ∧ (q.pending n).head? = some job := by
  obtain ⟨entered, present⟩ := admitted
  have present := retained q job present (max start entered) (by omega)
  obtain ⟨before, suffix, position⟩ := List.append_of_mem present
  refine ⟨max start entered + before.length, by omega, ?_⟩
  exact position_serviced q _ before suffix job position

variable (c : Config V T R f)

/-- Muted work represents a non-cooperating handler. The algorithm does not know
which committee members are honest. Disabled/empty/muted work emits replay. -/
def select (serve : Command V T → Bool) (s : State V T) (candidate : Option (Command V T)) : Command V T :=
  match candidate with
  | none => .replay
  | some job => if serve job then
      match perform c s job with
      | some _ => job
      | none => .replay
    else .replay

/-- Protocol state paired with its concrete pending command queue. -/
structure Machine (V T : Nat) where
  /-- Current protocol state serviced by the dispatcher. -/
  protocol : State V T
  /-- Retained commands in FIFO retry order. -/
  pending : List (Command V T)

/-- Service one eligible head command, then rotate the queue with new arrivals. -/
def tick (serve : Command V T → Bool) (arrivals : List (Command V T)) (s : Machine V T) : Machine V T where
  protocol := (perform c s.protocol (select c serve s.protocol s.pending.head?)).getD s.protocol
  pending := advance s.pending arrivals

/-- Deterministic reference scheduler; ticks are local-service interleavings,
not consensus/ledger decisions. The clock counts completed worker turns. -/
def run (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) : Nat → Machine V T
  | 0 => ⟨initial, initialQueue⟩
  | n+1 => tick c serve (arrivals n) (run serve initialQueue arrivals n)

theorem select_accepted (serve : Command V T → Bool) (s : State V T)
    (candidate : Option (Command V T)) :
    ∃ t, perform c s (select c serve s candidate) = some t := by
  cases candidate with
  | none => exact ⟨s, rfl⟩
  | some job =>
    simp only [select]
    split
    · cases result : perform c s job with
      | none => exact ⟨s, rfl⟩
      | some t => exact ⟨t, result⟩
    · exact ⟨s, rfl⟩

/-- Project the concrete dispatcher run into an initialized protocol execution. -/
def execution (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) : Execution c where
  state n := (run c serve initialQueue arrivals n).protocol
  command n := select c serve (run c serve initialQueue arrivals n).protocol
    (run c serve initialQueue arrivals n).pending.head?
  starts := rfl
  accepted := by
    intro n
    obtain ⟨t, accepted⟩ := select_accepted c serve (run c serve initialQueue arrivals n).protocol
      (run c serve initialQueue arrivals n).pending.head?
    simp only [run, tick, accepted, Option.getD_some]

/-- Project the dispatcher run into its FIFO queue trace. -/
def queues (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) : QueueTrace (Command V T) where
  pending n := (run c serve initialQueue arrivals n).pending
  arrivals := arrivals
  next _ := rfl

/-- At a serviced slot, an unmuted valid command actually executes. -/
theorem select_executes (serve : Command V T → Bool) (s : State V T) (job : Command V T)
    (unmuted : serve job = true) (accepted : ∃ t, perform c s job = some t) :
    select c serve s (some job) = job := by
  obtain ⟨t, ht⟩ := accepted
  simp [select, unmuted, ht]

/-- The actual dispatcher satisfies weak fairness for every retained, admitted,
unmuted action whose enabled predicate entails the existing perform guard. -/
theorem scheduler_fair (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) (job : Command V T) (enabled : Nat → Prop)
    (admitted : ∃ n, job ∈ (queues c serve initialQueue arrivals).pending n)
    (unmuted : serve job = true)
    (valid : ∀ n, enabled n → ∃ t, perform c ((execution c serve initialQueue arrivals).state n) job = some t) :
    WeakFair (execution c serve initialQueue arrivals).command enabled job := by
  intro start continuous
  obtain ⟨n, hn, head⟩ := admitted_revisited (queues c serve initialQueue arrivals) job admitted start
  refine ⟨n, hn, ?_⟩
  change select c serve (run c serve initialQueue arrivals n).protocol
    (run c serve initialQueue arrivals n).pending.head? = job
  change (run c serve initialQueue arrivals n).pending.head? = some job at head
  rw [head]
  exact select_executes c serve _ job unmuted (valid n (continuous n hn))

/-- Queue admission and an honest responsive handler are explicit environmental
premises. No fair-scheduling or eventual-certificate field appears here. -/
structure HonestJobs (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) (tx : Fin T) : Prop where
  signQueued : ∀ w ∈ c.committee.core,
    ∃ n, .sign tx w ∈ (queues c serve initialQueue arrivals).pending n
  effectQueued : ∀ w ∈ c.committee.core,
    ∃ n, .effect tx w ∈ (queues c serve initialQueue arrivals).pending n
  signUnmuted : ∀ w ∈ c.committee.core, serve (.sign tx w) = true
  effectUnmuted : ∀ w ∈ c.committee.core, serve (.effect tx w) = true

theorem sign_fair (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) (tx : Fin T) (w : Nat)
    (admitted : ∃ n, .sign tx w ∈ (queues c serve initialQueue arrivals).pending n)
    (unmuted : serve (.sign tx w) = true) :
    WeakFair (execution c serve initialQueue arrivals).command
      (fun n => SignEnabled c ((execution c serve initialQueue arrivals).state n) tx w) (.sign tx w) := by
  apply scheduler_fair c serve initialQueue arrivals (.sign tx w) _ admitted unmuted
  intro n enabled
  refine ⟨signed ((execution c serve initialQueue arrivals).state n) tx w, ?_⟩
  simp only [perform]
  rw [if_pos enabled.2]

theorem effect_fair (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) (tx : Fin T) (w : Nat)
    (admitted : ∃ n, .effect tx w ∈ (queues c serve initialQueue arrivals).pending n)
    (unmuted : serve (.effect tx w) = true) :
    WeakFair (execution c serve initialQueue arrivals).command
      (fun n => EffectEnabled c ((execution c serve initialQueue arrivals).state n) tx w) (.effect tx w) := by
  apply scheduler_fair c serve initialQueue arrivals (.effect tx w) _ admitted unmuted
  intro n enabled
  refine ⟨emitted ((execution c serve initialQueue arrivals).state n) tx w, ?_⟩
  simp only [perform]
  rw [if_pos (fun _ => enabled.2)]

/-- Concrete-scheduler liveness: fairness is a theorem about the dispatcher.
The remaining premises concern admission, honesty, enrollment and cancellation. -/
theorem scheduled_finality (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) (tx : Fin T)
    (jobs : HonestJobs c serve initialQueue arrivals tx)
    (noCancel : c.cancelAuthorized tx = false)
    (admission : ∀ w ∈ c.committee.core, ∃ start, ∀ n, start ≤ n →
      ((execution c serve initialQueue arrivals).state n).signatures tx w = false →
      SignAllowed c ((execution c serve initialQueue arrivals).state n) tx w) :
    ∃ start, ∀ n, start ≤ n → finalCert c ((execution c serve initialQueue arrivals).state n) tx = true :=
  eventual_finality (execution c serve initialQueue arrivals) tx noCancel admission
    (fun w hw => sign_fair c serve initialQueue arrivals tx w (jobs.signQueued w hw) (jobs.signUnmuted w hw))
    (fun w hw => effect_fair c serve initialQueue arrivals tx w (jobs.effectQueued w hw) (jobs.effectUnmuted w hw))

/-- Fully concrete sufficient-condition capstone: arithmetic capacity and fixed
honest local versions imply admission; the queue algorithm supplies fairness. -/
theorem scheduled_envelope_finality (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) (tx : Fin T)
    (jobs : HonestJobs c serve initialQueue arrivals tx)
    (authorized : c.authorized tx = true) (noCancel : c.cancelAuthorized tx = false)
    (stable : ∀ n w, w ∈ c.committee.core →
      ((execution c serve initialQueue arrivals).state n).active w = c.opVersion tx)
    (budget : FitsEnvelope c (c.opVersion tx)) :
    ∃ start, ∀ n, start ≤ n → finalCert c ((execution c serve initialQueue arrivals).state n) tx = true :=
  scheduled_finality c serve initialQueue arrivals tx jobs noCancel
    (admission_from_envelope (execution c serve initialQueue arrivals) tx authorized noCancel stable budget)

/-- Reliable delivery of individual effects votes extends the concrete worker
result to client receipt. Neither protocol fairness premise is assumed. -/
theorem scheduled_client_finality (serve : Command V T → Bool) (initialQueue : List (Command V T))
    (arrivals : Nat → List (Command V T)) (tx : Fin T)
    (jobs : HonestJobs c serve initialQueue arrivals tx)
    (observer : Observer (execution c serve initialQueue arrivals) tx)
    (noCancel : c.cancelAuthorized tx = false)
    (admission : ∀ w ∈ c.committee.core, ∃ start, ∀ n, start ≤ n →
      ((execution c serve initialQueue arrivals).state n).signatures tx w = false →
      SignAllowed c ((execution c serve initialQueue arrivals).state n) tx w) :
    ∃ start, ∀ n, start ≤ n → quorum c (observer.seen n) = true :=
  client_eventual_finality (execution c serve initialQueue arrivals) tx observer noCancel admission
    (fun w hw => sign_fair c serve initialQueue arrivals tx w (jobs.signQueued w hw) (jobs.signUnmuted w hw))
    (fun w hw => effect_fair c serve initialQueue arrivals tx w (jobs.effectQueued w hw) (jobs.effectUnmuted w hw))

end CBCL.ConsensusFree.MultiParent.Liveness.Scheduler
