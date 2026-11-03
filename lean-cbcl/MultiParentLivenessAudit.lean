import LeanCbcl.ConsensusFree.Scheduler

/-! Kernel-checked witnesses and countermodels for conditional liveness. -/
namespace CBCL.ConsensusFree.MultiParent.Liveness.Audit
open CBCL.ValidatorBudget
set_option maxRecDepth 10000

private def committee : Committee 1 where
  core := [0,1,2]
  others := [3]
  distinct := by decide
  core_size := by decide
  other_size := by decide

/-- A static genesis pool of 3, one authorized transaction, no cancellation. -/
def pool (cost : Nat) : Config 0 1 1 1 where
  graph := ⟨fun _ => []⟩
  committee := committee
  manifest := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => 0, true⟩
  initial := fun _ => 3
  opVersion := fun _ => 0
  cost := fun _ _ => cost
  credit := fun _ _ => 0
  authorized := fun _ => true
  cancelAuthorized := fun _ => false
  disjoint := by intros; exact Or.inr rfl

/-- At f=1, 3*2 ≤ 2*3: a nonempty, concrete sufficient funding envelope. -/
example : FitsEnvelope (pool 2) 0 := by unfold FitsEnvelope; decide
example : SignAllowed (pool 2) initial 0 0 := by decide
/-- A globally affordable full-balance spend still fails local admission. -/
example : (pool 3).cost 0 0 ≤ (pool 3).initial 0 := by decide
example : ¬ SignAllowed (pool 3) initial 0 0 := by decide

/-- No Byzantine vote at all: honest members alone finish the two voting phases. -/
def goodScript : List (Command 0 1) :=
  [.sign 0 0, .sign 0 1, .sign 0 2, .effect 0 0, .effect 0 1, .effect 0 2]

def goodState (n : Nat) : State 0 1 :=
  (execute (pool 2) initial (goodScript.take (min n 6))).getD initial

def goodCommand (n : Nat) : Command 0 1 :=
  if n < 6 then (goodScript[n]?).getD .replay else .replay

def good : Execution (pool 2) where
  state := goodState
  command := goodCommand
  starts := rfl
  accepted := by
    intro n
    have casesN : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
    rcases casesN with rfl | rfl | rfl | rfl | rfl | rfl | hn
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [goodState, goodCommand, Nat.min_eq_right hn,
        Nat.min_eq_right (show 6 ≤ n+1 by omega), show ¬n < 6 by omega, perform]

/-- Outstanding work that is eventually completed is not continuously enabled. -/
theorem fair_when_disabled (commands : Nat → Command V T) (enabled : Nat → Prop)
    (action : Command V T) (disabled : ∃ start, ∀ n, start ≤ n → ¬enabled n) :
    WeakFair commands enabled action := by
  intro start continuous
  obtain ⟨cutoff, gone⟩ := disabled
  exact False.elim (gone (max start cutoff) (by omega) (continuous _ (by omega)))

theorem good_bits (n : Nat) (hn : 6 ≤ n) (w : Nat) (hw : w ∈ committee.core) :
    (good.state n).signatures 0 w = true ∧ (good.state n).effects 0 w = true := by
  have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [committee] using hw
  rcases members with rfl | rfl | rfl
  all_goals simp only [good, goodState, Nat.min_eq_right hn]; decide

theorem good_sign_fair (w : Nat) (hw : w ∈ (pool 2).committee.core) :
    WeakFair good.command (fun n => SignEnabled (pool 2) (good.state n) 0 w) (.sign 0 w) := by
  apply fair_when_disabled
  refine ⟨6, ?_⟩
  intro n hn enabled
  have bit := (good_bits n hn w hw).1
  simp [SignEnabled, bit] at enabled

theorem good_effect_fair (w : Nat) (hw : w ∈ (pool 2).committee.core) :
    WeakFair good.command (fun n => EffectEnabled (pool 2) (good.state n) 0 w) (.effect 0 w) := by
  apply fair_when_disabled
  refine ⟨6, ?_⟩
  intro n hn enabled
  have bit := (good_bits n hn w hw).2
  simp [EffectEnabled, bit] at enabled

theorem good_stable : ∀ n w, w ∈ (pool 2).committee.core → (good.state n).active w = (pool 2).opVersion 0 := by
  intros; exact Fin.ext (by omega)

/-- The parametric liveness theorem applies to an actual nonvacuous infinite run. -/
theorem good_finalizes : ∃ start, ∀ n, start ≤ n → finalCert (pool 2) (good.state n) 0 = true :=
  envelope_eventual_finality good 0 (by decide) (by decide) good_stable
    (by unfold FitsEnvelope; decide) good_sign_fair good_effect_fair

/-- A permanently quiet execution is accepted by the safety model. -/
def quiet (cost : Nat) : Execution (pool cost) where
  state := fun _ => initial
  command := fun _ => .replay
  starts := rfl
  accepted := fun _ => rfl

/-- Without scheduling fairness, even admissible funded work never finalizes. -/
example : ∀ n, finalCert (pool 2) ((quiet 2).state n) 0 = false := by intro _; change finalCert _ initial _ = false; decide
example : ¬ WeakFair (quiet 2).command
    (fun n => SignEnabled (pool 2) ((quiet 2).state n) 0 0) (.sign 0 0) := by
  intro fair
  obtain ⟨n, _, bad⟩ := fair 0 (by intros; change SignEnabled (pool 2) initial 0 0; unfold SignEnabled; decide)
  cases bad

/-- Global funds plus fairness do not imply admission: all honest signing guards
reject the full-balance debit, so a fair scheduler can legitimately do nothing. -/
theorem blocked_sign_fair (w : Nat) (hw : w ∈ (pool 3).committee.core) :
    WeakFair (quiet 3).command
      (fun n => SignEnabled (pool 3) ((quiet 3).state n) 0 w) (.sign 0 w) := by
  apply fair_when_disabled
  refine ⟨0, ?_⟩
  intro n _ enabled
  have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
  have impossible : ¬ SignAllowed (pool 3) initial 0 w := by
    rcases members with rfl | rfl | rfl <;> decide
  exact impossible enabled.2

theorem blocked_effect_fair (w : Nat) :
    WeakFair (quiet 3).command
      (fun n => EffectEnabled (pool 3) ((quiet 3).state n) 0 w) (.effect 0 w) := by
  apply fair_when_disabled
  refine ⟨0, ?_⟩
  intro n _ enabled
  have noQC : operationCert (pool 3) initial 0 = false := by decide
  have qc := enabled.2.1
  rw [show (quiet 3).state n = initial from rfl, noQC] at qc
  contradiction

example : ∀ n, finalCert (pool 3) ((quiet 3).state n) 0 = false := by intro _; change finalCert _ initial _ = false; decide

/-- Two individually affordable requests over-subscribe a pool of three. -/
def contested : Config 0 2 1 1 where
  graph := ⟨fun _ => []⟩
  committee := committee
  manifest := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => 0, true⟩
  initial := fun _ => 3
  opVersion := fun _ => 0
  cost := fun _ _ => 2
  credit := fun _ _ => 0
  authorized := fun _ => true
  cancelAuthorized := fun _ => false
  disjoint := by intros; exact Or.inr rfl

def contestedScript : List (Command 0 2) := [.sign 0 0, .sign 0 1, .sign 1 2]
def contestedState (n : Nat) : State 0 2 :=
  (execute contested initial (contestedScript.take (min n 3))).getD initial
def contestedCommand (n : Nat) : Command 0 2 :=
  if n < 3 then (contestedScript[n]?).getD .replay else .replay

def deadlocked : Execution contested where
  state := contestedState
  command := contestedCommand
  starts := rfl
  accepted := by
    intro n
    have casesN : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
    rcases casesN with rfl | rfl | rfl | hn
    · rfl
    · rfl
    · rfl
    · simp [contestedState, contestedCommand, Nat.min_eq_right hn,
        Nat.min_eq_right (show 3 ≤ n+1 by omega), show ¬n < 3 by omega, perform]

/-- Both transactions pass every honest guard when considered at genesis. -/
example : ∀ tx : Fin 2, ∀ w : Fin 3, SignAllowed contested initial tx w.val := by decide

/-- After a split reservation, no honest signing action remains enabled. -/
theorem contested_no_sign (tx : Fin 2) (w : Nat) (hw : w ∈ contested.committee.core)
    (n : Nat) (hn : 3 ≤ n) : ¬ SignEnabled contested (deadlocked.state n) tx w := by
  have checked : ∀ t : Fin 2, ∀ v : Fin 3,
      ¬SignEnabled contested (contestedState 3) t v.val := by
    unfold SignEnabled
    decide
  have bound : w < 3 := by
    have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [contested, committee] using hw
    omega
  simpa only [deadlocked, contestedState, Nat.min_eq_right hn] using checked tx ⟨w,bound⟩

theorem contested_no_operation (tx : Fin 2) (n : Nat) (hn : 3 ≤ n) :
    operationCert contested (deadlocked.state n) tx = false := by
  have checked : ∀ t : Fin 2, operationCert contested (contestedState 3) t = false := by decide
  simpa only [deadlocked, contestedState, Nat.min_eq_right hn] using checked tx

/-- Every honest target-sign action is weakly fair despite the permanent stall. -/
theorem contested_sign_fair (tx : Fin 2) (w : Nat) (hw : w ∈ contested.committee.core) :
    WeakFair deadlocked.command
      (fun n => SignEnabled contested (deadlocked.state n) tx w) (.sign tx w) :=
  fair_when_disabled _ _ _ ⟨3, fun n hn => contested_no_sign tx w hw n hn⟩

theorem contested_effect_fair (tx : Fin 2) (w : Nat) :
    WeakFair deadlocked.command
      (fun n => EffectEnabled contested (deadlocked.state n) tx w) (.effect tx w) := by
  apply fair_when_disabled
  refine ⟨3, ?_⟩
  intro n hn enabled
  have qc := enabled.2.1
  rw [contested_no_operation tx n hn] at qc
  contradiction

/-- Neither transaction ever finalizes in this accepted infinite execution. -/
theorem contested_never_finalizes (tx : Fin 2) (n : Nat) :
    finalCert contested (deadlocked.state n) tx = false := by
  have casesN : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
  have early : ∀ t : Fin 2, ∀ k : Fin 4,
      finalCert contested (contestedState k.val) t = false := by decide
  rcases casesN with rfl | rfl | rfl | hn
  · exact early tx 0
  · exact early tx 1
  · exact early tx 2
  · simpa only [deadlocked, contestedState, Nat.min_eq_right hn] using early tx 3

/-- A concrete observer delayed by seven abstract steps; receipt is not immediate. -/
def delayedObserver : Observer good 0 where
  seen := fun n w => (good.state (n-7)).effects 0 w
  authentic := by
    intro n w seen
    exact persists _ (fun k => (step_journals (good.step k)).effects 0 w) seen n (by omega)
  retained := by
    intro n w seen
    exact persists _ (fun k => (step_journals (good.step k)).effects 0 w) seen ((n+1)-7) (by omega)
  delivered := by
    intro w _ n bit
    exact ⟨n+7, by omega, by simpa using bit⟩

theorem good_client_finalizes :
    ∃ start, ∀ n, start ≤ n → quorum (pool 2) (delayedObserver.seen n) = true :=
  client_eventual_finality good 0 delayedObserver (by decide)
    (admission_from_envelope good 0 (by decide) (by decide) good_stable
      (by unfold FitsEnvelope; decide)) good_sign_fair good_effect_fair

/-- Individually affordable requests can both stall under fair honest target
scheduling; a balance/fairness-only unconditional liveness theorem is false. -/
theorem contention_can_stall_fairly :
    ∃ e : Execution contested,
      (∀ tx w, w ∈ contested.committee.core →
        WeakFair e.command (fun n => SignEnabled contested (e.state n) tx w) (.sign tx w) ∧
        WeakFair e.command (fun n => EffectEnabled contested (e.state n) tx w) (.effect tx w)) ∧
      (∀ n tx, finalCert contested (e.state n) tx = false) :=
  ⟨deadlocked, fun tx w hw => ⟨contested_sign_fair tx w hw, contested_effect_fair tx w⟩,
    fun n tx => contested_never_finalizes tx n⟩

/-! Concrete retry scheduling: blocked effects work precedes reservation work,
and validator 3 never cooperates. No fairness hypothesis is supplied below. -/
def retryJobs : List (Command 0 1) :=
  [.effect 0 0, .sign 0 0, .effect 0 1, .sign 0 1,
   .effect 0 2, .sign 0 2, .sign 0 3, .effect 0 3]

def retryServe : Command 0 1 → Bool
  | .sign _ w | .effect _ w => decide (w ≠ 3)
  | _ => true

def retry : Execution (pool 2) := Scheduler.execution (pool 2) retryServe retryJobs (fun _ => [])

theorem retry_jobs : Scheduler.HonestJobs (pool 2) retryServe retryJobs (fun _ => []) 0 := by
  constructor
  · intro w hw
    have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
    rcases members with rfl | rfl | rfl <;> exact ⟨0, by simp [Scheduler.queues, Scheduler.run, retryJobs]⟩
  · intro w hw
    have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
    rcases members with rfl | rfl | rfl <;> exact ⟨0, by simp [Scheduler.queues, Scheduler.run, retryJobs]⟩
  · intro w hw
    have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
    rcases members with rfl | rfl | rfl <;> rfl
  · intro w hw
    have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
    rcases members with rfl | rfl | rfl <;> rfl

/-- A blocked head is skipped, and the next reservation job gets a turn. -/
example : retry.command 0 = .replay := rfl
example : retry.command 1 = .sign 0 0 := rfl
example : retryServe (.sign 0 3) = false ∧ retryServe (.effect 0 3) = false := by decide
example : finalCert (pool 2) (retry.state 13) 0 = true := by decide
example : (retry.state 13).signatures 0 3 = false ∧ (retry.state 13).effects 0 3 = false := by decide

theorem retry_stable : ∀ n w, w ∈ (pool 2).committee.core →
    (retry.state n).active w = (pool 2).opVersion 0 := by
  intros; exact Fin.ext (by omega)

/-- Main connection: concrete queue, actual dispatcher, arithmetic admission;
there is no signFair/effectFair assumption on this theorem. -/
theorem retry_eventually_finalizes :
    ∃ start, ∀ n, start ≤ n → finalCert (pool 2) (retry.state n) 0 = true :=
  Scheduler.scheduled_envelope_finality (pool 2) retryServe retryJobs (fun _ => []) 0
    retry_jobs (by decide) (by decide) retry_stable (by unfold FitsEnvelope; decide)

/-- Growing queues and duplicate arrivals still cannot overtake queued jobs. -/
def noisyPending : Nat → List Nat
  | 0 => [7,8]
  | n+1 => Scheduler.advance (noisyPending n) [9,9,9]

def noisyQueue : Scheduler.QueueTrace Nat where
  pending := noisyPending
  arrivals := fun _ => [9,9,9]
  next _ := rfl

example : noisyPending 1 = [8,9,9,9,7] := rfl
example : ∀ start, ∃ n, start ≤ n ∧ (noisyQueue.pending n).head? = some 7 :=
  fun start => Scheduler.admitted_revisited noisyQueue 7 ⟨0, by decide⟩ start
example : ∀ n, 9 ∈ noisyQueue.pending (n+1) :=
  fun n => Scheduler.arrival_admitted noisyQueue n 9 (by change 9 ∈ [9,9,9]; decide)

/-- Requests can arrive after startup, amid an unending stream of Byzantine fence
jobs. Each tick still has only a finite list of newly admitted work. -/
def floodedArrivals (n : Nat) : List (Command 0 1) :=
  if n = 5 then retryJobs ++ [.fence 0 3] else [.fence 0 3]

def flooded : Execution (pool 2) :=
  Scheduler.execution (pool 2) retryServe [] floodedArrivals

theorem flooded_jobs : Scheduler.HonestJobs (pool 2) retryServe [] floodedArrivals 0 := by
  constructor
  · intro w hw
    have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
    refine ⟨6, ?_⟩
    apply Scheduler.arrival_admitted (Scheduler.queues (pool 2) retryServe [] floodedArrivals) 5
    rcases members with rfl | rfl | rfl <;> simp [Scheduler.queues, floodedArrivals, retryJobs]
  · intro w hw
    have members : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [pool, committee] using hw
    refine ⟨6, ?_⟩
    apply Scheduler.arrival_admitted (Scheduler.queues (pool 2) retryServe [] floodedArrivals) 5
    rcases members with rfl | rfl | rfl <;> simp [Scheduler.queues, floodedArrivals, retryJobs]
  · exact retry_jobs.signUnmuted
  · exact retry_jobs.effectUnmuted

theorem flooded_stable : ∀ n w, w ∈ (pool 2).committee.core →
    (flooded.state n).active w = (pool 2).opVersion 0 := by
  intros; exact Fin.ext (by omega)

theorem flooded_eventually_finalizes :
    ∃ start, ∀ n, start ≤ n → finalCert (pool 2) (flooded.state n) 0 = true :=
  Scheduler.scheduled_envelope_finality (pool 2) retryServe [] floodedArrivals 0
    flooded_jobs (by decide) (by decide) flooded_stable (by unfold FitsEnvelope; decide)

/-- An actual delayed observer for the computed reference scheduler. -/
def retryObserver : Observer retry 0 where
  seen := fun n w => (retry.state (n-7)).effects 0 w
  authentic := by
    intro n w seen
    exact persists _ (fun k => (step_journals (retry.step k)).effects 0 w) seen n (by omega)
  retained := by
    intro n w seen
    exact persists _ (fun k => (step_journals (retry.step k)).effects 0 w) seen ((n+1)-7) (by omega)
  delivered := by
    intro w _ n bit
    exact ⟨n+7, by omega, by simpa using bit⟩

theorem retry_client_finalizes :
    ∃ start, ∀ n, start ≤ n → quorum (pool 2) (retryObserver.seen n) = true :=
  Scheduler.scheduled_client_finality (pool 2) retryServe retryJobs (fun _ => []) 0
    retry_jobs retryObserver (by decide)
    (admission_from_envelope retry 0 (by decide) (by decide) retry_stable
      (by unfold FitsEnvelope; decide))

#print axioms flooded_eventually_finalizes
#print axioms retry_client_finalizes

#print axioms Scheduler.position_serviced
#print axioms Scheduler.scheduler_fair
#print axioms Scheduler.scheduled_finality
#print axioms Scheduler.scheduled_envelope_finality
#print axioms Scheduler.scheduled_client_finality
#print axioms retry_eventually_finalizes

#print axioms eventual_finality
#print axioms envelope_eventual_finality
#print axioms client_eventual_finality
#print axioms observed_certificate_sound
#print axioms good_finalizes
#print axioms blocked_sign_fair
#print axioms contested_never_finalizes
#print axioms contested_sign_fair
#print axioms good_client_finalizes
#print axioms contention_can_stall_fairly
end CBCL.ConsensusFree.MultiParent.Liveness.Audit
