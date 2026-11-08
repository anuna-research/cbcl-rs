import LeanCbcl.StateResourceNative

/-! Native escrow Summary::record, including checked i128/usize operations.
Maps are extensional with native absent-entry default zero; no cast/account
validation or classification premise is hidden in the summary transition. -/
namespace CBCL.StateResourceSummary
open State StateLift CheckpointEvidence StateResource StateResourceNative

/-- A checked cumulative summary of one owner's operation chain. -/
structure Summary where
  /-- The length of the summarized owner chain. -/
  sequence : Nat
  /-- The cumulative credited amount. -/
  credited : Int
  /-- The cumulative debited amount. -/
  debited : Int
  /-- The cumulative transferred rights. -/
  sentRights : String → Int
  /-- The cumulative transferred headroom. -/
  sentHeadroom : String → Int

/-- The empty owner summary. -/
def empty : Summary := ⟨0,0,0,fun _ => 0,fun _ => 0⟩

/-- Apply one fact to a cumulative owner summary. -/
def update (values : String → Int) (recipient : String) (value : Int) : String → Int :=
  fun owner => if owner = recipient then value else values owner

/-- The native transition in the same branch order as Summary::record. -/
def record (summary : Summary) (node : ResourceFact) : Option Summary := do
  if summary.sequence + 1 < 2^64 then
    let next := {summary with sequence := summary.sequence + 1}
    match node.data.kind with
    | .increment =>
      let amount ← checkedAdd summary.credited node.data.amount
      some {next with credited := amount}
    | .decrement =>
      let amount ← checkedAdd summary.debited node.data.amount
      some {next with debited := amount}
    | .transfer =>
      let recipient ← node.data.selected.recipient
      let amount ← checkedAdd (summary.sentRights recipient) node.data.amount
      some {next with sentRights := update summary.sentRights recipient amount}
    | .transferHeadroom =>
      let recipient ← node.data.selected.recipient
      let amount ← checkedAdd (summary.sentHeadroom recipient) node.data.amount
      some {next with sentHeadroom := update summary.sentHeadroom recipient amount}
    | _ => none
  else none

/-- Independent algebraic effect used to interpret a successful native record.
The primitive transition above must prove this effect; it is not assumed. -/
def effect (summary : Summary) (node : ResourceFact) : Summary := {
  sequence := summary.sequence + 1
  credited := summary.credited + if node.data.kind = .increment then node.data.amount else 0
  debited := summary.debited + if node.data.kind = .decrement then node.data.amount else 0
  sentRights := fun recipient => summary.sentRights recipient +
    if node.data.kind = .transfer ∧ node.data.selected.recipient = some recipient then node.data.amount else 0
  sentHeadroom := fun recipient => summary.sentHeadroom recipient +
    if node.data.kind = .transferHeadroom ∧ node.data.selected.recipient = some recipient then node.data.amount else 0 }

theorem update_add (values : String → Int) (recipient : String) (amount : Int) :
    update values recipient (values recipient + amount) =
      fun owner => values owner + if some recipient = some owner then amount else 0 := by
  funext owner
  by_cases equal : owner = recipient
  · subst owner; simp [update]
  · simp [update,equal,Ne.symm equal]

theorem record_refinement (summary out : Summary) (node : ResourceFact)
    (success : record summary node = some out) : out = effect summary node := by
  unfold record at success
  split at success
  · cases kind : node.data.kind <;> simp only [kind] at success
    all_goals try contradiction
    case increment =>
      cases amount : checkedAdd summary.credited node.data.amount with
      | none => simp [amount] at success
      | some value =>
        have same := (checkedAdd_iff _ _ _).mp amount
        have result := Option.some.inj (by simpa [amount] using success)
        rw [← result]
        simp [effect,kind,same.2]
    case decrement =>
      cases amount : checkedAdd summary.debited node.data.amount with
      | none => simp [amount] at success
      | some value =>
        have same := (checkedAdd_iff _ _ _).mp amount
        have result := Option.some.inj (by simpa [amount] using success)
        rw [← result]
        simp [effect,kind,same.2]
    case transfer =>
      cases recipient : node.data.selected.recipient with
      | none => simp [recipient] at success
      | some owner =>
        cases amount : checkedAdd (summary.sentRights owner) node.data.amount with
        | none => simp [recipient,amount] at success
        | some value =>
          have same := (checkedAdd_iff _ _ _).mp amount
          have result := Option.some.inj (by simpa [recipient,amount] using success)
          rw [← result]
          simp [effect,kind,recipient,same.2,update_add]
    case transferHeadroom =>
      cases recipient : node.data.selected.recipient with
      | none => simp [recipient] at success
      | some owner =>
        cases amount : checkedAdd (summary.sentHeadroom owner) node.data.amount with
        | none => simp [recipient,amount] at success
        | some value =>
          have same := (checkedAdd_iff _ _ _).mp amount
          have result := Option.some.inj (by simpa [recipient,amount] using success)
          rw [← result]
          simp [effect,kind,recipient,same.2,update_add]
  · contradiction

/-- Fold checked owner-summary updates over the supplied chain. -/
def run (chain : Facts) (initial : Summary := empty) : Option Summary := chain.foldlM record initial

theorem run_refinement (chain : Facts) (initial out : Summary)
    (success : run chain initial = some out) : out = chain.foldl effect initial := by
  induction chain generalizing initial with
  | nil => exact (Option.some.inj success).symm
  | cons node rest ih =>
    cases first : record initial node with
    | none => simp [run,List.foldlM_cons,first] at success
    | some next =>
      have continued : run rest next = some out := by simpa [run,List.foldlM_cons,first] using success
      have meaning := record_refinement initial next node first
      simpa only [List.foldl_cons,meaning] using ih next continued

theorem effect_sequence (chain : Facts) (initial : Summary) :
    (chain.foldl effect initial).sequence = initial.sequence + chain.length := by
  induction chain generalizing initial with
  | nil => simp
  | cons node rest ih => simpa [effect,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (effect initial node)

/-- Native sequence is exactly owner-chain length, discharging the premise
of sequence-based native tip arbitration once the worklist establishes that
this supplied prefix is the corresponding complete owner chain. -/
theorem native_sequence_is_prefix_length (chain : Facts) (out : Summary)
    (success : run chain empty = some out) : out.sequence = chain.length := by
  rw [run_refinement chain empty out success,effect_sequence]
  simp [empty]

theorem effect_credited (chain : Facts) (initial : Summary) :
    (chain.foldl effect initial).credited = initial.credited +
      (chain.map (fun n => if n.data.kind = .increment then n.data.amount else 0)).sum := by
  induction chain generalizing initial with
  | nil => simp
  | cons node rest ih => simpa [effect,Int.add_assoc] using ih (effect initial node)

theorem effect_debited (chain : Facts) (initial : Summary) :
    (chain.foldl effect initial).debited = initial.debited +
      (chain.map (fun n => if n.data.kind = .decrement then n.data.amount else 0)).sum := by
  induction chain generalizing initial with
  | nil => simp
  | cons node rest ih => simpa [effect,Int.add_assoc] using ih (effect initial node)

theorem effect_sentRights (chain : Facts) (initial : Summary) (recipient : String) :
    (chain.foldl effect initial).sentRights recipient = initial.sentRights recipient +
      (chain.map (fun n => if n.data.kind = .transfer ∧ n.data.selected.recipient = some recipient
        then n.data.amount else 0)).sum := by
  induction chain generalizing initial with
  | nil => simp
  | cons node rest ih => simpa [effect,Int.add_assoc] using ih (effect initial node)

theorem effect_sentHeadroom (chain : Facts) (initial : Summary) (recipient : String) :
    (chain.foldl effect initial).sentHeadroom recipient = initial.sentHeadroom recipient +
      (chain.map (fun n => if n.data.kind = .transferHeadroom ∧ n.data.selected.recipient = some recipient
        then n.data.amount else 0)).sum := by
  induction chain generalizing initial with
  | nil => simp
  | cons node rest ih => simpa [effect,Int.add_assoc] using ih (effect initial node)

/-- Every successful native prefix fold has the exact cumulative counters and
per-recipient transfer maps used by cone arithmetic. -/
theorem native_counters_refinement (chain : Facts) (out : Summary) (success : run chain empty = some out) :
    out.credited = (chain.map (fun n => if n.data.kind = .increment then n.data.amount else 0)).sum ∧
    out.debited = (chain.map (fun n => if n.data.kind = .decrement then n.data.amount else 0)).sum ∧
    ∀ recipient,
      out.sentRights recipient = (chain.map (fun n => if n.data.kind = .transfer ∧ n.data.selected.recipient = some recipient
        then n.data.amount else 0)).sum ∧
      out.sentHeadroom recipient = (chain.map (fun n => if n.data.kind = .transferHeadroom ∧ n.data.selected.recipient = some recipient
        then n.data.amount else 0)).sum := by
  rw [run_refinement chain empty out success]
  simp [effect_credited,effect_debited,effect_sentRights,effect_sentHeadroom,empty]

end CBCL.StateResourceSummary
