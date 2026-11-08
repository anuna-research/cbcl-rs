import LeanCbcl.StateObservationPlan

namespace CBCL.StateResourceTests
open State StateLift CheckpointEvidence StateResource

def config : ResourceConfig := {
  ownership := .account, certification := .legacy, floor := 0, ceiling := none,
  initialVerb := "open", initialKey := "allocations", headroomKey := none, issuerRole := "issuer",
  increment := ⟨"mint","amount",none⟩, decrement := ⟨"burn","amount",none⟩,
  transfer := some ⟨"pay","amount",some "recipient"⟩, transferHeadroom := none }

def root : ResourceFact := ⟨1,{
  signer := "treasury",kind := .castRoot,amount := 0,prev := none,deps := [],
  selected := { resource := "coins",bindings := .value [
    ⟨"issuer",["treasury"]⟩,⟨"holder",["treasury","alice","bob"]⟩] } }⟩

def opener : ResourceFact := ⟨2,{
  signer := "treasury",kind := .initialize,amount := 0,prev := none,deps := [],
  selected := {
    resource := "coins",verb := "open",predecessors := [1],
    initialAllocations := .value [("treasury",1000),("alice",0),("bob",0)] } }⟩

def burn : ResourceFact := ⟨3,{
  signer := "alice",kind := .decrement,amount := 1,prev := some 2,deps := [],
  selected := {
    resource := "coins",verb := "burn",predecessors := [2],
    authenticatedFrom := .value "alice",amountStatus := .recognized,
    previousStatus := .recognized,dependenciesStatus := .recognized } }⟩

theorem checked_overflow : checkedAdd (2^127 - 1) 1 = none := by decide

theorem checked_underflow : checkedSub (-(2^127)) 1 = none := by decide

theorem insufficient_budget : localBudget opener burn [burn] false = some 0 := by
  simp [localBudget,ownTotal,ordered,burn,opener,accounts,allocation,checkedSum,checkedAdd,checkedSub,checked,List.lookup]

theorem valid_opener : validInitial config opener root := by
  simp [validInitial,validAccounts,config,opener,root,bindings,members,issuers,accounts,natural64,i128]
  rintro a b (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> decide

theorem reordered_headroom_valid : validInitial
    {config with ceiling := some 1000,headroomKey := some "space"}
    {opener with data := {opener.data with selected := {opener.data.selected with
      headroomAllocations := .value [("bob",0),("alice",0),("treasury",0)]}}} root := by
  simp [validInitial,validAccounts,config,opener,root,bindings,members,issuers,accounts,natural64,i128,
    or_assoc,or_left_comm,or_comm]
  constructor <;> rintro a b (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> decide

theorem valid_burn_shape : validOperation config opener root burn := by
  simp [validOperation,kindMatches,config,opener,root,burn,accounts,natural64,issuers,bindings]

theorem burn_cone : ExactCone opener burn [burn] := by
  refine ⟨by simp,by simp [burn],?_,?_⟩
  · intro n hn id link
    have same : n = burn := by simpa using hn
    subst n
    exact Or.inl (by simpa [links,burn,opener] using link)
  · intro n hn
    have same : n = burn := by simpa using hn
    subst n
    exact .refl

theorem burn_budget_fault : budgetFault config opener burn [burn] := by
  unfold budgetFault
  right; right; right
  refine ⟨by simp [burn],0,insufficient_budget,by decide⟩

theorem concrete_budget_cause : Cause config [root,opener,burn] := by
  exact .budget (op := opener) (root := root) (a := burn) (C := [burn])
    (by simp) (by simp) rfl rfl valid_opener
    (fun n hn => by have same : n = burn := by simpa using hn
                    subst n
                    simp) burn_cone
    (by intro n hn; have same : n = burn := by simpa using hn
        subst n
        exact ⟨Or.inr (Or.inl rfl),valid_burn_shape⟩) burn_budget_fault

/-- The no-opener pending precedence is not assumed as an external classifier
law: every possible concrete cause except unsupported configuration needs one. -/
theorem no_opener_no_cause (F : Facts) (none : ∀ f ∈ F, ¬initial config f) : ¬Cause config F := by
  intro cause
  cases cause with
  | unsupported bad => simpa [config] using bad
  | openers ha _ ia _ _ => exact none _ ha ia
  | openerArity h i _ => exact none _ h i
  | initialization ho _ i _ _ => exact none _ ho i
  | malformed ho _ _ i _ _ _ => exact none _ ho i
  | fork ho _ i _ _ _ _ _ _ _ _ => exact none _ ho i
  | foreign ho _ _ _ _ i _ _ _ => exact none _ ho i
  | cycle ho _ i _ _ _ _ _ _ _ => exact none _ ho i
  | budget ho _ i _ _ _ _ _ _ => exact none _ ho i

def act (f : ResourceFact) : Act := {
  addr := f.id,verb := f.data.selected.verb,signer := f.data.signer,
  preds := f.data.selected.predecessors,fields := [],replaces := [] }

def decode (a : Act) : ResourceData :=
  if a.addr = 1 then root.data else if a.addr = 2 then opener.data else burn.data

theorem concrete_fault : faultRead config decode [act root,act opener,act burn] =
    some (evidence config decode [act root,act opener,act burn]) := by
  classical
  have projected : project decode [act root,act opener,act burn] = [root,opener,burn] := by
    rfl
  have cause : Fault config decode [act root,act opener,act burn] :=
    ⟨[act root,act opener,act burn],fun _ h => h,by rw [projected]; exact concrete_budget_cause⟩
  simp [faultRead,cause]

end CBCL.StateResourceTests
