import LeanCbcl.StateEventMapKernel

/-! Exact event totals count each address once. Missing and nonnumeric fields
contribute zero, as in the native numeric field fold. -/
set_option autoImplicit false
namespace CBCL.StateEventMapTotal
open State StateKernelSemantics StateKernelQueries StateKernelAggregates StateEventMapKernel

/-- Omitting missing payloads does not change a numeric field total. -/
theorem present_sum (field : String) (A : List Act) :
    sumField field (A.filter (fun a => (a.get field).isSome)) = sumField field A := by
  induction A with
  | nil => rfl
  | cons a rest ih =>
    cases data : a.get field with
    | none => simp [data,sumField_cons,amount,ih]
    | some value => simp [data,sumField_cons,ih]

/-- Supported keys enumerate exactly the present-field writers' addresses. -/
theorem keys_perm (clock : Clock) (rank : SignerRank) (A : List Act) (verb field : String)
    (unique : NodupAddr A) :
    (evalMap clock rank A (plan verb field)).keys.Perm
      ((select A (.withField (.verb verb) field)).map (fun a => Val.int a.addr)) := by
  have selectedUnique := select_unique unique (.withField (.verb verb) field)
  have mappedUnique : ((select A (.withField (.verb verb) field)).map (fun a => Val.int a.addr)).Nodup := by
    have addresses := List.Pairwise.map (S := fun (a b : Val) => a ≠ b) (fun a => Val.int a.addr)
      (fun a b different equal => different (Int.ofNat.inj (Val.int.inj equal)))
      (List.pairwise_map.mp selectedUnique)
    exact addresses
  apply (List.perm_ext_iff_of_nodup (map_correct clock rank A (plan verb field)).1 mappedUnique).mpr
  intro key
  rw [(map_correct clock rank A (plan verb field)).2.1]
  simp only [List.mem_map,select_correct]
  constructor
  · rintro ⟨a,chosen,equal⟩
    exact ⟨a,chosen,(Option.some.inj equal)⟩
  · rintro ⟨a,chosen,equal⟩
    exact ⟨a,chosen,congrArg some equal⟩

/-- The actual map aggregate equals the native total over unique source acts. -/
theorem map_total (clock : Clock) (rank : SignerRank) (A : List Act) (verb field : String)
    (unique : NodupAddr A) :
    mapSum (evalMap clock rank A (plan verb field)) = sumField field (acts verb A) := by
  have permutation := keys_perm clock rank A verb field unique
  have sums := sum_perm (permutation.map (fun key => cellNumber ((evalMap clock rank A (plan verb field)).read key)))
  have cells : ((select A (.withField (.verb verb) field)).map
      (fun a => cellNumber ((evalMap clock rank A (plan verb field)).read (.int a.addr)))) =
      (select A (.withField (.verb verb) field)).map (Number field) := by
    apply List.map_congr_left
    intro a member
    have chosen := (select_correct A (.withField (.verb verb) field) a).mp member
    have selected : (a ∈ A ∧ a.verb = verb) ∧ (a.get field).isSome = true := chosen
    cases data : a.get field with
    | none => simp [data] at selected
    | some value =>
      rw [read_event clock rank A verb field (fun _ ha _ hb eq => unique.eq_of_addr ha hb eq)
        a selected.1.1 selected.1.2 value data]
      cases value <;> simp [cellNumber,Number,data]
  calc
    mapSum (evalMap clock rank A (plan verb field)) =
        (((evalMap clock rank A (plan verb field)).keys).map
          (fun key => cellNumber ((evalMap clock rank A (plan verb field)).read key))).sum := by
      simp only [mapSum,List.sum_eq_foldl,List.foldl_map]
    _ = (((select A (.withField (.verb verb) field)).map (fun a => Val.int a.addr)).map
          (fun key => cellNumber ((evalMap clock rank A (plan verb field)).read key))).sum := sums
    _ = ((select A (.withField (.verb verb) field)).map (Number field)).sum := by
      simpa only [List.map_map,Function.comp_def] using congrArg List.sum cells
    _ = sumField field (select A (.withField (.verb verb) field)) := (sumField_eq _ _).symm
    _ = sumField field (acts verb A) := present_sum field (acts verb A)

/-- Canonical history and domain selection preserve the exact event sum test.
The unique-address premise is the store boundary, not a numeric-shape premise. -/
theorem native_sum (context : StateKernelSEC.Context) (domains : List StateInstalledDomains.Domain)
    (verb field : String) (bound : Int) (A : List Act) (unique : NodupAddr A) :
    StateInstalledLegacy.readTest (.element (.sum bound))
      (.kernel (StateInstalledDomains.evaluate context domains (.mapped (plan verb field)) (StateLVar.rawHistory A))) =
      decide (bound ≤ sumField field (StateDomainSupportLocality.selected domains [verb] A)) := by
  have canonicalUnique := StateInstalledLegacy.history_unique unique
  have selectedUnique := canonicalUnique.filter
    (fun act => domains.all (fun domain => StateInstalledDomains.eligible domain (StateInstalledLegacy.history (StateLVar.rawHistory A)) act))
  have total := map_total context.clock context.rank
    (StateInstalledDomains.select domains (StateInstalledLegacy.history (StateLVar.rawHistory A))) verb field selectedUnique
  have same := StateNativeDataPolicies.selected_setEq domains [verb] (StateInstalledLegacy.history_setEq A)
  have sumSame := sumField_setEq (selectedUnique.filter _) ((unique.filter _).filter _) same field
  have bridge : sumField field (acts verb (StateInstalledDomains.select domains (StateInstalledLegacy.history (StateLVar.rawHistory A)))) =
      sumField field (StateDomainSupportLocality.selected domains [verb] A) := by
    simpa [StateDomainSupportLocality.selected,acts,StateInstalledDomains.select,beq_iff_eq] using sumSame
  simp only [StateInstalledDomains.evaluate,StateInstalledDomains.rawExpression,StateKernel.evaluate,
    StateKernelSEC.Context.input,StateNativeDataPolicies.admitted_nil,StateInstalledLegacy.readTest]
  simp only [Bool.false_eq_true,ite_false]
  rw [total,bridge]

end CBCL.StateEventMapTotal
