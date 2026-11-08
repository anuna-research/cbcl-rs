import LeanCbcl.StateEventMapTotal

/-! Numeric totals count addresses rather than distinct payloads. These typed
fixtures exercise arithmetic and field projection, not protocol admission. -/
set_option autoImplicit false
namespace CBCL.StateEventMapTotalTests
open State StateKernelQueries StateKernelAggregates StateEventMapKernel

/-- Two equal positive payloads, a negative, a missing field and a nonnumber. -/
def writers : List Act := [
  ⟨1,"mint","@a",[],[("amount",.int 5)],[]⟩,
  ⟨2,"mint","@b",[],[("amount",.int 5)],[]⟩,
  ⟨3,"mint","@a",[],[("amount",.int (-1))],[]⟩,
  ⟨4,"mint","@a",[],[],[]⟩,
  ⟨5,"mint","@a",[],[("amount",.str "5")],[]⟩,
  ⟨6,"other","@a",[],[("amount",.int 99)],[]⟩]

/-- The fixture satisfies the store's distinct-address invariant. -/
theorem unique : NodupAddr writers := by
  change ([1,2,3,4,5,6] : List Nat).Nodup
  decide

/-- Equal amounts count twice; negative values remain signed; other verbs,
missing fields and nonnumeric values add nothing. No clock premise is needed. -/
theorem exact_total (clock : Clock) (rank : SignerRank) :
    mapSum (evalMap clock rank writers (plan "mint" "amount")) = 9 := by
  rw [StateEventMapTotal.map_total clock rank writers "mint" "amount" unique]
  decide

/-- The actual canonical kernel sum test reaches its exact boundary. -/
theorem threshold_boundary (context : StateKernelSEC.Context) :
    StateInstalledLegacy.readTest (.element (.sum 9))
      (.kernel (StateInstalledDomains.evaluate context [] (.mapped (plan "mint" "amount")) (StateLVar.rawHistory writers))) = true := by
  rw [StateEventMapTotal.native_sum context [] "mint" "amount" 9 writers unique]
  decide

/-- The next bound stays pending; this fixture does not claim nonnegative
threshold stability for its deliberately negative writer. -/
theorem threshold_above (context : StateKernelSEC.Context) :
    StateInstalledLegacy.readTest (.element (.sum 10))
      (.kernel (StateInstalledDomains.evaluate context [] (.mapped (plan "mint" "amount")) (StateLVar.rawHistory writers))) = false := by
  rw [StateEventMapTotal.native_sum context [] "mint" "amount" 10 writers unique]
  decide

end CBCL.StateEventMapTotalTests
