import LeanCbcl.StateResourceCache
import LeanCbcl.StateResourceTests

namespace CBCL.StateResourceCacheTests
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceTests

def second : ResourceFact := {burn with id := 4,data := {burn.data with amount := 2,prev := some 3}}
def otherOwner : ResourceFact := {burn with id := 5,data := {burn.data with signer := "@bob",amount := 7}}

/-- Interleaved owners must not contaminate each other's cumulative prefix.
These are Summary::record checks; budget authorization is a separate phase. -/
theorem cached_owner_sequence_and_debit :
    ((execute 2 [burn,otherOwner,second] emptyCache).bind fun cache =>
      (cache 4).map fun entry => (entry.2.sequence,entry.2.debited)) = some (2,3) := by decide

theorem cached_other_owner_sequence_and_debit :
    ((execute 2 [burn,otherOwner,second] emptyCache).bind fun cache =>
      (cache 5).map fun entry => (entry.2.sequence,entry.2.debited)) = some (1,7) := by decide

theorem actual_cached_tip_chooses_longer_prefix :
    ((execute 2 [burn,otherOwner,second] emptyCache).bind fun cache => chooseTip cache 3 4) = some 4 := by decide

theorem absent_previous_prevents_cache_insertion :
    ((execute 2 [second] emptyCache).map fun cache => (cache 4).isSome) = none := by decide

end CBCL.StateResourceCacheTests
