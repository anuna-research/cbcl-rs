import LeanCbcl.StateFaultRendering

/-! Canonical byte order, witness membership and public fault layout. -/
namespace CBCL.StateFaultRenderingTests
open StateFaultRendering StateJsonValue

/-- Reordering and duplicates do not affect canonical evidence. -/
theorem ascii_order : canonical ["b","a","b",""] = ["","a","b"] := by
  simp +decide [canonical,StateLift.FinSet.dedup,List.mergeSort]

/-- The missing-byte sentinel precedes an actual zero byte. -/
theorem nul_prefix_order : canonical ["a",String.ofList [Char.ofNat 0],"","aa","a" ++ String.ofList [Char.ofNat 0]] =
    ["",String.ofList [Char.ofNat 0],"a","a" ++ String.ofList [Char.ofNat 0],"aa"] := by
  simp +decide [canonical,StateLift.FinSet.dedup,List.mergeSort]

/-- Compare raw address bytes, not the spelling of their quoted JSON strings. -/
theorem raw_byte_order : canonical ["[","\""] = ["\"","["] := by
  simp +decide [canonical,StateLift.FinSet.dedup,List.mergeSort]

/-- Multibyte Unicode ordering agrees with UTF-8 byte lexicographic order. -/
theorem unicode_order : canonical ["β","a","😀","é"] = ["a","é","β","😀"] := by
  simp +decide [canonical,StateLift.FinSet.dedup,List.mergeSort]

/-- Faults render fixed keys with complete sorted unique evidence and reason. -/
theorem fault_layout : render (fault "r" ["b","a","b"]) =
    "{\"evidence\":[\"a\",\"b\"],\"reason\":\"r\",\"status\":\"fault\"}" := by
  simp +decide [fault,canonical,StateLift.FinSet.dedup,List.mergeSort,render,members,keyText,sequence]

end CBCL.StateFaultRenderingTests
