import LeanCbcl.StateJsonValue

/-! Canonical spelling and stored-order fixtures, independent of admission. -/
namespace CBCL.StateJsonValueTests
open StateJsonValue

/-- C0 controls without short forms use lowercase four-digit escapes. -/
theorem lowercase_control : StateJsonString.quote (String.ofList [Char.ofNat 11]) = "\"\\u000b\"" := by decide

/-- Quotes, backslashes and short control escapes have exact native spellings. -/
theorem short_escapes : StateJsonString.quote (String.ofList ['"','\\','\n','\r','\t',Char.ofNat 8,Char.ofNat 12]) =
    "\"\\\"\\\\\\n\\r\\t\\b\\f\"" := by decide

/-- Unicode scalar sequences are emitted without normalization or ASCII conversion. -/
theorem raw_unicode : StateJsonString.quote "é𝄞🌍é" = "\"é𝄞🌍é\"" := by decide

/-- The independent string decoder rejects unescaped C0 characters. -/
theorem unescaped_control_rejected : StateJsonString.unquote "\"\n\"" = none := by decide

/-- List and set serializers preserve the stored order instead of sorting here. -/
theorem stored_set_order : render (.set [.int 2,.int 1]) = "[2,1]" := by simp only [render,sequence] <;> decide

/-- Event values retain signer and recursively rendered payload. -/
theorem event_layout : render (.event "@a" (.list [.int 2,.bool true])) = "{\"by\":\"@a\",\"value\":[2,true]}" := by simp only [render,sequence] <;> decide

/-- Non-string map keys use rendered key text; all text is quoted exactly once. -/
theorem key_layout : render (.map [(.int 2,.str "x"),(.str "quoted\"key",.absent)]) =
    "{\"2\":\"x\",\"quoted\\\"key\":null}" := by simp only [render,members,keyText] <;> decide

/-- Whole states retain declaration order, not alphabetic field order. -/
theorem clause_order : renderState [("z",.bool true),("a",.int 1)] = "{\"z\":true,\"a\":1}" := by simp [renderState,render,members,keyText] <;> decide

end CBCL.StateJsonValueTests
