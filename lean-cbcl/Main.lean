import LeanCbcl.Pipeline
import LeanCbcl.Serializer

/-!
# CBCL Parser — Verified Executable

A formally verified CBCL parser extracted from Lean proofs.
Every function in this binary has machine-checked correctness properties.

Usage:
  cbcl-parse                     # Read from stdin
  cbcl-parse "(tell alice hello)" # Parse argument
  cbcl-parse --verify-dialect "..." # Verify a dialect definition
-/

open CBCL

def showResult : PipelineResult → IO Unit
  | .success msg => do
    IO.println "OK"
    IO.println s!"  type: {repr msg.type}"
    IO.println s!"  performative: {repr msg.performative}"
    IO.println s!"  params: {msg.params.length} argument(s)"
  | .parseError msg =>
    IO.eprintln s!"PARSE ERROR: {msg}"
  | .validationError msg =>
    IO.eprintln s!"VALIDATION ERROR: {msg}"

def main (args : List String) : IO Unit := do
  match args with
  | ["--help"] => do
    IO.println "cbcl-parse: Formally verified CBCL message parser"
    IO.println ""
    IO.println "Usage:"
    IO.println "  cbcl-parse <sexpr>             Parse a CBCL message"
    IO.println "  cbcl-parse --verify-dialect <s> Verify a dialect definition"
    IO.println "  cbcl-parse --test              Run verification test suite"
    IO.println ""
    IO.println "All parsing and verification is backed by Lean 4 proofs."
  | ["--test"] => do
    IO.println "=== CBCL Verified Parser Test Suite ==="
    IO.println ""
    let tests := [
      ("(tell alice hello)", true),
      ("(ask bob (status))", true),
      ("(reply (data 42))", true),
      ("(error \"not found\")", true),
      ("(ok)", true),
      ("(cancel thread-1)", true),
      ("(hello)", true),
      ("(bye)", true),
      ("(meta (define my-dialect))", true),
      ("(lang my-dialect (tell alice hi))", true),
      ("(with-limits ((max-depth . 8)) (tell alice hi))", true),
      ("(custom-perf alice data)", true),
      ("(tell alice hi) trailing", false),
      ("\"unterminated", false),
      ("", false),
      (")(", false),
      ("(unclosed", false)
    ]
    let mut passed := 0
    let mut failed := 0
    for (input, expectOk) in tests do
      let result := runPipeline input
      let isOk := match result with | .success _ => true | _ => false
      if isOk == expectOk then
        IO.println s!"  PASS: {input}"
        passed := passed + 1
      else
        IO.println s!"  FAIL: {input} (expected {if expectOk then "ok" else "error"}, got {repr result})"
        failed := failed + 1
    IO.println ""
    IO.println s!"Results: {passed} passed, {failed} failed"
    if failed > 0 then
      IO.Process.exit 1
  | ["--verify-dialect", dialectStr] =>
    match verifyDialectString dialectStr with
    | .ok d => IO.println s!"Dialect '{d.name}' passed R1/R2/R3 verification"
    | .error msg => IO.eprintln s!"Verification failed: {msg}"
  | [input] => showResult (runPipeline input)
  | [] => do
    let stdin ← IO.getStdin
    let input ← stdin.getLine
    showResult (runPipeline input.trimAsciiEnd.toString)
  | _ => IO.eprintln "Usage: cbcl-parse [--test | --help | <sexpr>]"
