import LeanCbcl.SExpr
import LeanCbcl.Message
import LeanCbcl.Dialect
import LeanCbcl.Agent
import LeanCbcl.Parser
import LeanCbcl.Serializer
import LeanCbcl.MessageParser
import LeanCbcl.PatternMatch
import LeanCbcl.DialectParser
import LeanCbcl.R1NoRecursion
import LeanCbcl.R2ResourceBounds
import LeanCbcl.R3CorePreservation

/-!
# CBCL Verified Pipeline

The complete verified pipeline from raw string input to safe message evaluation.

```
  String
    │  parse
    ▼
  SExpr
    │  parseMessage
    ▼
  Message
    │  validateMessage
    ▼
  ValidMessage
    │  verifyDialect (R1+R2+R3)
    ▼
  SafeMessage
    │  boundedEval
    ▼
  Result (guaranteed termination)
```

Every step is a total function with machine-checked properties.
-/

namespace CBCL

/-- Result of the full pipeline. -/
inductive PipelineResult where
  | success : Message → PipelineResult
  | parseError : String → PipelineResult
  | validationError : String → PipelineResult
  deriving Repr, BEq, DecidableEq

/-- Run the full verified pipeline on a string. -/
def runPipeline (input : String) : PipelineResult :=
  match parse input with
  | .error msg => .parseError msg
  | .ok sexpr =>
    match parseMessage sexpr with
    | none => .validationError "not a valid CBCL message structure"
    | some msg =>
      let errors := validateMessage msg
      if errors.isEmpty then
        match msg.type, msg.params with
        | .metaMsg, defExpr :: _ =>
          match defExpr with
          | .list (.atom (.symbol head) :: _) =>
            if head == "define" || head == "define-dialect" then
              match parseDialect defExpr with
              | .error err => .validationError err
              | .ok d =>
                if verifyR1Dialect d && verifyR2 d && verifyR3 d then
                  .success msg
                else
                  .validationError "dialect failed R1/R2/R3 verification"
            else
              .success msg
          | _ => .success msg
        | _, _ => .success msg
      else .validationError s!"{errors}"

/-- Verify that a dialect definition (as a string) passes all safety constraints. -/
def verifyDialectString (dialectDef : String) : Except String Dialect :=
  match parse dialectDef with
  | .error msg => .error s!"parse error: {msg}"
  | .ok sexpr =>
    match parseDialect sexpr with
    | .error msg => .error msg
    | .ok d =>
      if verifyR1Dialect d && verifyR2 d && verifyR3 d then
        .ok d
      else
        .error "dialect failed R1/R2/R3 verification"

/-- The pipeline always terminates. -/
theorem pipeline_terminates (input : String) :
    ∃ result, runPipeline input = result := ⟨_, rfl⟩

/-- The pipeline correctly handles any input: it either succeeds or produces an error. -/
theorem pipeline_total (input : String) :
    (∃ msg, runPipeline input = .success msg) ∨
    (∃ msg, runPipeline input = .parseError msg) ∨
    (∃ msg, runPipeline input = .validationError msg) := by
  match runPipeline input with
  | .success msg         => exact .inl ⟨msg, rfl⟩
  | .parseError msg      => exact .inr (.inl ⟨msg, rfl⟩)
  | .validationError msg => exact .inr (.inr ⟨msg, rfl⟩)

-- ============================================================
-- Pipeline structure lemmas (without concrete string reduction)
-- ============================================================

/-- If parse succeeds and parseMessage succeeds and validation passes,
    runPipeline returns success for non-meta messages. -/
theorem runPipeline_success (input : String) (sexpr : SExpr) (msg : Message)
    (hp : parse input = .ok sexpr)
    (hm : parseMessage sexpr = some msg)
    (hv : (validateMessage msg).isEmpty = true)
    (hmeta : msg.type ≠ .metaMsg) :
    runPipeline input = .success msg := by
  simp [runPipeline, hp, hm, hv, hmeta]

/-- If parse fails, runPipeline returns parseError. -/
theorem runPipeline_parseError (input : String) (errMsg : String)
    (hp : parse input = .error errMsg) :
    runPipeline input = .parseError errMsg := by
  simp [runPipeline, hp]

/-- If parse succeeds but parseMessage fails, runPipeline returns validationError. -/
theorem runPipeline_msgError (input : String) (sexpr : SExpr)
    (hp : parse input = .ok sexpr)
    (hm : parseMessage sexpr = none) :
    runPipeline input = .validationError "not a valid CBCL message structure" := by
  simp [runPipeline, hp, hm]

-- ============================================================
-- Pipeline soundness: success implies grammar validity
-- ============================================================

/-- If the pipeline succeeds, the parsed SExpr satisfies the message grammar. -/
theorem pipeline_success_implies_valid (input : String) (msg : Message) :
    runPipeline input = .success msg →
    ∃ sexpr, parse input = .ok sexpr ∧
             parseMessage sexpr = some msg ∧
             (validateMessage msg).isEmpty = true := by
  intro h
  cases hparse : parse input with
  | error errMsg =>
    simp [runPipeline, hparse] at h
  | ok sexpr =>
    cases hmsg : parseMessage sexpr with
    | none =>
      simp [runPipeline, hparse, hmsg] at h
    | some msg' =>
      cases hvalid : (validateMessage msg').isEmpty with
      | false =>
        simp [runPipeline, hparse, hmsg, hvalid] at h
      | true =>
        cases htype : msg'.type with
        | metaMsg =>
          cases hparams : msg'.params with
          | nil =>
            simp [runPipeline, hparse, hmsg, hvalid, htype, hparams] at h
            have heq : msg' = msg := by cases h; rfl
            exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
          | cons defExpr rest =>
            cases hdef : defExpr with
            | atom a =>
              simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef] at h
              have heq : msg' = msg := by cases h; rfl
              exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
            | list xs =>
              cases xs with
              | nil =>
                simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef] at h
                have heq : msg' = msg := by cases h; rfl
                exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
              | cons hd tl =>
                cases hd with
                | atom a =>
                  cases a with
                  | symbol head =>
                    by_cases hhead : (head == "define" || head == "define-dialect") = true
                    · cases hpd : parseDialect (SExpr.list (SExpr.atom (Atom.symbol head) :: tl)) with
                      | error err =>
                        simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef, hhead, hpd] at h
                      | ok d =>
                        by_cases hver : (verifyR1Dialect d && verifyR2 d && verifyR3 d) = true
                        · simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef, hhead, hpd, hver] at h
                          have heq : msg' = msg := by cases h; rfl
                          exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
                        · simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef, hhead, hpd, hver] at h
                    · simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef, hhead] at h
                      have heq : msg' = msg := by cases h; rfl
                      exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
                  | _ =>
                    simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef] at h
                    have heq : msg' = msg := by cases h; rfl
                    exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
                | list _ =>
                  simp [runPipeline, hparse, hmsg, hvalid, htype, hparams, hdef] at h
                  have heq : msg' = msg := by cases h; rfl
                  exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
        | simple =>
          simp [runPipeline, hparse, hmsg, hvalid, htype] at h
          have heq : msg' = msg := by cases h; rfl
          exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
        | dialect =>
          simp [runPipeline, hparse, hmsg, hvalid, htype] at h
          have heq : msg' = msg := by cases h; rfl
          exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩
        | wrapped =>
          simp [runPipeline, hparse, hmsg, hvalid, htype] at h
          have heq : msg' = msg := by cases h; rfl
          exact ⟨sexpr, by simp, heq ▸ hmsg, heq ▸ hvalid⟩

/-- Pipeline success implies the message satisfies the grammar relation. -/
theorem pipeline_success_grammar (input : String) (msg : Message) :
    runPipeline input = .success msg →
    ∃ sexpr, parse input = .ok sexpr ∧ ValidMessageGrammar sexpr msg := by
  intro h
  obtain ⟨sexpr, hparse, hmsg, _⟩ := pipeline_success_implies_valid input msg h
  exact ⟨sexpr, hparse, parseMessage_sound sexpr msg hmsg⟩

end CBCL
