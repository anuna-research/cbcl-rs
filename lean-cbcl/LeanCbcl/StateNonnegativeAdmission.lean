import LeanCbcl.StateAuthoredEventSum
import LeanCbcl.SExpr

/-! Necessary mandatory/nonnegative checks from the native shape stage, over
expanded messages. This projection does not replace general shape validation.
Typed numeric-field extraction remains explicit; no Rust extraction is assumed. -/
set_option autoImplicit false
namespace CBCL.StateNonnegativeAdmission
open State StateInstalledLegacy StateAuthoredBindings StateInstalledCompiler StateOutputCompiler

/-- Native shape lookup scans every top-level item and stops at the first
matching keyword, including a dangling match with no following value. -/
def findItems (field : String) : List SExpr → Option SExpr
  | [] => none
  | item :: rest => match item with
    | .atom (.keyword key) => if key == field then rest.head? else findItems field rest
    | _ => findItems field rest

/-- Top-level lookup on the fully expanded message. -/
def findKeyword (message : SExpr) (field : String) : Option SExpr :=
  match message with | .list items => findItems field items | _ => none

/-- The exact native nonnegative type test accepts numeric atoms only. -/
def nonnegative : SExpr → Bool
  | .atom (.num n) => decide (0 ≤ n)
  | _ => false

/-- Necessary checks retained by the recognized writer-shape metadata. Other
native type, child and depth checks are additional admission obligations. -/
def checkProjection (shape : WriterShape) (message : SExpr) : Bool :=
  match findKeyword message shape.field with
  | none => !shape.required
  | some value => !shape.nonnegative || nonnegative value

/-- Every recognized shape for the decoded writer is checked, conjunctively. -/
def checkedWriter (shapes : List WriterShape) (act : Act) (message : SExpr) : Bool :=
  shapes.all (fun shape => if shape.verb == act.verb then checkProjection shape message else true)

/-- Expanded-message numeric lookup agrees with the typed state-field decoder.
This relation is an extraction boundary, not a shape or positivity assumption. -/
def NumericExtraction (act : Act) (message : SExpr) : Prop :=
  ∀ field n, findKeyword message field = some (.atom (.num n)) → act.get field = some (.int n)

/-- A mandatory nonnegative shape plus successful projected checks supplies a
present numeric atom and its nonnegative value. -/
theorem checked_numeric (shapes : List WriterShape) (verb field : String) (act : Act) (message : SExpr)
    (mandatory : mandatoryNonnegative shapes verb field = true) (verbEq : act.verb = verb)
    (checked : checkedWriter shapes act message = true) :
    ∃ n, findKeyword message field = some (.atom (.num n)) ∧ 0 ≤ n := by
  obtain ⟨shape,member,valid⟩ := List.any_eq_true.mp mandatory
  have properties : shape.verb = verb ∧ shape.field = field ∧ shape.required = true ∧ shape.nonnegative = true := by
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using valid
  have check := List.all_eq_true.mp checked shape member
  have projected : checkProjection shape message = true := by simpa [verbEq,properties.1] using check
  cases found : findKeyword message field with
  | none => simp [checkProjection,properties.2.1,found,properties.2.2.1] at projected
  | some value =>
    have positive : nonnegative value = true := by
      simpa [checkProjection,properties.2.1,found,properties.2.2.2] using projected
    cases value with
    | list _ => simp [nonnegative] at positive
    | atom atom => cases atom with
      | num n => exact ⟨n,rfl,by simpa [nonnegative] using positive⟩
      | _ => simp [nonnegative] at positive

/-- Shape success yields the numeric premise used by event-sum preservation,
provided expanded numeric fields are faithfully extracted. -/
theorem checked_amount (shapes : List WriterShape) (verb field : String) (act : Act) (message : SExpr)
    (mandatory : mandatoryNonnegative shapes verb field = true) (verbEq : act.verb = verb)
    (checked : checkedWriter shapes act message = true) (extracted : NumericExtraction act message) :
    0 ≤ amount field act := by
  obtain ⟨n,found,positive⟩ := checked_numeric shapes verb field act message mandatory verbEq checked
  simpa [amount,extracted field n found] using positive

/-- Per-act shape-stage evidence establishes every later writer's amount law;
the conclusion is derived rather than asserted from installation metadata. -/
theorem checked_history (shapes : List WriterShape) (verb field : String) (B : List Act)
    (mandatory : mandatoryNonnegative shapes verb field = true)
    (accepted : ∀ act ∈ B, ∃ message, checkedWriter shapes act message = true ∧ NumericExtraction act message) :
    ∀ act ∈ B, act.verb = verb → 0 ≤ amount field act := by
  intro act member verbEq
  obtain ⟨message,checked,extracted⟩ := accepted act member
  exact checked_amount shapes verb field act message mandatory verbEq checked extracted

/-- Actual authored sum preservation consumes checked expanded-message evidence,
rather than an externally supplied amount inequality. Numeric extraction and
full native admission remain explicit boundaries. -/
theorem successive_compiled (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb field : String) (bound : Int)
    (present : (name,StateAuthoredBindings.Rule.legacy (.events verb field)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.sum bound)] ∈ entries)
    (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (checked : ∀ act ∈ B, ∃ message, checkedWriter environment.shapes act message = true ∧ NumericExtraction act message)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (earlier later : StateOutputCompiler.CompiledObservation)
    (compiledA : compileAuthored environment entries A = some earlier)
    (compiledB : compileAuthored environment entries B = some later)
    (reached : (outputName,.data (.reached (.element (.sum bound)))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.sum bound)))) ∈ later.observe ∨
      ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  obtain ⟨_,query,queryCompiled,_⟩ := StateAuthoredDataPreservation.authored_reached
    (.events verb field) environment entries prepared accepted name outputName present [.element (.sum bound)] threshold
    A rankedA consistentA earlier compiledA _ reached
  have mandatory := (StateAuthoredEventSum.admitted_sum environment prepared.domains verb field bound query queryCompiled).2
  exact StateAuthoredEventSum.successive_compiled environment entries prepared accepted name outputName verb field bound
    present threshold A B (checked_history environment.shapes verb field B mandatory checked) growth rankedA rankedB
    consistentA consistentB earlier later compiledA compiledB reached

end CBCL.StateNonnegativeAdmission
