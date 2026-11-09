import LeanCbcl.StateNonnegativeAdmissionTests

/-! A concrete complete authored event-sum trace with an actual reached result.
This typed fixture does not assert native protocol admission. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredSumTrace
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredDataProvenance StateAuthoredDataOutputs

/-- Source and sum threshold without a freezer declaration. -/
def entries : List Entry := [
  .field "credits" (.legacy (.events "mint" "amount")),
  .threshold "funded" "credits" [.element (.sum 5)]]

/-- Exact static result of the concrete authored compiler. -/
noncomputable def prepared (environment : Environment) : Prepared :=
  ⟨[.field "credits" ((Head.events "mint" "amount").definition environment []),
    .threshold "funded" "credits" [.element (.sum 5)]],[],[]⟩

/-- The static installation result is computed, not supplied. -/
theorem preparation (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredEventSumTests.environment context) entries =
      some (prepared (StateAuthoredEventSumTests.environment context)) := by rfl

/-- Successful compilation retains the actual prepared history and global
freezes. This helper does not assume any observed output. -/
theorem compiled_metadata (environment : Environment) (items : List Entry) (static : Prepared)
    (accepted : prepareStatic environment items = some static) (A : List Act)
    (program : CompiledObservation) (compiled : compileAuthored environment items A = some program) :
    program.history = A ∧ program.program.freezes = materialize static.domains A static.freezes := by
  simp only [compileAuthored,prepare,accepted] at compiled
  change ((StateOutputCompiler.compileClause (clauseAt static A)).bind (fun output => some (⟨A,output⟩ : CompiledObservation))) = some program at compiled
  cases sources : StateInstalledLowering.compile (clauseAt static A) with
  | none =>
    simp only [clauseAt] at sources
    simp [StateOutputCompiler.compileClause,clauseAt,sources] at compiled
  | some plans =>
    simp only [clauseAt] at sources
    cases code : compileDeclarations plans [] (clauseAt static A).declarations with
    | none =>
      simp only [clauseAt] at code
      simp [StateOutputCompiler.compileClause,clauseAt,sources,code] at compiled
    | some outputs =>
      simp only [clauseAt] at code
      have same : (⟨A,⟨(clauseAt static A).freezes,outputs⟩⟩ : CompiledObservation) = program := by
        simpa [StateOutputCompiler.compileClause,clauseAt,sources,code] using compiled
      subst program
      exact ⟨rfl,rfl⟩

/-- A native witness yields an actual named reached member in the complete
compiled vector. No earlier reached-output premise appears here. -/
theorem compiled_reached (context : StateKernelSEC.Context) (A : List Act)
    (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (reached : 5 ≤ sumField "amount" (StateDomainSupportLocality.selected [] ["mint"] (StateScopePool.normalize A))) :
    ∃ program, compileAuthored (StateAuthoredEventSumTests.environment context) entries A = some program ∧
      ("funded",.data (.reached (.element (.sum 5)))) ∈ program.observe := by
  let environment := StateAuthoredEventSumTests.environment context
  have accepted := preparation context
  obtain ⟨declaration,query,program,compiled,queryCompiled,member,history,metadata⟩ :=
    authored_emitted (.events "mint" "amount") environment entries (prepared environment) accepted "credits" "funded"
      (by simp [entries,rawFields,Head.rule]) [.element (.sum 5)] (by simp [entries]) A ranked consistent
  have actual := compiled_metadata environment entries (prepared environment) accepted A program compiled
  have noFreeze : program.program.freezes = [] := actual.2
  have noDeclaration : declaration = none := by
    rw [noFreeze] at metadata
    cases declaration with
    | none => rfl
    | some verb => simp at metadata
  subst declaration
  obtain ⟨code,codeCompiled,run⟩ := StateNativeEventSum.compiled_sum environment [] "mint" "amount" 5 (by decide) rfl
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  refine ⟨program,compiled,?_⟩
  apply dispatch_member (.events "mint" "amount") environment [] A none "credits" "funded" query program member history metadata
  have ran := run (StateScopePool.normalize A) (StateScopePool.normalize_unique A consistent)
  have source : ∃ payload, sourceValue A ((Head.events "mint" "amount").bare environment []) = .data payload := by
    exact ⟨_,rfl⟩
  obtain ⟨payload,source⟩ := source
  change ("funded",query.run (StateScopePool.normalize A) (sourceValue A ((Head.events "mint" "amount").bare environment []))) = _
  rw [source,ran payload]
  simp only [reached,if_true]

/-- A later writer extends the first writer's causal history. -/
def laterWriter : Act := ⟨2,"mint","@b",[1],[("amount",.int 2)],[]⟩

/-- Later reverse delivery repeats a writer identity without adding weight. -/
def laterHistory : List Act := [laterWriter,StateAuthoredEventSumTests.writer,laterWriter]

/-- The later writer's expanded message retains its numeric atom. -/
def laterMessage : SExpr := .list [.atom (.symbol "mint"),.atom (.keyword "amount"),.atom (.num 2)]

/-- Expanded numeric lookup agrees with the second typed writer's field. -/
theorem later_extracted : StateNonnegativeAdmission.NumericExtraction laterWriter laterMessage := by
  intro field n found
  by_cases same : field = "amount"
  · subst field
    have number : n = 2 := by simpa [StateNonnegativeAdmission.findKeyword,StateNonnegativeAdmission.findItems,laterMessage] using found.symm
    subst n
    rfl
  · have different : "amount" ≠ field := Ne.symm same
    simp [StateNonnegativeAdmission.findKeyword,StateNonnegativeAdmission.findItems,laterMessage,different,beq_iff_eq] at found

/-- Every delivered later identity has computed shape checks and proved field
extraction. No whole-program reached result is used as evidence here. -/
theorem later_checked (context : StateKernelSEC.Context) : ∀ act ∈ laterHistory, ∃ message,
    StateNonnegativeAdmission.checkedWriter (StateAuthoredEventSumTests.environment context).shapes act message = true ∧
      StateNonnegativeAdmission.NumericExtraction act message := by
  intro act member
  have choices : act = laterWriter ∨ act = StateAuthoredEventSumTests.writer ∨ act = laterWriter := by simpa [laterHistory] using member
  rcases choices with rfl | rfl | rfl
  · exact ⟨laterMessage,rfl,later_extracted⟩
  · exact ⟨StateNonnegativeAdmissionTests.message,StateNonnegativeAdmissionTests.checked,StateNonnegativeAdmissionTests.extracted⟩
  · exact ⟨laterMessage,rfl,later_extracted⟩

/-- Normalized later evidence contributes five plus two, despite delivery of
three records and reverse causal order. -/
theorem later_total : sumField "amount" (StateDomainSupportLocality.selected [] ["mint"]
    (StateScopePool.normalize laterHistory)) = 7 := by decide

/-- Concrete earlier and later complete programs exist. The earlier reached
member is proved from native evaluation; the later result follows through the
checked-shape authored preservation theorem, even with duplicate reverse delivery. -/
theorem successive_trace (context : StateKernelSEC.Context) : ∃ earlier later,
    compileAuthored (StateAuthoredEventSumTests.environment context) entries [StateAuthoredEventSumTests.writer] = some earlier ∧
    compileAuthored (StateAuthoredEventSumTests.environment context) entries laterHistory = some later ∧
    ("funded",.data (.reached (.element (.sum 5)))) ∈ earlier.observe ∧
    (("funded",.data (.reached (.element (.sum 5)))) ∈ later.observe ∨ ∃ evidence, ("funded",.fault evidence) ∈ later.observe) := by
  let A := [StateAuthoredEventSumTests.writer]
  let B := laterHistory
  let environment := StateAuthoredEventSumTests.environment context
  have uniqueA : NodupAddr A := by change ([1] : List Nat).Nodup; decide
  have consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b := fun _ ha _ hb eq => uniqueA.eq_of_addr ha hb eq
  have consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b := by
    have unique : NodupAddr [StateAuthoredEventSumTests.writer,laterWriter] := by change ([1,2] : List Nat).Nodup; decide
    have inside : ∀ act ∈ B, act ∈ [StateAuthoredEventSumTests.writer,laterWriter] := by
      intro act member
      simp only [B,laterHistory,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> simp
    exact fun _ ha _ hb eq => unique.eq_of_addr (inside _ ha) (inside _ hb) eq
  have rankedA : StateExecutableFreeze.Ranked A := StateCausalRank.causalCheck_sound A (by decide)
  have rankedB : StateExecutableFreeze.Ranked B := StateCausalRank.causalCheck_sound B (by decide)
  have growth : ∀ act ∈ A, act ∈ B := by
    intro act member
    have same : act = StateAuthoredEventSumTests.writer := by simpa [A] using member
    subst act
    exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨earlier,compiledA,reached⟩ := compiled_reached context A rankedA consistentA (by decide)
  have positive := StateNonnegativeAdmission.checked_history environment.shapes "mint" "amount" B rfl (later_checked context)
  obtain ⟨later,compiledB,_⟩ := StateAuthoredEventSum.program_stability environment entries (prepared environment) (preparation context)
    "credits" "funded" "mint" "amount" 5 (by simp [entries,rawFields]) (by simp [entries]) B positive rankedB consistentB
  refine ⟨earlier,later,compiledA,compiledB,reached,?_⟩
  exact StateNonnegativeAdmission.successive_compiled environment entries (prepared environment) (preparation context)
    "credits" "funded" "mint" "amount" 5 (by simp [entries,rawFields]) (by simp [entries]) A B growth (later_checked context)
    rankedA rankedB consistentA consistentB earlier later compiledA compiledB reached

end CBCL.StateAuthoredSumTrace
