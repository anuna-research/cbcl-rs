import LeanCbcl.StateNonnegativeAdmission

/-! Numeric extraction from recognized keyword/value rows. Shape's first-match
scan and the native state's last-value map are deliberately distinct. R7's
nonrouting-key uniqueness makes them agree on every accepted numeric field.
Full native message parsing/admission and hash/signature extraction remain ports. -/
set_option autoImplicit false
namespace CBCL.StateKeywordExtraction
open State StateNonnegativeAdmission

/-- Routing metadata is excluded from native state fields. -/
def routing (key : String) : Bool := ["caused-by","thread","from","to","sender"].contains key

/-- Raw parameter rows, retaining order and duplicates for recognition. -/
abbrev Rows := List (String × SExpr)

/-- Flatten recognized keyword/value rows without changing atom kinds. -/
def encode : Rows → List SExpr
  | [] => []
  | (key,value)::rest => .atom (.keyword key)::value::encode rest

/-- Recognize the complete pair grammar before interpreting field values. -/
def parse : List SExpr → Option Rows
  | [] => some []
  | .atom (.keyword key)::value::rest => do return (key,value)::(← parse rest)
  | _ => none

/-- All parameter trees represented by rows are recognized exactly. -/
theorem parse_encode (rows : Rows) : parse (encode rows) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => obtain ⟨key,value⟩ := row; simp [encode,parse,ih]

/-- Recognition preserves the complete input, without ignoring extra tokens. -/
theorem parse_sound (params : List SExpr) (rows : Rows) (parsed : parse params = some rows) : encode rows = params := by
  induction params using parse.induct generalizing rows with
  | case1 =>
    have same : rows = [] := (Option.some.inj parsed).symm
    subst rows
    rfl
  | case2 key value rest ih =>
    cases tail : parse rest with
    | none => simp [parse,tail] at parsed
    | some found =>
      have same : (key,value)::found = rows := by simpa [parse,tail] using parsed
      subst rows
      simp [encode,ih found tail]
  | case3 params => simp [parse] at parsed

/-- State-bearing data rows after the native routing-key exclusion. -/
def dataRows (rows : Rows) : Rows := rows.filter (fun row => !routing row.1)

/-- Native R7's duplicate-data-key condition. Routing keys are not included. -/
def Unique (rows : Rows) : Prop := ((dataRows rows).map Prod.fst).Nodup

instance (rows : Rows) : Decidable (Unique rows) := inferInstanceAs (Decidable (((dataRows rows).map Prod.fst).Nodup))

/-- Scalar conversion used by native legacy state values. Symbol/keyword cases
are total fallbacks; admitted state-bearing field types constrain their use. -/
def scalar : SExpr → Option Scalar
  | .atom (.num n) => some (.int n)
  | .atom (.str s) | .atom (.symbol s) => some (.str s)
  | .atom (.keyword s) => some (.str (":" ++ s))
  | .atom (.bool b) => some (.bool b)
  | .list _ => none

/-- Decode the scalar/scalar-list value domain represented by State.Val.
Nested nonscalar lists are outside this typed domain, never turned into numbers. -/
def decode : SExpr → Option Val
  | .list values => (values.mapM scalar).map Val.list
  | value => (scalar value).map Scalar.toVal

/-- Materialize last-value-first state fields. Admitted unique keys exclude any
fallback to an earlier value if a later raw value is outside the typed domain. -/
def fields (rows : Rows) : List (String × Val) :=
  (dataRows rows).reverse.filterMap (fun (key,value) => (decode value).map (key,·))

/-- A unique-key association list returns the value of each member. -/
theorem lookup_member {V : Type} (rows : List (String × V)) (unique : (rows.map Prod.fst).Nodup)
    (key : String) (value : V) (member : (key,value) ∈ rows) : rows.lookup key = some value := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨other,current⟩ := row
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | inside
    · cases same; simp
    · have different : key ≠ other := by
        intro same
        subst other
        exact parts.1 (List.mem_map.mpr ⟨(key,value),inside,rfl⟩)
      simpa [List.lookup,show (key == other) = false from by simpa using different] using ih parts.2 inside

/-- A decoded member is retained without changing its key. -/
theorem field_member (rows : Rows) (key : String) (raw : SExpr) (value : Val)
    (member : (key,raw) ∈ dataRows rows) (decoded : decode raw = some value) :
    (key,value) ∈ fields rows := by
  apply List.mem_filterMap.mpr
  exact ⟨(key,raw),by simpa using member,by simp [decoded]⟩

/-- Decoding cannot introduce duplicate data keys. -/
theorem fields_unique (rows : Rows) (unique : Unique rows) : (fields rows).map Prod.fst |>.Nodup := by
  have helper : ∀ raw : Rows,
      ((raw.filterMap (fun (key,value) => (decode value).map (key,·))).map Prod.fst).Sublist (raw.map Prod.fst) := by
    intro raw
    induction raw with
    | nil => exact .refl []
    | cons row rest ih =>
      obtain ⟨key,value⟩ := row
      cases decoded : decode value with
      | none => simpa [decoded] using List.Sublist.cons key ih
      | some current => simpa [decoded] using List.Sublist.cons₂ key ih
  have sub := helper (dataRows rows).reverse
  change ((dataRows rows).map Prod.fst).Nodup at unique
  have reversed : ((dataRows rows).reverse.map Prod.fst).Nodup := by simpa using (List.reverse_perm ((dataRows rows).map Prod.fst)).nodup_iff.mpr unique
  exact reversed.sublist sub

/-- Numeric state extraction retains the exact native raw-map member. -/
theorem numeric_member (rows : Rows) (unique : Unique rows) (key : String) (n : Int)
    (member : (key,.atom (.num n)) ∈ dataRows rows) :
    (fields rows).lookup key = some (.int n) :=
  lookup_member _ (fields_unique rows unique) key (.int n) (field_member rows key _ _ member rfl)

/-- A keyword-looking value cannot fabricate a numeric field from the next key. -/
theorem after_value (key : String) (value : SExpr) (rows : Rows) (n : Int)
    (found : findItems key (value::encode rows) = some (.atom (.num n))) :
    findItems key (encode rows) = some (.atom (.num n)) := by
  cases value with
  | list _ => exact found
  | atom atom => cases atom with
    | num _ | str _ | bool _ | symbol _ => exact found
    | keyword other =>
      by_cases same : other = key
      · subst other
        cases rows with
        | nil => simp [findItems,encode] at found
        | cons row rest => obtain ⟨name,raw⟩ := row; simp [findItems,encode] at found
      · simpa [findItems,same] using found

/-- Every numeric result of the first-match shape scan comes from a genuine
keyword/value row, even when other values are themselves keyword atoms. -/
theorem shape_member (rows : Rows) (key : String) (n : Int)
    (found : findItems key (encode rows) = some (.atom (.num n))) :
    (key,.atom (.num n)) ∈ rows := by
  induction rows with
  | nil => simp [encode,findItems] at found
  | cons row rest ih =>
    obtain ⟨name,value⟩ := row
    by_cases same : name = key
    · subst name
      have equal : value = .atom (.num n) := by simpa [encode,findItems] using found
      simp [equal]
    · have tail : findItems key (value::encode rest) = some (.atom (.num n)) := by
        simpa [encode,findItems,same] using found
      exact List.mem_cons_of_mem _ (ih (after_value key value rest n tail))

/-- The admitted first-shape/last-state numeric equality follows from grammar,
R7 uniqueness and routing exclusion, not a NumericExtraction oracle. -/
theorem shape_numeric (rows : Rows) (unique : Unique rows) (key : String) (n : Int)
    (dataKey : routing key = false) (found : findItems key (encode rows) = some (.atom (.num n))) :
    (fields rows).lookup key = some (.int n) := by
  apply numeric_member rows unique key n
  exact List.mem_filter.mpr ⟨shape_member rows key n found,by simp [dataKey]⟩

/-- The recognized simple-message header cannot masquerade as a keyword. -/
def cleanHeader (header : List SExpr) : Bool := header.all (fun item => match item with | .atom (.keyword _) => false | _ => true)

/-- Shape lookup passes a positional header without inspecting nested lists. -/
theorem header_lookup (header params : List SExpr) (key : String) (clean : cleanHeader header = true) :
    findItems key (header ++ params) = findItems key params := by
  induction header with
  | nil => rfl
  | cons item rest ih =>
    have parts := clean
    simp only [cleanHeader,List.all_cons,Bool.and_eq_true] at parts
    cases item with
    | list _ => exact ih parts.2
    | atom atom => cases atom with
      | keyword _ => contradiction
      | str _ | symbol _ | num _ | bool _ => exact ih parts.2

/-- No routing key can appear among materialized state fields. -/
theorem routing_absent (rows : Rows) (key : String) (route : routing key = true) : (fields rows).lookup key = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  obtain ⟨raw,inside,decoded⟩ := List.mem_filterMap.mp member
  obtain ⟨name,value⟩ := raw
  have allowed : routing name = false := by
    have original : (name,value) ∈ dataRows rows := by simpa using inside
    simpa using (List.mem_filter.mp original).2
  cases found : decode value with
  | none => simp [found] at decoded
  | some result =>
    have same : (name,result) = pair := by simpa [found] using decoded
    subst pair
    simp only [bne_iff_ne]
    intro identity
    subst name
    simp [route] at allowed

/-- Executable field extraction performs full pair recognition and duplicate
validation before materializing values. No trusted lookup callback is supplied. -/
def extract (params : List SExpr) : Option (List (String × Val)) := do
  let rows ← parse params
  if Unique rows then some (fields rows) else none

/-- Successful extraction supplies its exact raw rows and R7 uniqueness gate. -/
theorem extract_sound (params : List SExpr) (output : List (String × Val)) (accepted : extract params = some output) :
    ∃ rows, encode rows = params ∧ Unique rows ∧ fields rows = output := by
  cases parsed : parse params with
  | none => simp [extract,parsed] at accepted
  | some rows =>
    by_cases valid : Unique rows
    · exact ⟨rows,parse_sound params rows parsed,valid,by simpa [extract,parsed,valid] using accepted⟩
    · simp [extract,parsed,valid] at accepted

/-- Necessary shape success now proves the actual extracted amount nonnegative.
Routing fields contribute zero; data fields retain the exact checked number.
There is no independently supplied NumericExtraction premise. -/
theorem checked_amount (shapes : List StateInstalledLegacy.WriterShape) (verb key : String) (act : Act)
    (header params : List SExpr) (clean : cleanHeader header = true)
    (accepted : extract params = some act.fields)
    (mandatory : StateInstalledLegacy.mandatoryNonnegative shapes verb key = true) (writer : act.verb = verb)
    (checked : checkedWriter shapes act (.list (header ++ params)) = true) : 0 ≤ amount key act := by
  obtain ⟨rows,encoded,unique,extracted⟩ := extract_sound params act.fields accepted
  cases route : routing key with
  | true =>
    have absent : act.get key = none := by simp only [Act.get,← extracted,routing_absent rows key route]
    simp [amount,absent]
  | false =>
    obtain ⟨n,found,positive⟩ := checked_numeric shapes verb key act (.list (header ++ params)) mandatory writer checked
    have inRows : findItems key (encode rows) = some (.atom (.num n)) := by
      have raw : findItems key (header ++ encode rows) = some (.atom (.num n)) := by
        simpa only [findKeyword,← encoded] using found
      rw [header_lookup header (encode rows) key clean] at raw
      exact raw
    have actual : act.get key = some (.int n) := by
      simpa only [Act.get,← extracted] using shape_numeric rows unique key n route inRows
    simpa [amount,actual] using positive

/-- Full authored sum preservation now consumes recognized parameter extraction
and checked source syntax instead of a numeric-field oracle. -/
theorem successive_compiled (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (prepared : StateAuthoredBindings.Prepared) (accepted : StateAuthoredBindings.prepareStatic environment entries = some prepared)
    (name outputName verb key : String) (bound : Int)
    (present : (name,StateAuthoredBindings.Rule.legacy (.events verb key)) ∈ StateAuthoredBindings.rawFields entries)
    (threshold : StateAuthoredBindings.Entry.threshold outputName name [.element (.sum bound)] ∈ entries)
    (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (checked : ∀ act ∈ B, ∃ header params, cleanHeader header = true ∧ extract params = some act.fields ∧
      checkedWriter environment.shapes act (.list (header ++ params)) = true)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (earlier later : StateOutputCompiler.CompiledObservation)
    (compiledA : StateOutputCompiler.compileAuthored environment entries A = some earlier)
    (compiledB : StateOutputCompiler.compileAuthored environment entries B = some later)
    (reached : (outputName,.data (.reached (.element (.sum bound)))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.sum bound)))) ∈ later.observe ∨
      ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  obtain ⟨_,query,queryCompiled,_⟩ := StateAuthoredDataPreservation.authored_reached
    (.events verb key) environment entries prepared accepted name outputName present [.element (.sum bound)] threshold
      A rankedA consistentA earlier compiledA _ reached
  have mandatory := (StateAuthoredEventSum.admitted_sum environment prepared.domains verb key bound query queryCompiled).2
  apply StateAuthoredEventSum.successive_compiled environment entries prepared accepted name outputName verb key bound present threshold
    A B ?_ growth rankedA rankedB consistentA consistentB earlier later compiledA compiledB reached
  intro act member writer
  obtain ⟨header,params,clean,extracted,shapes⟩ := checked act member
  exact checked_amount environment.shapes verb key act header params clean extracted mandatory writer shapes

end CBCL.StateKeywordExtraction
