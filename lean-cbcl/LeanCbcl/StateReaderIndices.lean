import LeanCbcl.StateMemoizedReader
import LeanCbcl.StateInstalledRecognition

/-! Derive cache request ranks from successful installed-field compilation.
Typed extraction still identifies each native dependency with an IR reference;
field positions and their strict order are constructed from the compiler. -/
set_option autoImplicit false
namespace CBCL.StateReaderIndices
open StateInstalledCompiler StateMemoizedReader

/-- A scoped rule reference is either preinstalled or appears before its field
in the concrete compiled field list. -/
theorem reference_prefix {V : Type} (fields : List (String × Rule V)) (earlier : List String)
    (wellScoped : WellScoped earlier fields) (name : String) (rule : Rule V)
    (present : (name,rule) ∈ fields) (source : String) (used : source ∈ references rule) :
    source ∈ earlier ∨ ∃ priorFields laterFields, fields = priorFields ++ (name,rule)::laterFields ∧ source ∈ priorFields.map Prod.fst := by
  induction fields generalizing earlier with
  | nil => simp at present
  | cons binding rest ih =>
    obtain ⟨head,headRule⟩ := binding
    rcases List.mem_cons.mp present with same | inRest
    · cases same
      exact .inl (wellScoped.1 source used)
    · rcases ih (head::earlier) wellScoped.2 inRest with prior | ⟨priorFields,laterFields,equal,inside⟩
      · rcases List.mem_cons.mp prior with rfl | prior
        · obtain ⟨priorFields,laterFields,equal⟩ := List.mem_iff_append.mp inRest
          exact .inr ⟨(source,headRule)::priorFields,laterFields,by simp [equal],by simp⟩
        · exact .inl prior
      · exact .inr ⟨(head,headRule)::priorFields,laterFields,by simp [equal],by simp [inside]⟩

/-- Distinct compiled field names turn the compiler's backward-reference check
into a strict numeric index suitable for the cache termination argument. -/
theorem reference_index {V : Type} (fields : List (String × Rule V))
    (unique : (fields.map Prod.fst).Nodup) (wellScoped : WellScoped [] fields)
    (name : String) (rule : Rule V) (present : (name,rule) ∈ fields)
    (source : String) (used : source ∈ references rule) :
    (fields.map Prod.fst).idxOf source < (fields.map Prod.fst).idxOf name := by
  rcases reference_prefix fields [] wellScoped name rule present source used with impossible | ⟨priorFields,laterFields,equal,inside⟩
  · simp at impossible
  · have noDuplicate : ((priorFields.map Prod.fst) ++ name::(laterFields.map Prod.fst)).Nodup := by
      simpa [equal] using unique
    have fresh : name ∉ priorFields.map Prod.fst := by
      intro member
      exact (List.nodup_append.mp noDuplicate).2.2 name member name (by simp) rfl
    simpa [equal,List.idxOf_append,inside,fresh] using List.idxOf_lt_length_of_mem inside

/-- A successful installed-clause compiler establishes unique field names and
all backward-reference obligations without assuming a separate ordering gate. -/
theorem compiled_scoping {V : Type} (clause : StateInstalledClause.Clause V) (plans : Plans V)
    (compiled : StateInstalledClause.compile clause = some plans) :
    (clause.fields.map Prod.fst).Nodup ∧ WellScoped [] clause.fields := by
  unfold StateInstalledClause.compile at compiled
  split at compiled
  · rename_i metadata
    exact ⟨metadata.1,StateInstalledRecognition.attached_fields_sound [] clause.fields clause.freezes plans compiled⟩
  · contradiction

/-- Successful compilation constructs numeric ordering for every dependency
identified by the typed extraction boundary. -/
theorem compiled_dependency_ordering {W V : Type} (clause : StateInstalledClause.Clause W) (plans : Plans W)
    (compiled : StateInstalledClause.compile clause = some plans) (ops : Operations V)
    (extracted : ∀ name source, ops.dependency name = some source →
      ∃ rule, (name,rule) ∈ clause.fields ∧ source ∈ references rule) :
    ∀ name source, ops.dependency name = some source →
      (clause.fields.map Prod.fst).idxOf source < (clause.fields.map Prod.fst).idxOf name := by
  intro name source selected
  obtain ⟨rule,present,used⟩ := extracted name source selected
  exact reference_index clause.fields (compiled_scoping clause plans compiled).1
    (compiled_scoping clause plans compiled).2 name rule present source used

/-- Successful compilation supplies the cache rank for typed native dependency
extraction. No independently supplied numeric field ranking is needed. -/
theorem compiled_native_cache {W V : Type} (clause : StateInstalledClause.Clause W) (plans : Plans W)
    (compiled : StateInstalledClause.compile clause = some plans) (ops : Operations V)
    (extracted : ∀ name source, ops.dependency name = some source →
      ∃ rule, (name,rule) ∈ clause.fields ∧ source ∈ references rule) (keys : List Key) :
    let rank := requestRank (clause.fields.map Prod.fst).idxOf ops.cut
    let ranked := body_ranked ops (clause.fields.map Prod.fst).idxOf
      (compiled_dependency_ordering clause plans compiled ops extracted)
    ∃ after, reads ops.body rank keys [] = some (keys.map (reference ops.body rank ranked),after) ∧
      Valid (reference ops.body rank ranked) after :=
  native_reads_refinement ops (clause.fields.map Prod.fst).idxOf
    (compiled_dependency_ordering clause plans compiled ops extracted) keys

end CBCL.StateReaderIndices
