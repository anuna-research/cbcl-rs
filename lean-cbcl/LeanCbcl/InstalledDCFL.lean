import LeanCbcl.InstalledSyntax
import LeanCbcl.Pipeline

/-!
# DCFL preservation under finite dialect installation

The syntax construction works for EVERY finite declaration environment. Thus
it is stronger than preservation restricted to a particular installation gate:
R1/R2/R3/R5/R6 cannot invalidate it by selecting a subset of installations.
This module does not assert that a rejected dialect is installed in the runtime.
Freshness additionally preserves unique name lookup and previous bindings.
The input language here is the classified TOKEN language; raw lexical lifting
is a separate obligation of SPEC-018 CON-1803.
-/
namespace CBCL.InstalledSyntax
open FormalLanguage

/-- The strengthened token-language installation certificate. -/
def dcfl_preserved (a : Agent) (d : Dialect) :
    IsRealtimeDCFL (tokenLanguage (a.installDialect d).dialects) :=
  environmentDCFL (a.installDialect d).dialects

def installMany (a : Agent) (ds : List Dialect) : Agent := ds.foldl Agent.installDialect a

theorem installMany_dialects (a : Agent) (ds : List Dialect) :
    (installMany a ds).dialects = a.dialects ++ ds := by
  induction ds generalizing a with
  | nil => simp [installMany]
  | cons d ds ih =>
    change (installMany (a.installDialect d) ds).dialects = _
    rw [ih]
    simp [Agent.installDialect, List.append_assoc]

/-- No global bound on the number of installations or declarations is imposed. -/
def dcfl_preserved_many (a : Agent) (ds : List Dialect) :
    IsRealtimeDCFL (tokenLanguage (installMany a ds).dialects) :=
  environmentDCFL (installMany a ds).dialects

/-- Any actual admission policy can instantiate this relation. The syntax
    theorem needs no unproved claim about that policy's implementation. -/
inductive AcceptedInstalls (accept : Agent → Dialect → Prop) : Agent → List Dialect → Agent → Prop
  | nil (a) : AcceptedInstalls accept a [] a
  | cons {a b d ds} : accept a d →
      AcceptedInstalls accept (a.installDialect d) ds b →
      AcceptedInstalls accept a (d :: ds) b

theorem AcceptedInstalls.result {accept : Agent → Dialect → Prop}
    {a b : Agent} {ds : List Dialect} (h : AcceptedInstalls accept a ds b) :
    b = installMany a ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- This quantifies over every policy, including stricter real installation gates. -/
def accepted_installations_dcfl {accept : Agent → Dialect → Prop}
    {a b : Agent} {ds : List Dialect} (_h : AcceptedInstalls accept a ds b) :
    IsRealtimeDCFL (tokenLanguage b.dialects) := environmentDCFL b.dialects

def base_dcfl (id : String) : IsRealtimeDCFL (tokenLanguage (Agent.new id).dialects) :=
  environmentDCFL (Agent.new id).dialects

theorem fresh_names_preserved (a : Agent) (d : Dialect)
    (hu : (a.dialects.map Dialect.name).Nodup)
    (hf : d.name ∉ a.dialects.map Dialect.name) :
    ((a.installDialect d).dialects.map Dialect.name).Nodup := by
  simp only [Agent.installDialect, List.map_append, List.map_cons, List.map_nil]
  apply List.nodup_append.mpr
  refine ⟨hu, by simp, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst y
  intro he
  exact hf (he ▸ hx)

theorem previous_declarations_preserved (a : Agent) (d old : Dialect)
    (h : old ∈ a.dialects) : old ∈ (a.installDialect d).dialects := by
  simp [Agent.installDialect, h]

/-- Append-only installation preserves first-match resolution even without freshness. -/
theorem previous_lookup_preserved (a : Agent) (d old : Dialect) (name : String)
    (h : a.dialects.find? (fun x => x.name == name) = some old) :
    (a.installDialect d).dialects.find? (fun x => x.name == name) = some old := by
  simp [Agent.installDialect, List.find?_append, h]

/-- The existing Lean dialect-verification gate, plus the fresh-name condition.
    Rust has additional admission gates; the unconditional theorem above also
    covers every finite environment those stricter gates can produce. -/
def VerifiedFresh (a : Agent) (d : Dialect) : Prop :=
  (verifyR1Dialect d && verifyR2 d && verifyR3 d) = true ∧
    d.name ∉ a.dialects.map Dialect.name

/-- This ties the named relation to the existing executable Lean pipeline. -/
theorem pipeline_verified_fresh (a : Agent) (d : Dialect) (source : String)
    (h : verifyDialectString source = .ok d)
    (hf : d.name ∉ a.dialects.map Dialect.name) : VerifiedFresh a d := by
  refine ⟨?_, hf⟩
  unfold verifyDialectString at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h

abbrev VerifiedFreshInstalls := AcceptedInstalls VerifiedFresh

def verified_fresh_installations_dcfl {a b : Agent} {ds : List Dialect}
    (h : VerifiedFreshInstalls a ds b) : IsRealtimeDCFL (tokenLanguage b.dialects) :=
  accepted_installations_dcfl h

 theorem verified_sequence_unique {a b : Agent} {ds : List Dialect}
    (h : VerifiedFreshInstalls a ds b) (hu : (a.dialects.map Dialect.name).Nodup) :
    (b.dialects.map Dialect.name).Nodup := by
  revert hu
  induction h with
  | nil => exact id
  | @cons a b d ds ha _ ih =>
    intro hu
    exact ih (fresh_names_preserved a d hu ha.2)

 theorem duplicate_not_verified_fresh (a : Agent) (d : Dialect)
    (h : d.name ∈ a.dialects.map Dialect.name) : ¬ VerifiedFresh a d :=
  fun ha => ha.2 h

end CBCL.InstalledSyntax
