/-
  EPP correspondence — completion layer (`P`-complete / obligations / sealing).

  Extends `EPP.lean` (safety) to the completion level, mechanizing `lem:complete-reconcile`
  and the completion parts of `thm:epp`. Obligations are modelled as required, role-relevant
  witness messages (`req r w`); discharge is their presence in the store. A single shared
  obligation system `O` models the (Seal) clause — all roles agree on the cast and its sealed
  memberships. This captures, uniformly, "required performatives present", "sealed
  `(all role[*])` members present", and "pooled `(any role[*])` occupant present".
-/
import LeanCbcl.EPP

namespace LeanCbcl.EPP

/-- An obligation system: `req r w` means message `w` is required for role `r`'s local
    obligations; every required witness is `r`-relevant. A single shared `O` is the (Seal)
    clause (agreement on the cast / sealed memberships). -/
structure Obligations {Role Perf Msg : Type} (P : Proto Role Perf Msg) where
  /-- `req r w`: message `w` is a required witness for role `r`'s local obligations. -/
  req    : Role → Msg → Prop
  reqRel : ∀ r w, req r w → endpoint P w r

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg)

/-- Role `r`'s obligations are discharged in store `S`: every required witness is present
    *and `Valid`* (not merely present) -- this is the "present and Valid" requirement on
    sealed `(all role[*])` fan-in members. -/
def dischargedFor (O : Obligations P) (S : Cfg Msg) (r : Role) : Prop :=
  ∀ w, O.req r w → S w ∧ isValid P S w

/-- A local run is locally complete: locally safe and its role's obligations discharged. -/
def localComplete (O : Obligations P) (L : Cfg Msg) (r : Role) : Prop :=
  localSafe P L ∧ dischargedFor P O L r

/-- `C` is `P`-complete: safe, closed, and every role's obligations discharged. -/
def pComplete (O : Obligations P) (C : Cfg Msg) : Prop :=
  pSafe P C ∧ closedCfg P C ∧ ∀ r, dischargedFor P O C r

/-- **Completion reconciliation (i)** / **Soundness (completion)** (`thm:epp`(1)): each
    projection of a `P`-complete configuration is locally complete. -/
theorem soundness_completion (O : Obligations P) {C : Cfg Msg}
    (hc : pComplete P O C) (r : Role) : localComplete P O (project P C r) r := by
  obtain ⟨hsafe, hcl, hdis⟩ := hc
  refine ⟨soundness_safety P hcl hsafe r, ?_⟩
  intro w hw
  obtain ⟨hwC, hwV⟩ := hdis r w hw
  have hproj : project P C r w := ⟨hwC, O.reqRel r w hw⟩
  exact ⟨hproj, (reconcile_global P hcl hsafe hproj).2.1.2 hwV⟩

/-- **Completion reconciliation (ii)** / **Completeness (completion)** (`thm:epp`(2)):
    gluing a compatible family of locally complete runs yields a `P`-complete configuration. -/
theorem completeness_completion (O : Obligations P) (F : Family P)
    (hLC : ∀ r, localComplete P O (F.run r) r) : pComplete P O (glue P F) := by
  refine ⟨(completeness_safety P F (fun r => (hLC r).1)).1, glue_closed P F, ?_⟩
  intro r w hw
  obtain ⟨hwr, hwV⟩ := (hLC r).2 w hw
  exact ⟨⟨r, hwr⟩, (reconcile_glue P F hwr).1 hwV⟩

/-- **EPP correspondence at the completion level**: soundness, completeness, and the
    round-trip identity, for `P`-complete configurations and compatible families of locally
    complete runs. -/
theorem epp_correspondence_complete (O : Obligations P) {C : Cfg Msg}
    (hcl : closedCfg P C) (hsafe : pSafe P C) (hc : pComplete P O C) :
    (∀ r, localComplete P O (project P C r) r) ∧
    pComplete P O (glue P (projFamily P hcl hsafe)) ∧
    (∀ m, glue P (projFamily P hcl hsafe) m ↔ C m) := by
  refine ⟨fun r => soundness_completion P O hc r, ?_, ?_⟩
  · exact completeness_completion P O (projFamily P hcl hsafe)
      (fun r => soundness_completion P O hc r)
  · intro m; exact glue_project_eq P m

end LeanCbcl.EPP



