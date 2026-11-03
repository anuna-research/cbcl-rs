/-
  EPP correspondence — completion layer (`P`-complete / obligations / sealing).

  Extends `EPP.lean` (safety) to the completion level, mechanizing `lem:complete-reconcile`
  and the completion parts of `thm:epp`. An obligation of role `r` is a *witness-set*
  `W : Msg → Prop` of role-relevant messages, discharged by ANY single witness of `W`
  present and `Valid` in the store:

  * a required performative / a sealed `(all role[*])` fan-in member is a SINGLETON `W`
    (its unique witness must be present and `Valid`);
  * a pooled `(any role[*])` obligation is a MULTI-member `W` (any occupant discharges
    it) — genuinely disjunctive: two locally complete runs may discharge the same pooled
    obligation via different occupants, and the glued store keeps them all.

  On "present and `Valid`" versus the paper's bare "present" for plain required
  performatives: the strengthening is vacuous on the correspondence's domain — in a
  `P`-safe closed configuration (and in a locally safe, causally closed run) presence
  already implies validity (`valid_of_safe_closed`; packaged for obligations as
  `dischargedFor_of_present`). We state discharge with `isValid` so the sealed
  `(all role[*])` "present and Valid" requirement is carried verbatim.

  A single shared obligation system `O` models the (Seal) clause — all roles agree on the
  cast and its sealed memberships. This is agreement BY FIAT: sharing one `O` across the
  global and local sides assumes the cast is common rather than stating cast agreement as
  a checkable compatibility condition, so `completeness_completion` cannot detect cast
  disagreement — a family whose members believe different casts is simply outside the
  model. Making (Seal) endpoint-checkable is future work (`proof.tex` §Notes).
-/
import LeanCbcl.EPP

namespace LeanCbcl.EPP

/-- An obligation system: `oblig r W` means witness-set `W` is one of role `r`'s local
    obligations, discharged by any single member of `W`; every potential witness is
    `r`-relevant. A single shared `O` is the (Seal) clause (agreement on the cast /
    sealed memberships — see the header note on what that assumes). -/
structure Obligations {Role Perf Msg : Type} (P : Proto Role Perf Msg) where
  /-- `oblig r W`: witness-set `W` is one of role `r`'s local obligations. -/
  oblig    : Role → (Msg → Prop) → Prop
  obligRel : ∀ r W, oblig r W → ∀ w, W w → endpoint P w r

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg)

/-- Role `r`'s obligations are discharged in store `S`: every obligation has some witness
    present *and `Valid`* (not merely present) -- the "present and Valid" requirement on
    sealed `(all role[*])` fan-in members, vacuously stronger than bare presence for the
    other obligation kinds on the correspondence's domain (`dischargedFor_of_present`). -/
def dischargedFor (O : Obligations P) (S : Cfg Msg) (r : Role) : Prop :=
  ∀ W, O.oblig r W → ∃ w, W w ∧ S w ∧ isValid P S w

/-- On a safe closed store, bare *presence* of a witness per obligation already discharges:
    presence implies validity there (`valid_of_safe_closed`), so requiring `Valid` in
    `dischargedFor` does not strengthen the paper's "required performative present". -/
theorem dischargedFor_of_present (O : Obligations P) {S : Cfg Msg}
    (hcl : closedCfg P S) (hsafe : pSafe P S) {r : Role}
    (h : ∀ W, O.oblig r W → ∃ w, W w ∧ S w) : dischargedFor P O S r := by
  intro W hW
  obtain ⟨w, hWw, hSw⟩ := h W hW
  exact ⟨w, hWw, hSw, valid_of_safe_closed P hcl hsafe hSw⟩

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
  intro W hW
  obtain ⟨w, hWw, hwC, hwV⟩ := hdis r W hW
  have hproj : project P C r w := ⟨hwC, O.obligRel r W hW w hWw⟩
  exact ⟨w, hWw, hproj, (reconcile_global P hcl hsafe hproj).2.1.2 hwV⟩

/-- **Completion reconciliation (ii)** / **Completeness (completion)** (`thm:epp`(2)):
    gluing a compatible family of locally complete runs yields a `P`-complete
    configuration. Disjunctive obligations glue soundly even when different runs
    discharged them via different witnesses -- each role's own witness survives in the
    union. -/
theorem completeness_completion (O : Obligations P) (F : Family P)
    (hLC : ∀ r, localComplete P O (F.run r) r) : pComplete P O (glue P F) := by
  refine ⟨(completeness_safety P F (fun r => (hLC r).1)).1, glue_closed P F, ?_⟩
  intro r W hW
  obtain ⟨w, hWw, hwr, hwV⟩ := (hLC r).2 W hW
  exact ⟨w, hWw, ⟨r, hwr⟩, (reconcile_glue P F hwr).1 hwV⟩

/-- **EPP correspondence at the completion level**: soundness, completeness, and both
    round-trip identities, for `P`-complete configurations and compatible families of
    locally complete runs. (`pComplete` already packages safety and closure, so no
    separate hypotheses are taken; the projection family is built from its components.) -/
theorem epp_correspondence_complete (O : Obligations P) {C : Cfg Msg}
    (hc : pComplete P O C) :
    (∀ r, localComplete P O (project P C r) r) ∧
    pComplete P O (glue P (projFamily P hc.2.1 hc.1)) ∧
    (∀ m, glue P (projFamily P hc.2.1 hc.1) m ↔ C m) ∧
    (∀ (F : Family P) (r : Role) (m : Msg), project P (glue P F) r m ↔ F.run r m) := by
  refine ⟨fun r => soundness_completion P O hc r, ?_, ?_, ?_⟩
  · exact completeness_completion P O (projFamily P hc.2.1 hc.1)
      (fun r => soundness_completion P O hc r)
  · intro m; exact glue_project_eq P m
  · intro F r m; exact project_glue_eq P F r m

end LeanCbcl.EPP
