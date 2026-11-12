/-
  Dialect enactability — the enactability check against the deployed verifier model.

  `Enactability.lean` decides enactability for an abstract clause table related to a
  `Proto` by hypothesis. This file removes the hypothesis for the name-level model of the
  deployed verifier in `R6DCFLPreservation.lean`: a `RoleProtocol` whose predecessor
  declarations are read by `justified`, route by route, as `verify_causal` reads them.
  The frame is Singh's enactability (AAMAS 2012, Def. 13).

  What is proved:

  * A CHECKER (`enactable`, `unenactableSteps`) computed from the protocol alone.
  * EXACTNESS (`enactable_iff_occurs`): a performative passes exactly when it occurs in
    some arrival-order trace (`CausalTrace`), that is, in some run in which every
    message is justified on arrival.
  * ONE ENACTMENT FOR THE WHOLE PROTOCOL (`unenactableSteps_eq_nil_iff`): the check
    reports nothing exactly when a single arrival-order trace contains every declared
    step.
  * ACYCLIC PROTOCOLS ARE ENACTABLE (`enactable_of_acyclic`): if the named-predecessor
    relation is well-founded and no step has a degenerate clause list, every
    performative is enactable. So for such protocols the check can never fail, and
    enactability is a consequence of acyclicity, not an additional requirement.
  * The converse fails (`Examples.cyclic_enactable`), and the degenerate case is real
    (`Examples.emptyAny_unenactable`): a step whose only declaration is an empty
    `(any)` is acyclic and can never be justified.

  Scope notes (read before citing):

  * The model is the NAME-LEVEL one of `R6DCFLPreservation.lean`, with its disclosed
    idealisations (first declaration wins on duplicate names; `begin` as a literal
    citation route; undeclared performatives unconstrained). Nothing here is connected
    to the Rust `CausalProtocol` beyond what that file already models.
  * Occurrence is stated for `CausalTrace`, not `StoreTrace`. The store language is
    order-free at name level and so admits words in which two steps justify each other;
    messages cannot do that, because a citation is a content address of an earlier
    message. `causalTrace_storeTrace` gives the inclusion.
  * `enactable_of_acyclic` assumes well-foundedness of `dependsOn`. It is NOT derived
    from the R5 acyclicity checker (`R5.lean`), which is stated over a different step
    record and over the successor graph. That the two agree for parser-built protocols
    is expected and unproved.
  * Roles do not enter: every participant is taken as willing. Obligations, casts and
    sealed role rosters are outside this file.
-/
import LeanCbcl.R6DCFLPreservation
import LeanCbcl.Enactability

namespace CBCL.DialectEnactability

open CBCL.R6DCFLPreservation
open LeanCbcl.Enactability (Table)

/-! ## Arrival-order traces -/

theorem foldl_none {P : RoleProtocol} (w : List String) :
    w.foldl (traceStep P) none = none := by
  induction w with
  | nil => rfl
  | cons t rest ih => exact ih

/-- A live arrival-order run has consumed exactly its input. -/
theorem foldl_some {P : RoleProtocol} :
    ∀ (w seen : List String), w.foldl (traceStep P) (some seen) ≠ none →
      w.foldl (traceStep P) (some seen) = some (w.reverse ++ seen) := by
  intro w
  induction w with
  | nil => intro seen _; rfl
  | cons u rest ih =>
    intro seen h
    cases hen : enabled P (fun x => seen.contains x) u with
    | false =>
      have hts : traceStep P (some seen) u = none := by
        simp only [traceStep, hen]
        simp
      rw [List.foldl_cons, hts] at h
      exact absurd (foldl_none rest) h
    | true =>
      have hts : traceStep P (some seen) u = some (u :: seen) := by
        simp only [traceStep, hen]
        simp
      rw [List.foldl_cons, hts] at h ⊢
      rw [ih (u :: seen) h]
      simp

/-- The first step of a live run was enabled, and the rest is live. -/
theorem foldl_cons_live {P : RoleProtocol} {u : String} {rest seen : List String}
    (h : (u :: rest).foldl (traceStep P) (some seen) ≠ none) :
    enabled P (fun x => seen.contains x) u = true ∧
      rest.foldl (traceStep P) (some (u :: seen)) ≠ none := by
  cases hen : enabled P (fun x => seen.contains x) u with
  | false =>
    have hts : traceStep P (some seen) u = none := by
        simp only [traceStep, hen]
        simp
    rw [List.foldl_cons, hts] at h
    exact absurd (foldl_none rest) h
  | true =>
    have hts : traceStep P (some seen) u = some (u :: seen) := by
        simp only [traceStep, hen]
        simp
    rw [List.foldl_cons, hts] at h
    exact ⟨rfl, h⟩

theorem causalTrace_nil (P : RoleProtocol) : CausalTrace P [] := by
  simp [CausalTrace]

/-- A trace extends by any step justified by what it already contains. -/
theorem causalTrace_snoc {P : RoleProtocol} {w : List String} {t : String}
    (h : CausalTrace P w) (ht : enabled P (fun x => w.contains x) t = true) :
    CausalTrace P (w ++ [t]) := by
  unfold CausalTrace at h ⊢
  have hen : enabled P (fun x => (w.reverse ++ []).contains x) t = true :=
    enabled_mono (fun x hx => by simpa using hx) ht
  rw [List.foldl_append, foldl_some w [] h]
  simp only [List.foldl_cons, List.foldl_nil, traceStep, hen]
  simp

/-- A trace extends by a list of steps each justified by what it already contains. -/
theorem causalTrace_append {P : RoleProtocol} :
    ∀ (l w : List String), CausalTrace P w →
      (∀ t, t ∈ l → enabled P (fun x => w.contains x) t = true) → CausalTrace P (w ++ l) := by
  intro l
  induction l with
  | nil => intro w h _; simpa using h
  | cons t l ih =>
    intro w h hl
    have h1 := causalTrace_snoc h (hl t List.mem_cons_self)
    have h2 := ih (w ++ [t]) h1 (fun u hu =>
      enabled_mono (fun x hx => by
        simp only [List.contains_iff_mem, List.mem_append] at hx ⊢
        exact Or.inl hx) (hl u (List.mem_cons_of_mem t hu)))
    simpa [List.append_assoc] using h2

/-- Justification is monotone on the relevant names alone. -/
theorem enabled_transfer {P : RoleProtocol} {f g : String → Bool}
    (h : ∀ x, x ∈ relevantNames P → f x = true → g x = true) {t : String}
    (ht : enabled P f t = true) : enabled P g t = true := by
  have h1 : enabled P (fun x => decide (x ∈ relevantNames P) && f x) t = true := by
    rw [← enabled_congr (f := f) (fun x hx => by simp [hx]) t]
    exact ht
  refine enabled_mono (fun x hx => ?_) h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  exact h x hx.1 hx.2

/-! ## The checker -/

/-- `x` has no step declaration; the verifier leaves it unconstrained. -/
def undeclared (P : RoleProtocol) (x : String) : Bool := !(stepNames P).contains x

/-- What can have been seen: undeclared names, and declared names in `R`. -/
def seenOf (P : RoleProtocol) (R : String → Bool) : String → Bool :=
  fun x => undeclared P x || R x

/-- The clause table of a protocol, for the generic fixed-point checker. -/
def table (P : RoleProtocol) : Table String where
  perfs := stepNames P
  deps := fun _ => relevantNames P
  sat := fun t R => enabled P (seenOf P R) t
  honest := fun _ => true

/-- **The checker.** `t` is enactable: it is undeclared, or the least fixed point of
    "justified by enactable names" contains it. -/
def enactable (P : RoleProtocol) (t : String) : Bool :=
  undeclared P t || (table P).enactable t

/-- The declared steps that can never be justified. -/
def unenactableSteps (P : RoleProtocol) : List String :=
  (stepNames P).filter (fun t => !enactable P t)

theorem mem_stepNames_of_declared {P : RoleProtocol} {t : String}
    (h : undeclared P t = false) : t ∈ stepNames P := by
  simpa [undeclared] using h

theorem stepNames_relevant {P : RoleProtocol} {t : String} (h : t ∈ stepNames P) :
    t ∈ relevantNames P := List.mem_append.2 (Or.inl h)

/-! ## Soundness: enactable names occur -/

/-- After each round there is one trace containing everything found so far. -/
theorem iter_trace (P : RoleProtocol) :
    ∀ n, ∃ w, CausalTrace P w ∧
      ∀ x, x ∈ relevantNames P → seenOf P ((table P).iter n) x = true → x ∈ w := by
  intro n
  induction n with
  | zero =>
    refine ⟨(relevantNames P).filter (undeclared P), ?_, ?_⟩
    · have h := causalTrace_append ((relevantNames P).filter (undeclared P)) []
        (causalTrace_nil P) (fun t ht => by
          have hu : undeclared P t = true := (List.mem_filter.1 ht).2
          exact enabled_of_undeclared (by simpa [undeclared] using hu))
      simpa using h
    · intro x hx hs
      have hu : undeclared P x = true := by simpa [seenOf, Table.iter] using hs
      exact List.mem_filter.2 ⟨hx, hu⟩
  | succ n ih =>
    obtain ⟨w, hw, hin⟩ := ih
    let fresh : String → Bool := fun t => (table P).iter (n + 1) t && !(table P).iter n t
    have hfresh : ∀ t, t ∈ (stepNames P).filter fresh →
        enabled P (fun x => w.contains x) t = true := by
      intro t ht
      have hf : fresh t = true := (List.mem_filter.1 ht).2
      simp only [fresh, Bool.and_eq_true, Bool.not_eq_true'] at hf
      obtain ⟨_, _, hsat⟩ := (table P).step_new hf.1 hf.2
      refine enabled_transfer (fun x hx hs => ?_) hsat
      have hs' : seenOf P ((table P).iter n) x = true := by
        simp only [seenOf, Table.avail, Bool.or_eq_true, Bool.and_eq_true] at hs ⊢
        exact hs.elim Or.inl (fun h => Or.inr h.2)
      exact List.contains_iff_mem.2 (hin x hx hs')
    refine ⟨w ++ (stepNames P).filter fresh, causalTrace_append _ w hw hfresh, ?_⟩
    intro x hx hs
    cases hold : seenOf P ((table P).iter n) x with
    | true => exact List.mem_append.2 (Or.inl (hin x hx hold))
    | false =>
      simp only [seenOf, Bool.or_eq_false_iff] at hold
      have hnew : (table P).iter (n + 1) x = true := by
        simpa [seenOf, hold.1] using hs
      have hmem : x ∈ stepNames P := ((table P).step_new hnew hold.2).1
      exact List.mem_append.2 (Or.inr (List.mem_filter.2 ⟨hmem, by simp [fresh, hnew, hold.2]⟩))

/-- **Soundness.** An enactable performative occurs in some arrival-order trace. -/
theorem enactable_occurs {P : RoleProtocol} {t : String} (h : enactable P t = true) :
    ∃ w, CausalTrace P w ∧ t ∈ w := by
  cases hu : undeclared P t with
  | true =>
    have h1 := causalTrace_append [t] [] (causalTrace_nil P) (fun u hu' => by
      have e : u = t := by simpa using hu'
      subst e
      exact enabled_of_undeclared (by simpa [undeclared] using hu))
    exact ⟨[t], by simpa using h1, List.mem_cons_self⟩
  | false =>
    obtain ⟨w, hw, hin⟩ := iter_trace P (stepNames P).length
    exact ⟨w, hw, hin t (stepNames_relevant (mem_stepNames_of_declared hu)) h⟩

/-! ## Completeness: what occurs is enactable -/

theorem trace_enactable_aux (P : RoleProtocol) :
    ∀ (w seen : List String), w.foldl (traceStep P) (some seen) ≠ none →
      (∀ x, x ∈ seen → enactable P x = true) → ∀ t, t ∈ w → enactable P t = true := by
  intro w
  induction w with
  | nil => intro _ _ _ t ht; exact nomatch ht
  | cons u rest ih =>
    intro seen h hseen
    obtain ⟨hen, hrest⟩ := foldl_cons_live h
    have hu : enactable P u = true := by
      cases hdecl : undeclared P u with
      | true => simp [enactable, hdecl]
      | false =>
        have hsat : enabled P
            (seenOf P ((table P).avail ((table P).iter (stepNames P).length) u)) u = true := by
          refine enabled_transfer (fun x hx hs => ?_) hen
          have hx' : enactable P x = true := hseen x (List.contains_iff_mem.1 hs)
          simp only [enactable, Table.enactable, Bool.or_eq_true] at hx'
          simp only [seenOf, Table.avail, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq]
          exact hx'.elim Or.inl (fun h => Or.inr ⟨hx, h⟩)
        have hE : (table P).enactable u = true :=
          (table P).enactable_of_sat (mem_stepNames_of_declared hdecl) rfl hsat
        rw [enactable, hE]
        exact Bool.or_true _
    intro t ht
    cases List.mem_cons.1 ht with
    | inl e => exact e ▸ hu
    | inr hr =>
      exact ih (u :: seen) hrest (fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ hu)
        (hseen x)) t hr

/-- **Completeness.** Whatever occurs in an arrival-order trace is enactable. -/
theorem occurs_enactable {P : RoleProtocol} {w : List String} {t : String}
    (h : CausalTrace P w) (ht : t ∈ w) : enactable P t = true :=
  trace_enactable_aux P w [] h (fun _ hx => nomatch hx) t ht

/-- **Enactability is occurrence.** The checker accepts `t` exactly when `t` occurs in
    some run in which every message is justified on arrival. -/
theorem enactable_iff_occurs (P : RoleProtocol) (t : String) :
    enactable P t = true ↔ ∃ w, CausalTrace P w ∧ t ∈ w :=
  ⟨enactable_occurs, fun ⟨_, hw, ht⟩ => occurs_enactable hw ht⟩

/-- **The protocol check.** No step is reported exactly when one arrival-order trace
    contains every declared step. -/
theorem unenactableSteps_eq_nil_iff (P : RoleProtocol) :
    unenactableSteps P = [] ↔ ∃ w, CausalTrace P w ∧ ∀ t, t ∈ stepNames P → t ∈ w := by
  constructor
  · intro h
    obtain ⟨w, hw, hin⟩ := iter_trace P (stepNames P).length
    refine ⟨w, hw, fun t ht => ?_⟩
    have hne : ¬ (!enactable P t) = true := List.filter_eq_nil_iff.1 h t ht
    have he : enactable P t = true := by simpa using hne
    exact hin t (stepNames_relevant ht) he
  · intro ⟨w, hw, hall⟩
    refine List.filter_eq_nil_iff.2 (fun t ht => ?_)
    simp [occurs_enactable hw (hall t ht)]

/-! ## Acyclic protocols are enactable -/

/-- `x` is named by the predecessor declarations of the step `t`. -/
def dependsOn (P : RoleProtocol) (t x : String) : Prop :=
  ∃ st, P.find? (fun st => st.name == t) = some st ∧ x ∈ st.preds.flatMap clauseNames

/-- No degenerate clause list: every step is justified once everything has been seen.
    This excludes, for example, a step whose only declaration is an empty `(any)`. -/
def Satisfiable (P : RoleProtocol) : Prop := ∀ t, enabled P (fun _ => true) t = true

/-- **Acyclic protocols are enactable.** If the named-predecessor relation is
    well-founded and no clause list is degenerate, the checker accepts every
    performative. -/
theorem enactable_of_acyclic {P : RoleProtocol}
    (hwf : WellFounded (fun x t : String => dependsOn P t x)) (hsat : Satisfiable P)
    (t : String) : enactable P t = true := by
  refine hwf.induction (C := fun t => enactable P t = true) t ?_
  intro t ih
  cases hdecl : undeclared P t with
  | true => simp [enactable, hdecl]
  | false =>
    have hsat' : (table P).sat t
        ((table P).avail ((table P).iter (table P).perfs.length) t) = true := by
      show enabled P _ t = true
      have ht := hsat t
      unfold enabled at ht ⊢
      cases hf : P.find? (fun st => st.name == t) with
      | none => rfl
      | some st =>
        rw [hf] at ht
        show justified st.preds _ = true
        rw [← justified_congr (f := fun _ => true) (fun x hx => ?_)]
        · exact ht
        · have hx' : enactable P x = true := ih x ⟨st, hf, hx⟩
          have hrel : x ∈ relevantNames P := List.mem_append.2 (Or.inr
            (List.mem_flatMap.2 ⟨st, List.mem_of_find?_eq_some hf, hx⟩))
          simp only [enactable, Table.enactable, Bool.or_eq_true] at hx'
          have : seenOf P ((table P).avail ((table P).iter (table P).perfs.length) t) x
              = true := by
            simp only [seenOf, Table.avail, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq]
            exact hx'.elim Or.inl (fun h => Or.inr ⟨hrel, h⟩)
          exact this.symm
    have hE : (table P).enactable t = true :=
      (table P).enactable_of_sat (mem_stepNames_of_declared hdecl) rfl hsat'
    rw [enactable, hE]
    exact Bool.or_true _

/-- An acyclic, non-degenerate protocol has one trace containing every declared step. -/
theorem acyclic_one_trace {P : RoleProtocol}
    (hwf : WellFounded (fun x t : String => dependsOn P t x)) (hsat : Satisfiable P) :
    ∃ w, CausalTrace P w ∧ ∀ t, t ∈ stepNames P → t ∈ w :=
  (unenactableSteps_eq_nil_iff P).1 (List.filter_eq_nil_iff.2 (fun t _ => by
    simp [enactable_of_acyclic hwf hsat t]))

/-! ## Examples -/

namespace Examples

/-- The straight-line example of `R6DCFLPreservation.lean` passes. -/
theorem ex_enactable : unenactableSteps exProtocol = [] := by decide

/-- A fan-in: `z` needs both `x` and `y`. -/
def fanIn : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["B"], preds := [] },
    { name := "y", sender := "B", recips := ["A"], preds := [] },
    { name := "z", sender := "A", recips := ["B"], preds := [.allOf ["x", "y"]] } ]

theorem fanIn_enactable : unenactableSteps fanIn = [] := by decide

/-- A cycle with an exit: `x` may cite `begin` or `y`, and `y` cites `x`. -/
def cyclic : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["B"], preds := [.single "begin", .single "y"] },
    { name := "y", sender := "B", recips := ["A"], preds := [.single "x"] } ]

/-- Enactability does not imply acyclicity. -/
theorem cyclic_enactable : unenactableSteps cyclic = [] := by decide

/-- Two steps that wait on each other, with no exit. -/
def deadlock : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["B"], preds := [.single "y"] },
    { name := "y", sender := "B", recips := ["A"], preds := [.single "x"] } ]

theorem deadlock_unenactable : unenactableSteps deadlock = ["x", "y"] := by decide

/-- A step whose only declaration is an empty `(any)`: acyclic, never justified. -/
def emptyAny : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["B"], preds := [.anyOf []] } ]

theorem emptyAny_unenactable : unenactableSteps emptyAny = ["x"] := by decide

end Examples

end CBCL.DialectEnactability
