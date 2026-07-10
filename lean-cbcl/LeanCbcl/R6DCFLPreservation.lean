import LeanCbcl.Parser
import LeanCbcl.DialectParser

/-!
# DCFL Preservation at R6 (SPEC-014 / `proof.tex` Prop. dcfl)

Mechanises the two halves of the R6 DCFL story that were previously ADR/paper-level:

## Half 1 — Role-annotation syntax adds no grammar (ADR-600 / CON-600)

Exactly the `DCFLPreservation.lean` argument, applied to the R6 surface syntax:
the `(:roles …)` clause, the indexed-role form `(* name)`, the `:from`/`:to`
attributes, and the `(with-roles …)` wrapper are all built with the same
`SExpr.list`/`SExpr.atom` constructors as every other CBCL form, so they inhabit
the existing S-expression DCFL grammar (`IsSExpr`, universal via
`allSExpr_isSExpr`). Role checking is a post-parse operation on already-parsed
trees; the byte-level trust boundary (`cbcl-parser`) is unchanged.
`roles_dispatch_currently_unwired` documents that the Lean dialect parser routes
the `roles` keyword to its catch-all error branch (the keyword is not yet wired,
mirroring `shape_dispatch_currently_unwired`; the preservation argument does not
depend on it being wired).

## Half 2 — Local protocol trace languages are regular, hence DCFL (Prop. dcfl)

`proof.tex` Prop. dcfl claims: "Each local protocol's accepted language is
regular, hence DCFL; projection adds no recogniser." Previously recap-only.
Here it is mechanised at the safety level, over the v1 raw-edge regime
(SPEC-014 ADR-605 — no bystander splicing; projection keeps `:caused-by` raw):

* A role-annotated protocol is a finite list of steps (`RoleStep`: name, sender,
  recipients, and `NodeRef`-style predecessor clauses `Single`/`Any`/`All`,
  mirroring the Rust `Vec<NodeRef>`).
* Its **trace language** (`CausalTrace`) is the set of performative-name
  sequences in which every step is declared and its predecessor clauses are
  satisfied by the names already seen — the type-level shadow of the causal
  verifier consuming a thread in arrival order. Acceptance is safety-level
  (every step justified when it arrives); a completion-level acceptance would
  change only the accepting predicate on the same finite state space, not the
  machine class.
* **Regularity** (`causalTrace_regular`): a deterministic finite automaton
  recognises `CausalTrace P` exactly. Finiteness is explicit and self-contained
  (no mathlib): the machine (`FinDFA`) carries a finite list of states, with
  proofs that the start state is in the list and the transition function never
  leaves it. The state space is the canonical seen-set — a sublist of the
  protocol's declared names — plus one dead state; the reference verifier's
  unbounded state (an arbitrary consumed-name list) provably collapses onto it
  (`Sim`), because enabledness reads the seen names only through membership,
  and only declared names can ever be consumed.
* **Hence DCFL** (`causalTrace_isTraceDCFL`): regular ⊆ DCFL is formal, not a
  remark — `IsRegular.toTraceDCFL` wraps any finite automaton as a
  deterministic pushdown machine (`TracePDA`, the alphabet-generic sibling of
  `DetParser.DetParser`) that never touches its stack. (The repo's `IsDCFL` is
  over S-expression *message syntax*; protocol traces are a different alphabet,
  hence the trace-level witness.)
* **Projection adds no recogniser** (`projection_adds_no_recogniser`):
  `projectProtocol P r` (the steps `r` sends or receives — Def. run-proj, raw
  edges) is again a protocol, and its recogniser is *the same builder* applied
  to it — a definitional equality, not merely an isomorphism. Local
  verifiability needs no machinery beyond the finite automaton the global
  protocol already has.

The worked example is the review's straight-line witness (`x : A → B`,
`y : C → B` caused-by `x`): globally `[x, y]` is accepted and `[y, x]` rejected;
in `C`'s projection the trace `[y]` is rejected — the trace-level shadow of
`my_permanently_unknown` in `Projectability.lean`.

Axioms: `#print axioms` on every headline theorem reports at most
`propext, Classical.choice, Quot.sound` (audited in `AxiomAudit.lean`).
-/

namespace CBCL
namespace R6DCFLPreservation

/-! ## Half 1 — R6 surface syntax inhabits the existing DCFL grammar -/

/-- An indexed-role declaration `(* name)` (ADR-600: the paper's `name[*]`
    rendered inside the existing symbol alphabet — `[` is not a CBCL symbol
    character, `*` is). -/
def indexedRole (name : String) : SExpr :=
  .list [.atom (.symbol "*"), .atom (.symbol name)]

/-- A `(:roles decl…)` clause (CON-600): a wrapped keyword clause in the style
    of `(:resource-requirements …)`, carrying the role declarations. -/
def rolesClause (decls : List SExpr) : SExpr :=
  .list (.atom (.keyword "roles") :: decls)

/-- A `:from role` attribute pair as it appears inside a performative
    declaration. -/
def fromAttr (role : String) : List SExpr :=
  [.atom (.keyword "from"), .atom (.symbol role)]

/-- A `:to (role…)` attribute pair as it appears inside a performative
    declaration. -/
def toAttr (roles : List String) : List SExpr :=
  [.atom (.keyword "to"), .list (roles.map (fun r => .atom (.symbol r)))]

/-- A `(with-roles args…)` wrapper (ADR-603: the thread root's runtime carrier
    binding the cast). -/
def withRolesWrapper (args : List SExpr) : SExpr :=
  .list (.atom (.symbol "with-roles") :: args)

/-- **ADR-600, mechanised:** an indexed-role form is an `IsSExpr` — it is built
    from the existing constructors, so it introduces no new grammar shape. -/
theorem indexedRole_isSExpr (name : String) : IsSExpr (indexedRole name) :=
  allSExpr_isSExpr _

/-- **DCFL preservation under role annotations (CON-600, mechanised):** a
    `(:roles …)` clause inhabits the existing CBCL S-expression DCFL grammar.
    The role layer is therefore a post-parse predicate on already-parsed data,
    not a new recogniser — the same argument as REQ-209/REQ-225 for R5. -/
theorem dcfl_preserved_under_roles (decls : List SExpr) :
    IsSExpr (rolesClause decls) :=
  allSExpr_isSExpr _

/-- `:from` attribute pairs are ordinary S-expressions. -/
theorem fromAttr_isSExpr (role : String) : ∀ e ∈ fromAttr role, IsSExpr e :=
  fun e _ => allSExpr_isSExpr e

/-- `:to` attribute pairs are ordinary S-expressions. -/
theorem toAttr_isSExpr (roles : List String) : ∀ e ∈ toAttr roles, IsSExpr e :=
  fun e _ => allSExpr_isSExpr e

/-- **DCFL preservation under the cast wrapper:** a `(with-roles …)` wrapper
    inhabits the existing grammar. -/
theorem dcfl_preserved_under_with_roles (args : List SExpr) :
    IsSExpr (withRolesWrapper args) :=
  allSExpr_isSExpr _

/-- The Lean dialect parser does not currently have a wired branch for the
    `roles` keyword; `applyKeywordClause` routes `"roles"` through its
    catch-all error branch. This documents the current state honestly
    (mirroring `shape_dispatch_currently_unwired`): the dispatch is
    deterministic, and the DCFL preservation argument above does not depend on
    the keyword being wired — only on `(:roles …)` being a well-formed
    `SExpr`, which it is. -/
theorem roles_dispatch_currently_unwired
    (acc : DialectAccum) (vals : List SExpr) :
    applyKeywordClause acc "roles" vals
      = .error s!"unknown dialect clause: roles" := by
  unfold applyKeywordClause
  rfl

/-! ## Half 2, §1 — Finite automata with explicit finite state carriers

Self-contained (Lean core only): finiteness is an explicit list of states the
machine provably never leaves, in the style of `DetParser.IsDCFL`'s explicit
witnesses — no `Fintype`, no cardinality arithmetic. -/

/-- A deterministic finite automaton over alphabet `α` with state type `σ`,
    carrying its own finiteness certificate: an explicit state list containing
    the start state and closed under the transition function. -/
structure FinDFA (α σ : Type) where
  /-- Transition function. -/
  step : σ → α → σ
  /-- Start state. -/
  start : σ
  /-- Acceptance predicate on the final state. -/
  accept : σ → Bool
  /-- The finite state carrier. -/
  states : List σ
  /-- The start state lies in the carrier. -/
  start_mem : start ∈ states
  /-- The carrier is closed under transitions: the machine never leaves it. -/
  closed : ∀ s ∈ states, ∀ a, step s a ∈ states

/-- Run the automaton over a word and report acceptance. -/
def FinDFA.run {α σ : Type} (M : FinDFA α σ) (w : List α) : Bool :=
  M.accept (w.foldl M.step M.start)

/-- The machine never leaves its finite carrier along any word — the
    substance of the finiteness certificate. -/
theorem FinDFA.foldl_mem {α σ : Type} (M : FinDFA α σ) (w : List α)
    {s : σ} (hs : s ∈ M.states) : w.foldl M.step s ∈ M.states := by
  induction w generalizing s with
  | nil => exact hs
  | cons a rest ih => exact ih (M.closed s hs a)

/-- Witness that a trace language `L` is regular: a finite automaton
    recognising exactly `L` (the `IsDCFL` pattern, one level down the
    Chomsky hierarchy). -/
structure IsRegular (α σ : Type) (L : List α → Prop) where
  /-- The recognising finite automaton. -/
  M : FinDFA α σ
  /-- Soundness: every accepted word is in `L`. -/
  sound : ∀ w, M.run w = true → L w
  /-- Completeness: every word of `L` is accepted. -/
  complete : ∀ w, L w → M.run w = true

/-! ## Half 2, §2 — Trace-level DPDAs and regular ⊆ DCFL

`DetParser.DetParser` is `Token`-specific; `TracePDA` is its alphabet-generic
sibling, with the finiteness of control states and stack alphabet explicit.
`IsRegular.toTraceDCFL` is the textbook inclusion REG ⊆ DCFL, made formal:
wrap the finite automaton as a pushdown machine that never touches its
stack. -/

/-- A deterministic pushdown machine over alphabet `α`, control states `σ`,
    stack symbols `γ`, with explicit finite carriers for both. Transition and
    acceptance mirror `DetParser` (replace-top semantics). -/
structure TracePDA (α σ γ : Type) where
  /-- Transition: state, input, top-of-stack ↦ new state and symbols pushed. -/
  step : σ → α → Option γ → σ × List γ
  /-- Start state. -/
  start : σ
  /-- Initial stack. -/
  startStack : List γ
  /-- Acceptance on final state and stack. -/
  accept : σ → List γ → Bool
  /-- Finite control-state carrier. -/
  states : List σ
  /-- Finite stack alphabet. -/
  stackAlphabet : List γ
  /-- The start state lies in the carrier. -/
  start_mem : start ∈ states
  /-- The initial stack draws from the stack alphabet. -/
  startStack_sub : ∀ g ∈ startStack, g ∈ stackAlphabet
  /-- Control states are closed under transitions. -/
  states_closed : ∀ s ∈ states, ∀ (a : α) (g : Option γ), (step s a g).1 ∈ states
  /-- Pushed symbols draw from the stack alphabet. -/
  push_sub : ∀ s ∈ states, ∀ (a : α) (g : Option γ), ∀ x ∈ (step s a g).2, x ∈ stackAlphabet

/-- One transition: consult `step` on the top of stack, replace the top with
    the pushed symbols (as in `DetParser.runStep`). -/
def TracePDA.runStep {α σ γ : Type} (p : TracePDA α σ γ)
    (cfg : σ × List γ) (a : α) : σ × List γ :=
  let (s', push) := p.step cfg.1 a cfg.2.head?
  (s', push ++ cfg.2.drop 1)

/-- Run the machine over a word and report acceptance. -/
def TracePDA.run {α σ γ : Type} (p : TracePDA α σ γ) (w : List α) : Bool :=
  let final := w.foldl p.runStep (p.start, p.startStack)
  p.accept final.1 final.2

/-- Witness that a trace language is a DCFL: a `TracePDA` recognising exactly
    it (`IsDCFL`, at the trace alphabet). -/
structure IsTraceDCFL (α σ γ : Type) (L : List α → Prop) where
  /-- The recognising deterministic pushdown machine. -/
  pda : TracePDA α σ γ
  /-- Soundness: every accepted word is in `L`. -/
  sound : ∀ w, pda.run w = true → L w
  /-- Completeness: every word of `L` is accepted. -/
  complete : ∀ w, L w → pda.run w = true

/-- Wrap a finite automaton as a pushdown machine that never touches its
    stack: the stack alphabet is empty, the initial stack is empty, and no
    transition pushes. -/
def FinDFA.toPDA {α σ : Type} (M : FinDFA α σ) : TracePDA α σ Unit where
  step := fun s a _ => (M.step s a, [])
  start := M.start
  startStack := []
  accept := fun s _ => M.accept s
  states := M.states
  stackAlphabet := []
  start_mem := M.start_mem
  startStack_sub := by intro g hg; cases hg
  states_closed := fun s hs a _ => M.closed s hs a
  push_sub := by intro s _ a g x hx; cases hx

private theorem toPDA_foldl {α σ : Type} (M : FinDFA α σ) (w : List α) (s : σ) :
    w.foldl M.toPDA.runStep (s, []) = (w.foldl M.step s, []) := by
  induction w generalizing s with
  | nil => rfl
  | cons a rest ih => exact ih (M.step s a)

/-- The wrapped machine recognises the same language. -/
theorem FinDFA.toPDA_run {α σ : Type} (M : FinDFA α σ) (w : List α) :
    M.toPDA.run w = M.run w := by
  unfold TracePDA.run FinDFA.run
  rw [show M.toPDA.startStack = [] from rfl, show M.toPDA.start = M.start from rfl,
    toPDA_foldl]
  rfl

/-- **Regular ⊆ DCFL**, formal: any finite automaton is a deterministic
    pushdown machine that ignores its stack. -/
def IsRegular.toTraceDCFL {α σ : Type} {L : List α → Prop}
    (h : IsRegular α σ L) : IsTraceDCFL α σ Unit L where
  pda := h.M.toPDA
  sound := fun w hw => h.sound w ((h.M.toPDA_run w) ▸ hw)
  complete := fun w hw => (h.M.toPDA_run w).symm ▸ h.complete w hw

/-! ## Half 2, §3 — Role-annotated protocols and their trace language -/

/-- A predecessor clause, mirroring the Rust `NodeRef ∈ {Single | Any | All}`:
    evaluated against the set of performative names already seen. -/
inductive PredClause where
  /-- One named predecessor type must have been seen. -/
  | single : String → PredClause
  /-- At least one of the named types must have been seen (`(any …)`). -/
  | anyOf : List String → PredClause
  /-- All of the named types must have been seen (`(all …)`). -/
  | allOf : List String → PredClause
  deriving BEq, DecidableEq, Repr

/-- Evaluate a clause against a seen-set (as a Boolean membership function). -/
def PredClause.sat (seen : String → Bool) : PredClause → Bool
  | .single t => seen t
  | .anyOf ts => ts.any seen
  | .allOf ts => ts.all seen

/-- One role-annotated protocol step: a performative name, its sender role,
    its recipient roles, and its predecessor clauses (all must hold; `[]` is a
    root step, e.g. `begin`). -/
structure RoleStep where
  /-- The performative name. -/
  name : String
  /-- The declared sender role (`:from`). -/
  sender : String
  /-- The declared recipient roles (`:to`). -/
  recips : List String
  /-- The `:caused-by` clauses (the Rust `Vec<NodeRef>`; all must hold). -/
  preds : List PredClause
  deriving BEq, DecidableEq, Repr

/-- A role-annotated protocol: a finite list of steps. -/
abbrev RoleProtocol := List RoleStep

/-- The declared performative names of a protocol. -/
def stepNames (P : RoleProtocol) : List String := P.map (·.name)

/-- Step `t` is enabled given seen-set `seen`: it is declared, and every one of
    its predecessor clauses is satisfied. Undeclared names are never enabled. -/
def enabled (P : RoleProtocol) (seen : String → Bool) (t : String) : Bool :=
  match P.find? (fun st => st.name == t) with
  | none => false
  | some st => st.preds.all (·.sat seen)

/-- The reference verifier's transition: consume one performative name,
    recording it, or move to the dead state (`none`) if it is not enabled.
    The live state is the raw list of consumed names — an *unbounded* state
    space; the regularity theorem below is exactly the fact that it collapses
    onto a finite one. -/
def traceStep (P : RoleProtocol) : Option (List String) → String → Option (List String)
  | none, _ => none
  | some seen, t =>
    if enabled P (fun x => seen.contains x) t then some (t :: seen) else none

/-- **The causal trace language** of a protocol: the words in which every step
    is declared and causally justified by the names before it (safety level;
    prefix-closed by construction). -/
def CausalTrace (P : RoleProtocol) (w : List String) : Prop :=
  w.foldl (traceStep P) (some []) ≠ none

instance (P : RoleProtocol) (w : List String) : Decidable (CausalTrace P w) := by
  unfold CausalTrace; infer_instance

/-! ## Half 2, §4 — The subset automaton and the regularity theorem -/

private theorem contains_true_iff {l : List String} {x : String} :
    l.contains x = true ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons a as ih => simp

private theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem or_true_iff {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

/-- Enabled steps are declared. -/
private theorem enabled_mem_names {P : RoleProtocol} {f : String → Bool} {t : String}
    (h : enabled P f t = true) : t ∈ stepNames P := by
  unfold enabled at h
  cases hf : P.find? (fun st => st.name == t) with
  | none => rw [hf] at h; cases h
  | some st =>
    have hbeq := List.find?_some hf
    have hname : st.name = t := eq_of_beq hbeq
    exact hname ▸ List.mem_map.mpr ⟨st, List.mem_of_find?_eq_some hf, rfl⟩

/-- The automaton's transition: the live state is the *canonical* seen-set —
    the sublist of `stepNames P` (in declaration order, deduplicated by
    construction) of names seen so far — plus the dead state `none`. On input
    `t`, re-canonicalise by filtering the declared names. -/
def dfaStep (P : RoleProtocol) : Option (List String) → String → Option (List String)
  | none, _ => none
  | some c, t =>
    if enabled P (fun x => c.contains x) t then
      some ((stepNames P).filter (fun nm => nm == t || c.contains nm))
    else none

/-- All sublists of a list (the canonical finite enumeration of the automaton's
    live states). -/
def sublistsOf {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => sublistsOf xs ++ (sublistsOf xs).map (x :: ·)

private theorem mem_sublistsOf {α : Type} {l xs : List α} :
    l ∈ sublistsOf xs ↔ l.Sublist xs := by
  induction xs generalizing l with
  | nil =>
    simp only [sublistsOf, List.mem_singleton]
    constructor
    · rintro rfl; exact List.Sublist.refl []
    · intro h; exact List.sublist_nil.mp h
  | cons x xs ih =>
    simp only [sublistsOf, List.mem_append, List.mem_map]
    constructor
    · rintro (h1 | ⟨l', hl', rfl⟩)
      · exact (ih.mp h1).cons x
      · exact (ih.mp hl').cons₂ x
    · intro h
      cases h with
      | cons _ h' => exact Or.inl (ih.mpr h')
      | cons₂ _ h' => exact Or.inr ⟨_, ih.mpr h', rfl⟩

/-- **The recogniser.** States: the dead state plus the canonical seen-sets —
    the sublists of the protocol's declared names. Finitely many, explicitly
    enumerated, provably closed under `dfaStep`. -/
def traceDFA (P : RoleProtocol) : FinDFA String (Option (List String)) where
  step := dfaStep P
  start := some []
  accept := fun s => s.isSome
  states := none :: (sublistsOf (stepNames P)).map some
  start_mem := by
    exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr
      ⟨[], mem_sublistsOf.mpr (List.nil_sublist _), rfl⟩))
  closed := by
    intro s _ t
    match s with
    | none => exact List.mem_cons.mpr (Or.inl rfl)
    | some c =>
      simp only [dfaStep]
      split
      · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr
          ⟨_, mem_sublistsOf.mpr List.filter_sublist, rfl⟩))
      · exact List.mem_cons.mpr (Or.inl rfl)

/-- The state-collapse simulation: the reference verifier's raw consumed-name
    list and the automaton's canonical seen-set agree on membership (and dead
    states pair with dead states). Consumed names are always declared. -/
inductive Sim (P : RoleProtocol) : Option (List String) → Option (List String) → Prop where
  /-- Dead pairs with dead. -/
  | dead : Sim P none none
  /-- Live pairs with live: same membership, all names declared. -/
  | live : ∀ (seen c : List String),
      (∀ x ∈ seen, x ∈ stepNames P) →
      (∀ x, x ∈ c ↔ x ∈ seen) →
      Sim P (some seen) (some c)

private theorem sim_step {P : RoleProtocol} {st ms : Option (List String)}
    (h : Sim P st ms) (t : String) :
    Sim P (traceStep P st t) (dfaStep P ms t) := by
  cases h with
  | dead => exact .dead
  | live seen c hsub hmem =>
    have hfun : (fun x => c.contains x) = (fun x => seen.contains x) := by
      funext x
      exact bool_eq_of_iff (by rw [contains_true_iff, contains_true_iff]; exact hmem x)
    simp only [traceStep, dfaStep, hfun]
    split
    · next hen =>
      refine .live _ _ ?_ ?_
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact enabled_mem_names hen
        · exact hsub x hx'
      · intro x
        rw [List.mem_filter, List.mem_cons]
        constructor
        · rintro ⟨-, hp⟩
          rcases or_true_iff.mp hp with hbeq | hc
          · exact Or.inl (eq_of_beq hbeq)
          · exact Or.inr ((hmem x).mp (contains_true_iff.mp hc))
        · rintro (rfl | hx)
          · exact ⟨enabled_mem_names hen, or_true_iff.mpr (Or.inl (beq_self_eq_true x))⟩
          · exact ⟨hsub x hx,
              or_true_iff.mpr (Or.inr (contains_true_iff.mpr ((hmem x).mpr hx)))⟩
    · exact .dead

private theorem sim_foldl {P : RoleProtocol} {st ms : Option (List String)}
    (h : Sim P st ms) (w : List String) :
    Sim P (w.foldl (traceStep P) st) (w.foldl (dfaStep P) ms) := by
  induction w generalizing st ms with
  | nil => exact h
  | cons t rest ih => exact ih (sim_step h t)

private theorem Sim.agree {P : RoleProtocol} {a b : Option (List String)}
    (h : Sim P a b) : (a ≠ none) ↔ (b.isSome = true) := by
  cases h <;> simp

/-- The automaton recognises exactly the causal trace language. -/
theorem causalTrace_iff_run (P : RoleProtocol) (w : List String) :
    CausalTrace P w ↔ (traceDFA P).run w = true := by
  have hinit : Sim P (some []) (some []) :=
    .live [] [] (by intro x hx; cases hx) (fun _ => Iff.rfl)
  have hsim := sim_foldl hinit w
  unfold CausalTrace FinDFA.run
  exact hsim.agree

/-- **`prop:dcfl`, regularity (global form):** the causal trace language of a
    role-annotated protocol is regular — recognised exactly by the explicit
    finite automaton `traceDFA P`, whose states are the sublists of the
    protocol's declared names plus a dead state. -/
def causalTrace_regular (P : RoleProtocol) :
    IsRegular String (Option (List String)) (CausalTrace P) where
  M := traceDFA P
  sound := fun w h => (causalTrace_iff_run P w).mpr h
  complete := fun w h => (causalTrace_iff_run P w).mp h

/-- **`prop:dcfl`, "hence DCFL":** the causal trace language is a trace-level
    DCFL — the finite automaton, wrapped as a pushdown machine that never
    touches its stack (`IsRegular.toTraceDCFL`). -/
def causalTrace_isTraceDCFL (P : RoleProtocol) :
    IsTraceDCFL String (Option (List String)) Unit (CausalTrace P) :=
  (causalTrace_regular P).toTraceDCFL

/-! ## Half 2, §5 — Projection adds no recogniser -/

/-- A step is `r`-relevant: `r` sends or receives it. -/
def RoleStep.relevant (st : RoleStep) (r : String) : Bool :=
  st.sender == r || st.recips.contains r

/-- **Run projection at the protocol level** (v1 raw-edge regime, ADR-605):
    keep exactly the steps `r` sends or receives, `:caused-by` clauses kept
    raw — no splicing. The projection of a protocol is again a protocol. -/
def projectProtocol (P : RoleProtocol) (r : String) : RoleProtocol :=
  P.filter (·.relevant r)

/-- **`prop:dcfl`, local form:** each local protocol's trace language is
    regular — the projection is a protocol, so the *same* construction
    recognises it. -/
def localTrace_regular (P : RoleProtocol) (r : String) :
    IsRegular String (Option (List String)) (CausalTrace (projectProtocol P r)) :=
  causalTrace_regular (projectProtocol P r)

/-- Each local trace language is a trace-level DCFL. -/
def localTrace_isTraceDCFL (P : RoleProtocol) (r : String) :
    IsTraceDCFL String (Option (List String)) Unit (CausalTrace (projectProtocol P r)) :=
  causalTrace_isTraceDCFL (projectProtocol P r)

/-- **`prop:dcfl`, "projection adds no recogniser" — definitionally.** The
    recogniser of a local protocol *is* the global builder applied to the
    projected step list: same automaton family, same state discipline, no new
    machine class. This is `rfl`, not an isomorphism. -/
theorem projection_adds_no_recogniser (P : RoleProtocol) (r : String) :
    (localTrace_regular P r).M = traceDFA (projectProtocol P r) :=
  rfl

/-! ## Worked example — the review's straight-line witness at trace level

`x : A → B` (root), `y : C → B` caused by `x`. Globally `[x, y]` is a causal
trace and `[y, x]` is not; role `C`'s projection contains only `y`, whose
clause demands the never-projected `x` — so `[y]` is not a local trace: the
trace-language shadow of `my_permanently_unknown` (`Projectability.lean`). -/

/-- The straight-line example protocol. -/
def exProtocol : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["B"], preds := [] },
    { name := "y", sender := "C", recips := ["B"], preds := [.single "x"] } ]

/-- Globally, `[x, y]` is accepted. -/
theorem ex_trace_ok : CausalTrace exProtocol ["x", "y"] := by decide

/-- Globally, the out-of-order `[y, x]` is rejected. -/
theorem ex_trace_out_of_order : ¬ CausalTrace exProtocol ["y", "x"] := by decide

/-- Locally at `C`, even `[y]` is rejected: the justifying `x` is not
    `C`-relevant, so no local trace ever enables `y`. -/
theorem ex_local_permanently_stuck :
    ¬ CausalTrace (projectProtocol exProtocol "C") ["y"] := by decide

/-! Axiom audit (informational output when this file is compiled). -/
#print axioms dcfl_preserved_under_roles
#print axioms roles_dispatch_currently_unwired
#print axioms causalTrace_iff_run
#print axioms causalTrace_regular
#print axioms causalTrace_isTraceDCFL
#print axioms localTrace_regular
#print axioms projection_adds_no_recogniser
#print axioms ex_local_permanently_stuck

end R6DCFLPreservation
end CBCL
