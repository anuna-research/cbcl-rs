import LeanCbcl.Parser
import LeanCbcl.DialectParser

/-!
# DCFL Preservation at R6 (SPEC-014 / `proof.tex` Prop. dcfl)

Mechanises the two halves of the R6 DCFL story that were previously ADR/paper-level.
This is the post-review revision: the transition semantics now follows the deployed
verifier (`crates/cbcl-core/src/protocol.rs::verify_causal`) branch by branch, and the
places where the model still idealises are disclosed here, not discovered by readers.

## Half 1 — Role-annotation syntax adds no grammar (ADR-600 / CON-600)

The `(:roles (…))` clause, the indexed-role form `(* name)`, the `:from`/`:to`
attributes, and the `(with-roles …)` wrapper are built with the same
`SExpr.list`/`SExpr.atom` constructors as every other CBCL form, so they inhabit the
existing S-expression DCFL grammar. **Honesty note:** `IsSExpr` is universal on `SExpr`
(`allSExpr_isSExpr` — a truism, exactly as in the R5 file `DCFLPreservation.lean`), so
these theorems pin the *constructors used* — the argument that role checking is a
post-parse operation on already-parsed trees — and do NOT verify the CON-600 clause
shape; that shape is enforced by `role.rs::parse_roles` and its property tests. The
constructors below do transcribe CON-600 faithfully (in particular `rolesClause` takes
its declarations as one inner list with at least one declaration, as the grammar
requires). `roles_dispatch_currently_unwired` documents that the Lean dialect parser
routes the `roles` keyword to its catch-all error branch (mirroring
`shape_dispatch_currently_unwired`).

## Half 2 — Protocol trace languages are regular, hence DCFL (Prop. dcfl)

`proof.tex` Prop. dcfl claims: "Each local protocol's accepted language is regular,
hence DCFL; projection adds no recogniser." Mechanised here over the v1 raw-edge
regime (SPEC-014 ADR-605 — no bystander splicing; `:caused-by` clauses kept raw).

### The verifier semantics, faithfully

A step's predecessor declarations (`preds : List PredClause`, mirroring the Rust
`Vec<NodeRef>` with `Single`/`Any`/`All`) are read the way `verify_causal` reads them —
**disjunctively across citation routes**, not conjunctively:

* *no-citation route*: a step with no declared predecessors is a root — always
  justified (`verify_causal`: `CausedBy = None` is `Valid` iff no predecessors);
* *literal-begin route*: `:caused-by begin` is `Valid` — with no store lookup —
  iff `"begin"` appears in the pooled `Single`/`Any` names (`BEGIN_KEYWORD` branch);
* *single-citation route*: citing one predecessor is `Valid` iff its type is **any**
  member of the pooled `Single`/`Any` names — `[Single a, Single b]` means `a ∨ b`
  (`protocol.rs` doc on `check_step_uniqueness`; `allowed_single_predecessors`);
* *fan-in route*: citing multiple predecessors is `Valid` iff the **first** `(all …)`
  declaration is completely covered by seen types (`find_map` in the
  `CausedBy::Multiple` branch — later `All` declarations are dead code in Rust too);
* *undeclared performatives are unconstrained*: a name with no step declaration is
  `Valid` (`protocol.steps.get = None ⇒ Valid`).

A word is in the language iff each occurrence admits **some** valid citation route —
the citation shape itself is below the name-level alphabet and existentially
quantified.

### Two acceptance regimes, and which one is the deployed language

* `CausalTrace P w` — the **arrival-order** language: every step justified by the
  names seen *before it*. This is the language of causal-order delivery schedules.
* `StoreTrace P w` — the **store** language: every step justified by the *completed*
  word. This is the deployed verifier's accepted language: verdicts are valid-sticky
  (out-of-order arrival is `Unknown`, never `Violation`, then `Valid` once the
  predecessor arrives — `projection.rs::out_of_order_is_unknown_then_valid`,
  ADR-602), so a thread is accepted iff every message is eventually `Valid` against
  the full store — which is order-free, exactly `StoreTrace`.
* `causalTrace_storeTrace`: `CausalTrace P w → StoreTrace P w` — arrival-order
  justification implies store justification (justification is monotone in the seen
  set). `ex_out_of_order_store` shows the inclusion is strict.

Both languages are **regular** (`causalTrace_regular`, `storeTrace_regular`): the
reference verifier's state — an arbitrary-length consumed-name list — provably
collapses (`Sim` / `store_foldl_inv`) onto the canonical seen-set, a sublist of the
finitely many *relevant* names (declared step names plus every name mentioned in any
clause), because justification reads the past only through membership of relevant
names. Finiteness is explicit and self-contained (no mathlib): `FinDFA` carries a
finite state list with a start-membership proof and transition closure.
**Hence DCFL** is formal (`IsRegular.toTraceDCFL`): the automaton wrapped as a
deterministic pushdown machine (`TracePDA`, the alphabet-generic sibling of
`DetParser`) that never touches its stack. (The repo's `IsDCFL` is over S-expression
*message syntax*; protocol traces are a different alphabet, hence the trace-level
witness.)

### Projection — and what `projection_adds_no_recogniser` does and does not say

`projectProtocol P r` keeps the steps `r` sends or receives, clauses raw — the
*paper's* protocol projection in the raw-edge regime (Def. proj minus the splice,
which ADR-605 defers). Note the **shipped** composition is different: per ADR-604 the
deployed `verify_causal_for_role` always runs against the *global* dialect-level
protocol; the step-filtered local protocol is the paper's object.
`localTrace_regular`/`localStoreTrace_regular` are instances of the global theorems
at the projected protocol, and `projection_adds_no_recogniser` records that the local
recogniser **is** the same builder applied to the projected steps — a definitional
equality (`rfl`), true by construction. Its mathematical content is only that the
protocol class is closed under projection so one recogniser family serves globally
and locally; it does not (and cannot) validate `projectProtocol` itself. The
substantive local claim is the regularity instance.

### Remaining idealisations (disclosed)

* **Duplicate step names**: `enabled` resolves a name by `find?` (first declaration
  wins; later duplicates are shadowed, order-sensitively). In Rust this situation is
  inexpressible — `CausalProtocol.steps` is a `BTreeMap`, multiple `(then …)` clauses
  on one target merge into one `StepDecl`, and literal duplicates are R5
  `DuplicateStep` violations. The model is faithful on the deduplicated protocols the
  system actually admits.
* **`begin`** is modelled as an ordinary name for pool-matching (root typing,
  ADR-603) plus the literal-citation route above; the root wrapper itself is a
  root step (`preds = []`).
* Acceptance is safety-level (`Valid`-ness of every message); a completion-level
  acceptance would change only the accepting predicate on the same finite state
  space, not the machine class.

The worked examples: the `protocol.rs` doc's own `a ∨ b` pool example
(`ex_pool_is_disjunctive`); out-of-order arrival rejected causally but accepted at
the store — the Unknown-then-Valid shadow (`ex_out_of_order_store`); a fan-in needing
its full `(all …)` set; and the review's straight-line witness: in `C`'s projection
even the *completed store* never justifies `y` (`ex_local_permanently_stuck`) — the
trace shadow of `my_permanently_unknown` (`Projectability.lean`).

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

/-- A `(:roles (decl decls…))` clause, transcribing CON-600: a wrapped keyword
    clause whose *value is one inner list* of at least one role declaration
    (`role.rs::parse_roles` rejects `(:roles ())` and non-list values; the
    `decl :: decls` shape carries the ≥1 requirement here). -/
def rolesClause (decl : SExpr) (decls : List SExpr) : SExpr :=
  .list [.atom (.keyword "roles"), .list (decl :: decls)]

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

/-- The indexed-role form is built from the existing constructors — no new
    grammar shape. (Typechecking-level: `IsSExpr` is universal, so this pins
    the constructors used, not the clause shape — see the header note.) -/
theorem indexedRole_isSExpr (name : String) : IsSExpr (indexedRole name) :=
  allSExpr_isSExpr _

/-- **DCFL preservation under role annotations** (the ADR-600/CON-600
    *argument*, at typechecking level): a `(:roles (…))` clause inhabits the
    existing CBCL S-expression DCFL grammar, so the role layer is a post-parse
    predicate on already-parsed data, not a new recogniser — the same argument
    as REQ-209/REQ-225 for R5. `IsSExpr` is universal, so this does not check
    the CON-600 shape itself (that is `role.rs` + property tests); it records
    that the surface forms live inside the grammar the DPDA already accepts. -/
theorem dcfl_preserved_under_roles (decl : SExpr) (decls : List SExpr) :
    IsSExpr (rolesClause decl decls) :=
  allSExpr_isSExpr _

/-- `:from` attribute pairs are ordinary S-expressions (typechecking-level). -/
theorem fromAttr_isSExpr (role : String) : ∀ e ∈ fromAttr role, IsSExpr e := by
  intro e he
  simp only [fromAttr, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact allSExpr_isSExpr _

/-- `:to` attribute pairs are ordinary S-expressions (typechecking-level). -/
theorem toAttr_isSExpr (roles : List String) : ∀ e ∈ toAttr roles, IsSExpr e := by
  intro e he
  simp only [toAttr, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact allSExpr_isSExpr _

/-- The `(with-roles …)` wrapper inhabits the existing grammar
    (typechecking-level). -/
theorem dcfl_preserved_under_with_roles (args : List SExpr) :
    IsSExpr (withRolesWrapper args) :=
  allSExpr_isSExpr _

/-- The Lean dialect parser does not currently have a wired branch for the
    `roles` keyword; `applyKeywordClause` routes `"roles"` through its
    catch-all error branch. This documents the current state honestly
    (mirroring `shape_dispatch_currently_unwired`): the dispatch is
    deterministic, and the DCFL preservation argument above does not depend on
    the keyword being wired. -/
theorem roles_dispatch_currently_unwired
    (acc : DialectAccum) (vals : List SExpr) :
    applyKeywordClause acc "roles" vals
      = .error s!"unknown dialect clause: roles" := by
  unfold applyKeywordClause
  rfl

/-! ## Half 2, §1 — Finite automata with explicit finite state carriers

Self-contained (Lean core only): finiteness is an explicit list of states the
machine provably never leaves — no `Fintype`, no cardinality arithmetic. -/

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

/-! ## Half 2, §3 — Role-annotated protocols and the verifier's justification -/

/-- A predecessor clause, mirroring the Rust `NodeRef ∈ {Single | Any | All}`. -/
inductive PredClause where
  /-- One named predecessor type (`NodeRef::Single`). -/
  | single : String → PredClause
  /-- A set of alternatives (`NodeRef::Any`). -/
  | anyOf : List String → PredClause
  /-- A fan-in set (`NodeRef::All`); consulted only by the fan-in citation
      route, as in `verify_causal`. -/
  | allOf : List String → PredClause
  deriving BEq, DecidableEq, Repr

/-- The names a clause mentions (for the finite relevant-name universe). -/
def clauseNames : PredClause → List String
  | .single t => [t]
  | .anyOf ts => ts
  | .allOf ts => ts

/-- The pooled `Single`/`Any` names — the types acceptable to a
    single-message citation (`allowed_single_predecessors` in `protocol.rs`;
    `All` is excluded there too). -/
def pooledNames (preds : List PredClause) : List String :=
  preds.flatMap fun c =>
    match c with
    | .single t => [t]
    | .anyOf ts => ts
    | .allOf _ => []

/-- The `(all …)` declarations, in order (`verify_causal` consults only the
    first — `find_map` — so later ones are dead in Rust as well). -/
def fanInDecls (preds : List PredClause) : List (List String) :=
  preds.filterMap fun c =>
    match c with
    | .allOf ts => some ts
    | _ => none

/-- **Justification, following `verify_causal` route by route** (disjunction
    of citation routes — NOT a conjunction over the clause list):
    root (no declared predecessors) / literal `:caused-by begin` (store-free) /
    single citation into the pooled `Single`/`Any` names / fan-in covering the
    first `(all …)` declaration. -/
def justified (preds : List PredClause) (seen : String → Bool) : Bool :=
  preds.isEmpty
    || (pooledNames preds).contains "begin"
    || (pooledNames preds).any seen
    || (match fanInDecls preds with
        | [] => false
        | g :: _ => g.all seen)

/-- One role-annotated protocol step: a performative name, its sender role,
    its recipient roles, and its predecessor declarations. -/
structure RoleStep where
  /-- The performative name. -/
  name : String
  /-- The declared sender role (`:from`). -/
  sender : String
  /-- The declared recipient roles (`:to`). -/
  recips : List String
  /-- The predecessor declarations (the Rust `Vec<NodeRef>`), read
      disjunctively across citation routes by `justified`. -/
  preds : List PredClause
  deriving BEq, DecidableEq, Repr

-- The derived record printer does not use precedence; suppress only this
-- generated argument, as for the other record Repr instances in the model.
attribute [nolint unusedArguments] instReprRoleStep.repr

/-- A role-annotated protocol: a finite list of steps. (Rust's
    `CausalProtocol.steps` is a `BTreeMap`, so duplicate names are
    inexpressible there; here `find?` resolves a name to its first
    declaration — see the header's duplicate-names note.) -/
abbrev RoleProtocol := List RoleStep

/-- The declared performative names of a protocol. -/
def stepNames (P : RoleProtocol) : List String := P.map (·.name)

/-- The finite name universe the verdict can ever read: declared step names
    plus every name mentioned in any clause (clause names may be undeclared,
    and an undeclared name — once seen — can still justify a pool member). -/
def relevantNames (P : RoleProtocol) : List String :=
  stepNames P ++ P.flatMap (fun st => st.preds.flatMap clauseNames)

/-- Step `t` is enabled given seen-set `seen`. Undeclared performatives are
    **unconstrained** — `Valid`, as in `verify_causal`
    (`protocol.steps.get = None ⇒ Valid`). -/
def enabled (P : RoleProtocol) (seen : String → Bool) (t : String) : Bool :=
  match P.find? (fun st => st.name == t) with
  | none => true
  | some st => justified st.preds seen

/-! ### Congruence and monotonicity: the verdict reads the past only through
membership of relevant names, and justification only grows with the seen set. -/

private theorem contains_true_iff {l : List String} {x : String} :
    l.contains x = true ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons a as ih => simp

private theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem or_true_iff {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

private theorem any_congr {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

private theorem all_congr {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

private theorem pooled_subset {preds : List PredClause} {x : String}
    (hx : x ∈ pooledNames preds) : x ∈ preds.flatMap clauseNames := by
  unfold pooledNames at hx
  rw [List.mem_flatMap] at hx ⊢
  obtain ⟨c, hc, hxc⟩ := hx
  refine ⟨c, hc, ?_⟩
  cases c <;> simp_all [clauseNames]

private theorem fanIn_subset {preds : List PredClause} {g : List String} {x : String}
    (hg : g ∈ fanInDecls preds) (hx : x ∈ g) : x ∈ preds.flatMap clauseNames := by
  unfold fanInDecls at hg
  rw [List.mem_filterMap] at hg
  obtain ⟨c, hc, hcg⟩ := hg
  rw [List.mem_flatMap]
  refine ⟨c, hc, ?_⟩
  cases c <;> simp_all [clauseNames]

private theorem justified_congr {preds : List PredClause} {f g : String → Bool}
    (h : ∀ x ∈ preds.flatMap clauseNames, f x = g x) :
    justified preds f = justified preds g := by
  unfold justified
  have hpool : (pooledNames preds).any f = (pooledNames preds).any g :=
    any_congr fun x hx => h x (pooled_subset hx)
  have hfan : (match fanInDecls preds with
      | [] => false
      | grp :: _ => grp.all f)
      = (match fanInDecls preds with
      | [] => false
      | grp :: _ => grp.all g) := by
    cases hfd : fanInDecls preds with
    | nil => rfl
    | cons grp rest =>
      exact all_congr fun x hx =>
        h x (fanIn_subset (by rw [hfd]; exact List.mem_cons_self) hx)
  rw [hpool, hfan]

private theorem enabled_congr {P : RoleProtocol} {f g : String → Bool}
    (h : ∀ x ∈ relevantNames P, f x = g x) (t : String) :
    enabled P f t = enabled P g t := by
  unfold enabled
  cases hf : P.find? (fun st => st.name == t) with
  | none => rfl
  | some st =>
    exact justified_congr fun x hx =>
      h x (List.mem_append.mpr (Or.inr
        (List.mem_flatMap.mpr ⟨st, List.mem_of_find?_eq_some hf, hx⟩)))

private theorem enabled_of_undeclared {P : RoleProtocol} {f : String → Bool} {t : String}
    (h : t ∉ stepNames P) : enabled P f t = true := by
  unfold enabled
  cases hf : P.find? (fun st => st.name == t) with
  | none => rfl
  | some st =>
    have hbeq := List.find?_some hf
    have hname : st.name = t := eq_of_beq hbeq
    exact absurd (hname ▸ List.mem_map.mpr ⟨st, List.mem_of_find?_eq_some hf, rfl⟩) h

private theorem any_mono {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = true → g x = true) (hf : l.any f = true) : l.any g = true := by
  rw [List.any_eq_true] at hf ⊢
  obtain ⟨x, hx, hfx⟩ := hf
  exact ⟨x, hx, h x hx hfx⟩

private theorem all_mono {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = true → g x = true) (hf : l.all f = true) : l.all g = true := by
  rw [List.all_eq_true] at hf ⊢
  exact fun x hx => h x hx (hf x hx)

private theorem justified_mono {preds : List PredClause} {f g : String → Bool}
    (h : ∀ x, f x = true → g x = true) (hj : justified preds f = true) :
    justified preds g = true := by
  unfold justified at hj ⊢
  rcases or_true_iff.mp hj with h1 | hfan
  · rcases or_true_iff.mp h1 with h2 | hany
    · exact or_true_iff.mpr (Or.inl (or_true_iff.mpr (Or.inl h2)))
    · exact or_true_iff.mpr (Or.inl (or_true_iff.mpr
        (Or.inr (any_mono (fun x _ => h x) hany))))
  · refine or_true_iff.mpr (Or.inr ?_)
    cases hfd : fanInDecls preds with
    | nil =>
      rw [hfd] at hfan
      exact Bool.noConfusion hfan
    | cons grp rest =>
      rw [hfd] at hfan
      exact all_mono (fun x _ => h x) hfan

private theorem enabled_mono {P : RoleProtocol} {f g : String → Bool}
    (h : ∀ x, f x = true → g x = true) {t : String}
    (ht : enabled P f t = true) : enabled P g t = true := by
  unfold enabled at ht ⊢
  cases hf : P.find? (fun st => st.name == t) with
  | none => rfl
  | some st =>
    rw [hf] at ht
    exact justified_mono h ht

/-! ## Half 2, §4 — The two acceptance regimes -/

/-- The reference verifier's arrival-order transition: consume one
    performative name if it is justified by what came before, else move to the
    dead state. The live state is the raw list of consumed names — an
    *unbounded* state space; the regularity theorem is exactly the fact that
    it collapses onto a finite one. -/
def traceStep (P : RoleProtocol) : Option (List String) → String → Option (List String)
  | none, _ => none
  | some seen, t =>
    if enabled P (fun x => seen.contains x) t then some (t :: seen) else none

/-- **The arrival-order (causal-order) trace language**: every step justified
    by the names seen strictly before it. This is the language of causal-order
    delivery schedules — NOT the deployed verifier's accepted language, which
    is order-free (`StoreTrace`; see `causalTrace_storeTrace`). -/
def CausalTrace (P : RoleProtocol) (w : List String) : Prop :=
  w.foldl (traceStep P) (some []) ≠ none

instance (P : RoleProtocol) (w : List String) : Decidable (CausalTrace P w) := by
  unfold CausalTrace; infer_instance

/-- **The store (deployed) trace language**: every step justified by the
    *completed* word. Under the valid-sticky lattice (ADR-602: out-of-order
    arrival is `Unknown` then `Valid`, never `Violation`), a thread is
    accepted iff every message is eventually `Valid` against the full store —
    which is order-free: exactly this language. -/
def StoreTrace (P : RoleProtocol) (w : List String) : Prop :=
  ∀ t ∈ w, enabled P (fun x => w.contains x) t = true

instance (P : RoleProtocol) (w : List String) : Decidable (StoreTrace P w) := by
  unfold StoreTrace; infer_instance

private theorem foldl_traceStep_none {P : RoleProtocol} (w : List String) :
    w.foldl (traceStep P) none = none := by
  induction w with
  | nil => rfl
  | cons t rest ih => exact ih

private theorem causal_steps_enabled {P : RoleProtocol} :
    ∀ (w seen : List String), w.foldl (traceStep P) (some seen) ≠ none →
      ∀ t ∈ w, enabled P (fun x => (seen ++ w).contains x) t = true := by
  intro w
  induction w with
  | nil => intro seen _ t ht; cases ht
  | cons u rest ih =>
    intro seen hfold t ht
    cases hen : enabled P (fun x => seen.contains x) u with
    | false =>
      exfalso
      have hts : traceStep P (some seen) u = none := by
        simp only [traceStep, hen]
        simp
      simp only [List.foldl_cons, hts] at hfold
      exact hfold (foldl_traceStep_none rest)
    | true =>
      have hts : traceStep P (some seen) u = some (u :: seen) := by
        simp only [traceStep, hen]
        simp
      have hfold' : rest.foldl (traceStep P) (some (u :: seen)) ≠ none := by
        simpa only [List.foldl_cons, hts] using hfold
      rcases List.mem_cons.mp ht with rfl | htr
      · refine enabled_mono ?_ hen
        intro x hx
        rw [contains_true_iff] at hx ⊢
        exact List.mem_append.mpr (Or.inl hx)
      · refine enabled_mono ?_ (ih (u :: seen) hfold' t htr)
        intro x hx
        rw [contains_true_iff] at hx ⊢
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        rcases hx with (rfl | hxs) | hxr
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hxs
        · exact Or.inr (Or.inr hxr)

/-- **Arrival-order acceptance implies store acceptance**: justification is
    monotone in the seen set, so a word whose every step is justified on
    arrival is justified at the completed store. The converse fails
    (`ex_out_of_order_store`): the store language also contains the
    out-of-order deliveries the valid-sticky verdicts tolerate. -/
theorem causalTrace_storeTrace {P : RoleProtocol} {w : List String}
    (h : CausalTrace P w) : StoreTrace P w := by
  intro t ht
  have := causal_steps_enabled w [] h t ht
  simpa using this

/-! ## Half 2, §5 — The subset automata and the regularity theorems -/

/-- The shared canonical state update: re-filter the relevant names by "seen
    before, or is the arriving name". The canonical state is always a sublist
    of `relevantNames P` — the finite carrier. -/
def storeStep (P : RoleProtocol) (c : List String) (t : String) : List String :=
  (relevantNames P).filter (fun nm => nm == t || c.contains nm)

/-- Arrival-order transition on canonical states (dead state `none`). -/
def dfaStep (P : RoleProtocol) : Option (List String) → String → Option (List String)
  | none, _ => none
  | some c, t =>
    if enabled P (fun x => c.contains x) t then some (storeStep P c t) else none

/-- All sublists of a list (the canonical finite enumeration of the automata's
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

/-- **The arrival-order recogniser.** States: the dead state plus the
    canonical seen-sets — sublists of the protocol's relevant names. -/
def traceDFA (P : RoleProtocol) : FinDFA String (Option (List String)) where
  step := dfaStep P
  start := some []
  accept := fun s => s.isSome
  states := none :: (sublistsOf (relevantNames P)).map some
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

/-- The state-collapse simulation for the arrival-order regime: the raw
    consumed-name list and the canonical seen-set agree on membership of every
    *relevant* name (dead pairs with dead). Nothing else about the past is
    readable by `enabled` (`enabled_congr`), so nothing else needs tracking. -/
inductive Sim (P : RoleProtocol) : Option (List String) → Option (List String) → Prop where
  /-- Dead pairs with dead. -/
  | dead : Sim P none none
  /-- Live pairs with live: same membership on the relevant names. -/
  | live : ∀ (seen c : List String),
      (∀ x ∈ relevantNames P, (x ∈ c ↔ x ∈ seen)) →
      Sim P (some seen) (some c)

private theorem sim_step {P : RoleProtocol} {st ms : Option (List String)}
    (h : Sim P st ms) (t : String) :
    Sim P (traceStep P st t) (dfaStep P ms t) := by
  cases h with
  | dead => exact .dead
  | live seen c hmem =>
    have hcond : enabled P (fun x => c.contains x) t
        = enabled P (fun x => seen.contains x) t :=
      enabled_congr (fun x hx => bool_eq_of_iff
        (by rw [contains_true_iff, contains_true_iff]; exact hmem x hx)) t
    simp only [traceStep, dfaStep, hcond]
    split
    · refine .live _ _ ?_
      intro x hxrel
      simp only [storeStep]
      rw [List.mem_filter, List.mem_cons]
      constructor
      · rintro ⟨-, hp⟩
        rcases or_true_iff.mp hp with hbeq | hc
        · exact Or.inl (eq_of_beq hbeq)
        · exact Or.inr ((hmem x hxrel).mp (contains_true_iff.mp hc))
      · rintro (rfl | hx)
        · exact ⟨hxrel, or_true_iff.mpr (Or.inl (beq_self_eq_true x))⟩
        · exact ⟨hxrel,
            or_true_iff.mpr (Or.inr (contains_true_iff.mpr ((hmem x hxrel).mpr hx)))⟩
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

/-- The arrival-order automaton recognises exactly `CausalTrace`. -/
theorem causalTrace_iff_run (P : RoleProtocol) (w : List String) :
    CausalTrace P w ↔ (traceDFA P).run w = true := by
  have hinit : Sim P (some []) (some []) := .live [] [] (fun _ _ => Iff.rfl)
  have hsim := sim_foldl hinit w
  unfold CausalTrace FinDFA.run
  exact hsim.agree

/-- **`prop:dcfl`, regularity (arrival-order form):** the causal-order trace
    language of a role-annotated protocol is regular — recognised exactly by
    the explicit finite automaton `traceDFA P`. -/
def causalTrace_regular (P : RoleProtocol) :
    IsRegular String (Option (List String)) (CausalTrace P) where
  M := traceDFA P
  sound := fun w h => (causalTrace_iff_run P w).mpr h
  complete := fun w h => (causalTrace_iff_run P w).mp h

/-- The arrival-order language is a trace-level DCFL. -/
def causalTrace_isTraceDCFL (P : RoleProtocol) :
    IsTraceDCFL String (Option (List String)) Unit (CausalTrace P) :=
  (causalTrace_regular P).toTraceDCFL

/-- **The store recogniser.** No dead state: every arrival is recorded, and
    acceptance checks — at the end — that every recorded relevant name is
    justified by the recorded set (undeclared names are unconstrained and need
    no check). -/
def storeDFA (P : RoleProtocol) : FinDFA String (List String) where
  step := storeStep P
  start := []
  accept := fun c => c.all (fun t => enabled P (fun x => c.contains x) t)
  states := sublistsOf (relevantNames P)
  start_mem := mem_sublistsOf.mpr (List.nil_sublist _)
  closed := fun _ _ _ => mem_sublistsOf.mpr List.filter_sublist

private theorem store_foldl_inv (P : RoleProtocol) :
    ∀ (w : List String) (c : List String) (seenP : String → Prop),
      (∀ x ∈ c, x ∈ relevantNames P) →
      (∀ x ∈ relevantNames P, (x ∈ c ↔ seenP x)) →
      (∀ x ∈ w.foldl (storeStep P) c, x ∈ relevantNames P) ∧
      (∀ x ∈ relevantNames P, (x ∈ w.foldl (storeStep P) c ↔ (seenP x ∨ x ∈ w))) := by
  intro w
  induction w with
  | nil =>
    intro c seenP hsub hmem
    refine ⟨hsub, fun x hx => ?_⟩
    simpa using hmem x hx
  | cons t rest ih =>
    intro c seenP hsub hmem
    have hsub' : ∀ x ∈ storeStep P c t, x ∈ relevantNames P := by
      intro x hx
      exact (List.mem_filter.mp hx).1
    have hmem' : ∀ x ∈ relevantNames P, (x ∈ storeStep P c t ↔ (seenP x ∨ x = t)) := by
      intro x hxrel
      simp only [storeStep]
      rw [List.mem_filter]
      constructor
      · rintro ⟨-, hp⟩
        rcases or_true_iff.mp hp with hbeq | hc
        · exact Or.inr (eq_of_beq hbeq)
        · exact Or.inl ((hmem x hxrel).mp (contains_true_iff.mp hc))
      · rintro (hx | rfl)
        · exact ⟨hxrel,
            or_true_iff.mpr (Or.inr (contains_true_iff.mpr ((hmem x hxrel).mpr hx)))⟩
        · exact ⟨hxrel, or_true_iff.mpr (Or.inl (beq_self_eq_true x))⟩
    obtain ⟨h1, h2⟩ := ih (storeStep P c t) (fun x => seenP x ∨ x = t) hsub' hmem'
    refine ⟨h1, fun x hxrel => (h2 x hxrel).trans ?_⟩
    rw [List.mem_cons]
    constructor
    · rintro ((hx | rfl) | hxr)
      · exact Or.inl hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr hxr)
    · rintro (hx | rfl | hxr)
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hxr

/-- The store automaton recognises exactly `StoreTrace`. -/
theorem storeTrace_iff_run (P : RoleProtocol) (w : List String) :
    StoreTrace P w ↔ (storeDFA P).run w = true := by
  obtain ⟨hsub, hmem⟩ :=
    store_foldl_inv P w [] (fun _ => False) (by intro x hx; cases hx)
      (by intro x _; simp)
  have hmem' : ∀ x ∈ relevantNames P, (x ∈ w.foldl (storeStep P) [] ↔ x ∈ w) := by
    intro x hx
    simpa using hmem x hx
  show StoreTrace P w ↔
    (w.foldl (storeStep P) []).all
      (fun t => enabled P (fun x => (w.foldl (storeStep P) []).contains x) t) = true
  generalize hc : w.foldl (storeStep P) [] = c
  rw [hc] at hsub hmem'
  have hen : ∀ t, enabled P (fun x => c.contains x) t
      = enabled P (fun x => w.contains x) t := fun t =>
    enabled_congr (fun x hx => bool_eq_of_iff
      (by rw [contains_true_iff, contains_true_iff]; exact hmem' x hx)) t
  rw [List.all_eq_true]
  constructor
  · intro hst t htc
    rw [hen t]
    exact hst t ((hmem' t (hsub t htc)).mp htc)
  · intro hall t htw
    by_cases hrel : t ∈ relevantNames P
    · have := hall t ((hmem' t hrel).mpr htw)
      rw [hen t] at this
      exact this
    · exact enabled_of_undeclared fun hd => hrel (List.mem_append.mpr (Or.inl hd))

/-- **`prop:dcfl`, regularity (store form — the deployed accepted language):**
    the store trace language of a role-annotated protocol is regular. Same
    canonical state space as the arrival-order automaton; only the acceptance
    predicate differs. -/
def storeTrace_regular (P : RoleProtocol) :
    IsRegular String (List String) (StoreTrace P) where
  M := storeDFA P
  sound := fun w h => (storeTrace_iff_run P w).mpr h
  complete := fun w h => (storeTrace_iff_run P w).mp h

/-- The store trace language is a trace-level DCFL. -/
def storeTrace_isTraceDCFL (P : RoleProtocol) :
    IsTraceDCFL String (List String) Unit (StoreTrace P) :=
  (storeTrace_regular P).toTraceDCFL

/-! ## Half 2, §6 — Projection: the same recogniser family serves locally -/

/-- A step is `r`-relevant: `r` sends or receives it. -/
def RoleStep.relevant (st : RoleStep) (r : String) : Bool :=
  st.sender == r || st.recips.contains r

/-- **Protocol projection** (the *paper's* Def. proj in the v1 raw-edge regime,
    ADR-605): keep exactly the steps `r` sends or receives, `:caused-by`
    declarations raw — no splicing. NB the *shipped* composition differs: per
    ADR-604 the deployed `verify_causal_for_role` always verifies against the
    global dialect-level protocol; the step-filtered local protocol is the
    paper's object, mechanised here. -/
def projectProtocol (P : RoleProtocol) (r : String) : RoleProtocol :=
  P.filter (·.relevant r)

/-- **`prop:dcfl`, local form (arrival-order):** each local protocol's
    causal-order trace language is regular — the projection is a protocol, so
    the same construction recognises it. -/
def localTrace_regular (P : RoleProtocol) (r : String) :
    IsRegular String (Option (List String)) (CausalTrace (projectProtocol P r)) :=
  causalTrace_regular (projectProtocol P r)

/-- **`prop:dcfl`, local form (store):** each local protocol's store trace
    language — the deployed acceptance — is regular. -/
def localStoreTrace_regular (P : RoleProtocol) (r : String) :
    IsRegular String (List String) (StoreTrace (projectProtocol P r)) :=
  storeTrace_regular (projectProtocol P r)

/-- Each local causal-order trace language is a trace-level DCFL. -/
def localTrace_isTraceDCFL (P : RoleProtocol) (r : String) :
    IsTraceDCFL String (Option (List String)) Unit (CausalTrace (projectProtocol P r)) :=
  causalTrace_isTraceDCFL (projectProtocol P r)

/-- **"Projection adds no recogniser" — definitionally, and read it as such.**
    The local recogniser *is* the global builder applied to the projected step
    list: this is `rfl` because `localTrace_regular` is defined that way, so
    the theorem's mathematical content is only that the protocol class is
    closed under projection — one recogniser family serves globally and
    locally, no new machine class. It does not (and cannot) validate
    `projectProtocol` itself; the substantive local statement is the
    regularity instance `localTrace_regular` / `localStoreTrace_regular`. -/
theorem projection_adds_no_recogniser (P : RoleProtocol) (r : String) :
    (localTrace_regular P r).M = traceDFA (projectProtocol P r) :=
  rfl

/-! ## Worked examples

The straight-line witness (`x : A → B`, `y : C → B` caused by `x`), the
`protocol.rs` doc's own disjunctive-pool example, and a fan-in. -/

/-- The straight-line example protocol. -/
def exProtocol : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["B"], preds := [] },
    { name := "y", sender := "C", recips := ["B"], preds := [.single "x"] } ]

/-- Causal-order delivery `[x, y]` is accepted. -/
theorem ex_trace_ok : CausalTrace exProtocol ["x", "y"] := by decide

/-- Out-of-order delivery `[y, x]` is not a *causal-order* trace… -/
theorem ex_out_of_order_not_causal : ¬ CausalTrace exProtocol ["y", "x"] := by decide

/-- …but it IS in the deployed accepted language: `y` is `Unknown` on arrival,
    then `Valid` once `x` lands (valid-sticky, ADR-602) — the store language
    tolerates reordering. The inclusion `causalTrace_storeTrace` is strict. -/
theorem ex_out_of_order_store : StoreTrace exProtocol ["y", "x"] := by decide

/-- Locally at `C`, even the completed store never justifies `y`: the
    justifying `x` is not `C`-relevant, so it is absent from every store `C`
    can reach — the trace shadow of `my_permanently_unknown`. -/
theorem ex_local_permanently_stuck :
    ¬ StoreTrace (projectProtocol exProtocol "C") ["y"] := by decide

/-- The `protocol.rs` doc example: two `Single` declarations on one step. -/
def exAlternatives : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["B"], preds := [] },
    { name := "b", sender := "A", recips := ["B"], preds := [] },
    { name := "z", sender := "B", recips := ["A"], preds := [.single "x", .single "b"] } ]

/-- **The pool is disjunctive**: `[Single x, Single b]` reads `x ∨ b`
    (`protocol.rs`, doc on `check_step_uniqueness`) — seeing `x` alone
    justifies `z`. Under a conjunctive misreading this trace would be
    rejected. -/
theorem ex_pool_is_disjunctive : CausalTrace exAlternatives ["x", "z"] := by decide

/-- A fan-in protocol: `f` demands the full `(all x y)` set. -/
def exFanIn : RoleProtocol :=
  [ { name := "x", sender := "A", recips := ["C"], preds := [] },
    { name := "y", sender := "B", recips := ["C"], preds := [] },
    { name := "f", sender := "C", recips := ["A", "B"], preds := [.allOf ["x", "y"]] } ]

/-- Fan-in is conjunctive over its `(all …)` set: `x` alone never justifies
    `f`, even at the completed store. -/
theorem ex_fanin_incomplete : ¬ StoreTrace exFanIn ["x", "f"] := by decide

/-- With the full fan-in set delivered first, `f` is causally justified. -/
theorem ex_fanin_ok : CausalTrace exFanIn ["x", "y", "f"] := by decide

/-! Axiom audit (informational output when this file is compiled). -/
#print axioms dcfl_preserved_under_roles
#print axioms roles_dispatch_currently_unwired
#print axioms causalTrace_iff_run
#print axioms causalTrace_regular
#print axioms causalTrace_isTraceDCFL
#print axioms storeTrace_iff_run
#print axioms storeTrace_regular
#print axioms storeTrace_isTraceDCFL
#print axioms causalTrace_storeTrace
#print axioms localTrace_regular
#print axioms localStoreTrace_regular
#print axioms projection_adds_no_recogniser
#print axioms ex_pool_is_disjunctive
#print axioms ex_out_of_order_store
#print axioms ex_local_permanently_stuck

end R6DCFLPreservation
end CBCL
