import LeanCbcl.SExpr
import LeanCbcl.Message
import LeanCbcl.Dialect
import LeanCbcl.Agent
import LeanCbcl.MessageParser
import LeanCbcl.R3CorePreservation
import LeanCbcl.DetParser

/-!
# Deterministic-Union Preservation for CBCL Dialects

Formalizes the key language-theoretic claim underlying CBCL's safety guarantees:
installing a new R3-verified dialect into a well-formed agent preserves both the
decidability and the DCFL membership of the agent's accepted message language.

## Key Theorems
- `decidable_preserved`: installing a fresh, R3-verified dialect into a well-formed
  agent yields an agent whose language is still decidable (IsDecidable).
- `dcfl_preserved`: installing a fresh, R3-verified dialect into a well-formed agent
  with unique dialect names yields an agent whose language is still DCFL (IsDCFL).
- `agentDetParser_agrees`: the deterministic pushdown automaton `agentDetParser`
  agrees with the boolean decider `agentLanguageDecide` (requires `namesUnique`).
-/

namespace CBCL

-- ============================================================
-- Section 1: Tag type and tag function
-- ============================================================

/-- Classification tag for an SExpr message, keyed on its head symbol: a core
performative, `meta`, a wrapper head, a `lang` dialect name, or a simple head. -/
inductive MsgTag where
  | core    : CorePerformative → MsgTag
  | metaT   : MsgTag
  | wrapped : String → MsgTag
  | lang    : String → MsgTag
  | simple  : String → MsgTag
  deriving BEq, DecidableEq, Repr

/-- Maps a head symbol to its `CorePerformative`, or `none` if it is not one of the eight
core performatives (`tell`, `ask`, `reply`, `error`, `ok`, `cancel`, `hello`, `bye`). -/
def stringToCorePerformative : String → Option CorePerformative
  | "tell"   => some .tell
  | "ask"    => some .ask
  | "reply"  => some .reply
  | "error"  => some .error
  | "ok"     => some .ok
  | "cancel" => some .cancel
  | "hello"  => some .hello
  | "bye"    => some .bye
  | _        => none

/-- Computes the `MsgTag` of an SExpr from its head symbol, returning `none` for atoms
and lists not headed by a symbol. -/
def msgTag : SExpr → Option MsgTag
  | .list (.atom (.symbol head) :: rest) =>
    match stringToCorePerformative head with
    | some cp => some (MsgTag.core cp)
    | none =>
      if head == "meta" then some MsgTag.metaT
      else if head == "envelope" || head == "signed" || head == "with-limits" then
        some (MsgTag.wrapped head)
      else if head == "lang" then
        match rest with
        | .atom (.symbol dname) :: _ => some (MsgTag.lang dname)
        | _ => none
      else some (MsgTag.simple head)
  | _ => none

-- ============================================================
-- Section 2: Tag determinism and prefix-boundedness
-- ============================================================

theorem msgTag_deterministic (e : SExpr) (t1 t2 : MsgTag)
    (h1 : msgTag e = some t1) (h2 : msgTag e = some t2) : t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

theorem msgTag_head_only (head : String) (xs ys : List SExpr)
    (hnotlang : (head == "lang") = false) :
    msgTag (.list (.atom (.symbol head) :: xs)) =
    msgTag (.list (.atom (.symbol head) :: ys)) := by
  simp only [msgTag]
  cases hcp : stringToCorePerformative head <;> simp [hnotlang]

theorem msgTag_lang_second (second : SExpr) (rest1 rest2 : List SExpr) :
    msgTag (.list (.atom (.symbol "lang") :: second :: rest1)) =
    msgTag (.list (.atom (.symbol "lang") :: second :: rest2)) := by
  simp only [msgTag, stringToCorePerformative]
  cases second with
  | atom a => cases a with
    | symbol s => rfl
    | _ => rfl
  | list _ => rfl

theorem msgTag_atom (a : Atom) : msgTag (.atom a) = none := by
  simp [msgTag]

theorem msgTag_nil : msgTag (.list []) = none := by
  simp [msgTag]

-- ============================================================
-- Section 3: Reserved token sets and disjointness
-- ============================================================

/-- Head symbols reserved by the core protocol: `meta`, the three wrapper heads, and `lang`. -/
def reservedHeads : List String :=
  ["meta", "envelope", "signed", "with-limits", "lang"]

/-- Heads for non-lang CBCL messages. -/
def agentHeadNames : List String :=
  corePerformativeNames ++ ["meta", "envelope", "signed", "with-limits"]

/-- Find the index of a dialect by name. -/
def findDialectIdx : List Dialect → String → Option Nat
  | [], _ => none
  | d :: ds, dn =>
      if d.name == dn then some 0 else
        match findDialectIdx ds dn with
        | some i => some (i + 1)
        | none => none

/-- Safe list lookup (avoid Std List.get?). -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Encoding for lang subparser states. -/

def langOffset : Nat := 200

/-- Per-dialect stride separating successive dialects' encoded lang-subparser states. -/
def langStride : Nat := 200

/-- Encodes a dialect index `idx` and its lang-subparser state `s` into a single `Nat`
parser state (`langOffset + idx * langStride + s`). -/
def langState (idx : Nat) (s : Nat) : Nat :=
  langOffset + idx * langStride + s

theorem langState_ne_one (idx s : Nat) : langState idx s ≠ 1 := by
  have hge : 200 ≤ langState idx s := by
    dsimp [langState, langOffset, langStride]
    have h1 : 200 ≤ 200 + idx * 200 := Nat.le_add_right _ _
    have h2 : 200 + idx * 200 ≤ 200 + idx * 200 + s := Nat.le_add_right _ _
    exact Nat.le_trans h1 h2
  have hlt : 1 < 200 := by decide
  have hgt : 1 < langState idx s := Nat.lt_of_lt_of_le hlt hge
  exact Nat.ne_of_gt hgt

/-- Inverse of `langState`: recovers `(dialect index, subparser state)` from an encoded
state, or `none` when the state is below `langOffset`. -/
def decodeLangState (s : Nat) : Option (Nat × Nat) :=
  if _ : langOffset ≤ s then
    let t := s - langOffset
    some (t / langStride, t % langStride)
  else none

private def isLangAcceptState (s : Nat) : Bool :=
  match decodeLangState s with
  | some (_, 7) => true
  | _ => false

theorem decodeLangState_langState (idx s : Nat) (hs : s < langStride) :
    decodeLangState (langState idx s) = some (idx, s) := by
  unfold decodeLangState langState langOffset langStride
  have hle : 200 ≤ 200 + idx * 200 + s := by
    have h1 : 200 ≤ 200 + idx * 200 := Nat.le_add_right _ _
    have h2 : 200 + idx * 200 ≤ 200 + idx * 200 + s := Nat.le_add_right _ _
    exact Nat.le_trans h1 h2
  have hs' : s < 200 := by
    have hs' := hs
    simp [langStride] at hs'
    exact hs'
  have hsub : 200 + idx * 200 + s - 200 = idx * 200 + s := by
    calc
      200 + idx * 200 + s - 200 = 200 + (idx * 200 + s) - 200 := by
        simp [Nat.add_assoc]
      _ = idx * 200 + s := by
        exact Nat.add_sub_cancel_left 200 (idx * 200 + s)
  have hdiv : (idx * 200 + s) / 200 = idx := by
    calc
      (idx * 200 + s) / 200 = (s + 200 * idx) / 200 := by
        simp [Nat.add_comm, Nat.mul_comm]
      _ = s / 200 + idx := by
        exact Nat.add_mul_div_left s idx (by decide)
      _ = idx := by
        simp [Nat.div_eq_of_lt hs']
  have hmod : (idx * 200 + s) % 200 = s := by
    calc
      (idx * 200 + s) % 200 = (s + 200 * idx) % 200 := by
        simp [Nat.add_comm, Nat.mul_comm]
      _ = s % 200 := by
        exact Nat.add_mul_mod_self_left s 200 idx
      _ = s := by
        simp [Nat.mod_eq_of_lt hs']
  by_cases h : 200 ≤ 200 + idx * 200 + s
  · simp [h, hsub, hdiv, hmod]
  · exact (False.elim (h hle))

theorem isLangAcceptState_langState (idx s : Nat) (hs : s < langStride) :
    isLangAcceptState (langState idx s) = (s == 7) := by
  by_cases h : s = 7
  · subst h
    have hs' : 7 < langStride := by simpa using hs
    simp [isLangAcceptState, decodeLangState_langState idx 7 hs']
  · have hne : s ≠ 7 := h
    simp [isLangAcceptState, decodeLangState_langState idx s hs, hne]


theorem stringToCorePerformative_some (s : String) (cp : CorePerformative)
    (h : stringToCorePerformative s = some cp) :
    s = "tell" ∨ s = "ask" ∨ s = "reply" ∨ s = "error" ∨
    s = "ok" ∨ s = "cancel" ∨ s = "hello" ∨ s = "bye" := by
  unfold stringToCorePerformative at h
  split at h
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    | simp at h

theorem core_not_reserved (s : String) (cp : CorePerformative)
    (hcore : stringToCorePerformative s = some cp) :
    s ∉ reservedHeads := by
  simp [reservedHeads, List.mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro heq; rw [heq] at hcore; simp [stringToCorePerformative] at hcore)

theorem msgTag_injective_lang (e : SExpr) (d1 d2 : String)
    (h1 : msgTag e = some (MsgTag.lang d1))
    (h2 : msgTag e = some (MsgTag.lang d2)) : d1 = d2 := by
  have := msgTag_deterministic e _ _ h1 h2
  exact MsgTag.noConfusion this (fun h => h)

theorem msgTag_metaT_not_lang (e : SExpr) (d : String)
    (hm : msgTag e = some MsgTag.metaT) :
    msgTag e ≠ some (MsgTag.lang d) := by
  rw [hm]; intro h; exact MsgTag.noConfusion (Option.some.inj h)

theorem msgTag_metaT_not_simple (e : SExpr) (s : String)
    (hm : msgTag e = some MsgTag.metaT) :
    msgTag e ≠ some (MsgTag.simple s) := by
  rw [hm]; intro h; exact MsgTag.noConfusion (Option.some.inj h)

theorem msgTag_metaT_not_core (e : SExpr) (cp : CorePerformative)
    (hm : msgTag e = some MsgTag.metaT) :
    msgTag e ≠ some (MsgTag.core cp) := by
  rw [hm]; intro h; exact MsgTag.noConfusion (Option.some.inj h)

theorem msgTag_core_not_simple (e : SExpr) (cp : CorePerformative) (s : String)
    (hc : msgTag e = some (MsgTag.core cp)) :
    msgTag e ≠ some (MsgTag.simple s) := by
  rw [hc]; intro h; exact MsgTag.noConfusion (Option.some.inj h)

theorem msgTag_core_not_lang (e : SExpr) (cp : CorePerformative) (d : String)
    (hc : msgTag e = some (MsgTag.core cp)) :
    msgTag e ≠ some (MsgTag.lang d) := by
  rw [hc]; intro h; exact MsgTag.noConfusion (Option.some.inj h)

theorem msgTag_wrapped_not_simple (e : SExpr) (w s : String)
    (hw : msgTag e = some (MsgTag.wrapped w)) :
    msgTag e ≠ some (MsgTag.simple s) := by
  rw [hw]; intro h; exact MsgTag.noConfusion (Option.some.inj h)

theorem msgTag_lang_not_simple (e : SExpr) (d s : String)
    (hl : msgTag e = some (MsgTag.lang d)) :
    msgTag e ≠ some (MsgTag.simple s) := by
  rw [hl]; intro h; exact MsgTag.noConfusion (Option.some.inj h)

theorem msgTag_categories_disjoint (e : SExpr) (t1 t2 : MsgTag)
    (h1 : msgTag e = some t1) (h2 : msgTag e = some t2) : t1 = t2 :=
  msgTag_deterministic e t1 t2 h1 h2

theorem msgTag_lang_concrete (dname : String) (inner : SExpr) :
    msgTag (.list [.atom (.symbol "lang"), .atom (.symbol dname), inner]) =
    some (MsgTag.lang dname) := by
  simp [msgTag, stringToCorePerformative]

-- ============================================================
-- Section 4: Tagged predicate and sublanguages
-- ============================================================

/-- Proposition holding exactly when `e`'s computed `msgTag` equals `some t`. -/
def Tagged (t : MsgTag) (e : SExpr) : Prop := msgTag e = some t

/-- The head-symbol string naming each `CorePerformative`. -/
def corePerformativeName : CorePerformative → String
  | .tell   => "tell"
  | .ask    => "ask"
  | .reply  => "reply"
  | .error  => "error"
  | .ok     => "ok"
  | .cancel => "cancel"
  | .hello  => "hello"
  | .bye    => "bye"

/-- The head-symbol string naming a `Performative`: the core name, or the custom name. -/
def performativeName : Performative → String
  | .core .tell   => "tell"
  | .core .ask    => "ask"
  | .core .reply  => "reply"
  | .core .error  => "error"
  | .core .ok     => "ok"
  | .core .cancel => "cancel"
  | .core .hello  => "hello"
  | .core .bye    => "bye"
  | .custom name  => name

/-- `e` is a list whose head symbol is a core performative name. -/
def coreLanguage (e : SExpr) : Prop :=
  ∃ cp args, e = .list (.atom (.symbol (corePerformativeName cp)) :: args)

/-- `e` is a list whose head symbol is `meta`. -/
def metaLanguage (e : SExpr) : Prop :=
  ∃ args, e = .list (.atom (.symbol "meta") :: args)

/-- `e` is a list whose head symbol is a wrapper head (`envelope`, `signed`, or `with-limits`). -/
def wrappedLanguage (e : SExpr) : Prop :=
  ∃ w args, (w = "envelope" ∨ w = "signed" ∨ w = "with-limits") ∧
    e = .list (.atom (.symbol w) :: args)

/-- `e` is a `lang`-tagged message naming dialect `d` and carrying an inner performative
listed in `d.performativeNames`. -/
def langLanguage (d : Dialect) (e : SExpr) : Prop :=
  ∃ perf args,
    e = .list [.atom (.symbol "lang"), .atom (.symbol d.name),
      .list (.atom (.symbol perf) :: args)] ∧
    perf ∈ d.performativeNames

/-- True when some dialect installed in `a` defines the performative `name`. -/
def Agent.acceptsPerf (a : Agent) (name : String) : Bool :=
  a.dialects.any (·.definesPerformative name)

/-- Dialect names are unique. -/
def Agent.namesUnique (a : Agent) : Prop :=
  (a.dialects.map Dialect.name).Nodup

/-- `e` is accepted by agent `a`: a core, meta, or wrapped message, or a `lang` message
for one of `a`'s installed dialects. -/
def agentLanguage (a : Agent) (e : SExpr) : Prop :=
  coreLanguage e ∨ metaLanguage e ∨ wrappedLanguage e ∨
  (∃ d ∈ a.dialects, langLanguage d e)

-- ============================================================
-- Section 5: Sublanguages imply tags
-- ============================================================

theorem stringToCorePerformative_corePerformativeName (cp : CorePerformative) :
    stringToCorePerformative (corePerformativeName cp) = some cp := by
  cases cp <;> rfl

theorem coreLanguage_tagged (e : SExpr) (h : coreLanguage e) :
    ∃ cp, Tagged (MsgTag.core cp) e := by
  obtain ⟨cp, args, rfl⟩ := h
  exact ⟨cp, by simp [Tagged, msgTag, stringToCorePerformative_corePerformativeName]⟩

theorem metaLanguage_tagged (e : SExpr) (h : metaLanguage e) :
    Tagged MsgTag.metaT e := by
  obtain ⟨args, rfl⟩ := h
  simp [Tagged, msgTag, stringToCorePerformative]

theorem wrappedLanguage_tagged (e : SExpr) (h : wrappedLanguage e) :
    ∃ w, Tagged (MsgTag.wrapped w) e := by
  obtain ⟨w, args, hw, rfl⟩ := h
  cases hw with
  | inl h =>
    subst h
    exact ⟨"envelope", show msgTag (.list (.atom (.symbol "envelope") :: args)) = some (MsgTag.wrapped "envelope") by
      unfold msgTag; unfold stringToCorePerformative; simp⟩
  | inr h => cases h with
    | inl h =>
      subst h
      exact ⟨"signed", show msgTag (.list (.atom (.symbol "signed") :: args)) = some (MsgTag.wrapped "signed") by
        unfold msgTag; unfold stringToCorePerformative; simp⟩
    | inr h =>
      subst h
      exact ⟨"with-limits", show msgTag (.list (.atom (.symbol "with-limits") :: args)) = some (MsgTag.wrapped "with-limits") by
        unfold msgTag; unfold stringToCorePerformative; simp⟩

theorem langLanguage_tagged (d : Dialect) (e : SExpr) (h : langLanguage d e) :
    Tagged (MsgTag.lang d.name) e := by
  obtain ⟨perf, args, rfl, _⟩ := h
  simp [Tagged, msgTag, stringToCorePerformative]

/-- DPDA for full agent language (core/meta/wrapped/lang). -/

def agentDetParser (a : Agent) : DetParser where
  step := fun state tok top =>
    match state, tok, top with
    | 1, .sym s, some 1 =>
        if s == "lang" then (langState 0 0, [1])
        else (headCheckDetParser agentHeadNames).step 1 tok top
    | _, _, _ =>
        match decodeLangState state with
        | some (idx, ls) =>
            if ls = 0 then
              match tok, top with
              | .sym dn, some 1 =>
                  match findDialectIdx a.dialects dn with
                  | some idx' => (langState idx' 3, [1])
                  | none => (99, [])
              | _, _ => (99, [])
            else
              match listGet? a.dialects idx with
              | some d =>
                  let p := langDetParser d.name d.performativeNames
                  let (ls', push) := p.step ls tok top
                  (langState idx ls', push)
              | none => (99, [])
        | none => (headCheckDetParser agentHeadNames).step state tok top
  accept := fun state stack =>
    match stack with
    | [0] =>
        if state == 3 then true
        else if isLangAcceptState state then true
        else false
    | _ => false

private theorem agentDetParser_step_lang (a : Agent) (d : Dialect) (idx s : Nat)
    (tok : Token) (top : Option Nat)
    (hs : s ≠ 0) (hslt : s < langStride)
    (hget : listGet? a.dialects idx = some d) :
    (agentDetParser a).step (langState idx s) tok top =
      let (s', push) := (langDetParser d.name d.performativeNames).step s tok top
      (langState idx s', push) := by
  have hstate : langState idx s ≠ 1 := langState_ne_one idx s
  cases tok <;> cases top <;>
    simp [agentDetParser, decodeLangState_langState idx s hslt, hs, hget, hstate]

private theorem agentDetParser_runStep_lang (a : Agent) (d : Dialect) (idx s : Nat)
    (tok : Token) (stack : List Nat)
    (hs : s ≠ 0) (hslt : s < langStride)
    (hget : listGet? a.dialects idx = some d) :
    (agentDetParser a).runStep (langState idx s, stack) tok =
      let res := (langDetParser d.name d.performativeNames).runStep (s, stack) tok
      (langState idx res.1, res.2) := by
  simp [DetParser.runStep, agentDetParser_step_lang a d idx s tok stack.head? hs hslt hget]

private theorem agentDetParser_run_lang_aux (a : Agent) (d : Dialect) (idx s : Nat)
    (tokens : List Token) (stack : List Nat)
    (hs : s ≠ 0) (hslt : s < langStride)
    (hget : listGet? a.dialects idx = some d) :
    List.foldl (agentDetParser a).runStep (langState idx s, stack) tokens =
      let res := List.foldl (langDetParser d.name d.performativeNames).runStep (s, stack) tokens
      (langState idx res.1, res.2) := by
  induction tokens generalizing s stack with
  | nil => simp
  | cons tok rest ih =>
      simp [List.foldl]
      have hstep := agentDetParser_runStep_lang a d idx s tok stack hs hslt hget
      let res := (langDetParser d.name d.performativeNames).runStep (s, stack) tok
      have hslt' : res.1 < langStride := by
        have h := langDetParser_step_state_lt d.name d.performativeNames s tok stack.head?
        simpa [DetParser.runStep, langStride, res] using h
      have hs' : res.1 ≠ 0 := by
        have h := langDetParser_step_state_ne_zero d.name d.performativeNames s tok stack.head?
        simpa [DetParser.runStep, res] using h
      have ih' := ih res.1 res.2 hs' hslt'
      simp [hstep, res, ih']


/-- Bool decider for the full agent language. -/
def agentLanguageBool (a : Agent) (e : SExpr) : Bool :=
  headCheckBool agentHeadNames e ||
  a.dialects.any (fun d => langCheckBool d.name d.performativeNames e)



/-- If findDialectIdx succeeds, it points to a dialect with the given name. -/
theorem findDialectIdx_get? {ds : List Dialect} {dn : String} {idx : Nat}
    (h : findDialectIdx ds dn = some idx) :
    ∃ d, listGet? ds idx = some d ∧ d.name = dn := by
  induction ds generalizing idx with
  | nil => cases h
  | cons d ds ih =>
      by_cases hdn : d.name = dn
      · have hbeq : (d.name == dn) = true := by
          simpa [beq_iff_eq] using hdn
        have h' : 0 = idx := by
          have htmp := h
          simp [findDialectIdx, hbeq] at htmp
          exact htmp
        cases h'
        exact ⟨d, by simp [listGet?], hdn⟩
      · have hbeq : (d.name == dn) = false := by
          simp [hdn]
        cases hfd : findDialectIdx ds dn with
        | none =>
            have htmp := h
            simp [findDialectIdx, hbeq, hfd] at htmp
        | some i =>
            have h' : i + 1 = idx := by
              have htmp := h
              simp [findDialectIdx, hbeq, hfd] at htmp
              exact htmp
            obtain ⟨d', hget, hname⟩ := ih hfd
            subst h'
            exact ⟨d', by simpa [listGet?] using hget, hname⟩

/-- If dialect names are unique, findDialectIdx recovers the exact dialect. -/
theorem findDialectIdx_unique {ds : List Dialect} {d : Dialect} {dn : String}
    (hnd : (ds.map Dialect.name).Nodup)
    (hmem : d ∈ ds) (hname : d.name = dn) :
    ∃ idx, findDialectIdx ds dn = some idx ∧ listGet? ds idx = some d := by
  induction ds with
  | nil => cases hmem
  | cons d0 ds ih =>
      have hnd' : d0.name ∉ ds.map Dialect.name ∧ (ds.map Dialect.name).Nodup := by
        simpa using hnd
      have hmem' : d = d0 ∨ d ∈ ds := by
        simpa [List.mem_cons] using hmem
      cases hmem' with
      | inl hEq =>
          subst hEq
          have hbeq : (d.name == dn) = true := by
            simpa [beq_iff_eq] using hname
          refine ⟨0, ?_, by simp [listGet?]⟩
          simp [findDialectIdx, hbeq]
      | inr hmem' =>
          have hne : d0.name ≠ dn := by
            intro h0
            have hmemmap : d.name ∈ ds.map Dialect.name := by
              exact (List.mem_map).2 ⟨d, hmem', rfl⟩
            have : d0.name ∈ ds.map Dialect.name := by
              simpa [hname, h0] using hmemmap
            exact (hnd'.left this).elim
          have hbeq : (d0.name == dn) = false := by
            simp [hne]
          obtain ⟨idx, hidx, hget⟩ := ih hnd'.right hmem'
          refine ⟨idx + 1, ?_, ?_⟩
          · simp [findDialectIdx, hbeq, hidx]
          · simpa [listGet?, Nat.succ_eq_add_one] using hget

-- ============================================================
-- Section 6: IsDecidable / IsDCFL instances
-- ============================================================

/-- Bool decider for lang language. -/
def langLanguageBool (d : Dialect) (e : SExpr) : Bool :=
  langCheckBool d.name d.performativeNames e

private theorem coreLanguage_sound (e : SExpr)
    (h : headCheckBool corePerformativeNames e = true) :
    coreLanguage e := by
  -- headCheckBool checks if e = .list (.atom (.symbol s) :: _) with s ∈ corePerformativeNames
  match e with
  | .atom _ => simp [headCheckBool] at h
  | .list [] => simp [headCheckBool] at h
  | .list (.list _ :: _) => simp [headCheckBool] at h
  | .list (.atom (.num _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.str _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.bool _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.keyword _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.symbol s) :: args) =>
    simp only [headCheckBool] at h
    -- h : corePerformativeNames.contains s = true
    have hmem : s ∈ corePerformativeNames := List.mem_of_elem_eq_true h
    simp [corePerformativeNames] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.tell, args, rfl⟩
    · exact ⟨.ask, args, rfl⟩
    · exact ⟨.reply, args, rfl⟩
    · exact ⟨.error, args, rfl⟩
    · exact ⟨.ok, args, rfl⟩
    · exact ⟨.cancel, args, rfl⟩
    · exact ⟨.hello, args, rfl⟩
    · exact ⟨.bye, args, rfl⟩

private theorem coreLanguage_complete (e : SExpr)
    (h : coreLanguage e) :
    headCheckBool corePerformativeNames e = true := by
  obtain ⟨cp, args, rfl⟩ := h
  cases cp <;> simp [headCheckBool, corePerformativeName, corePerformativeNames, List.contains, List.elem]

/-- `coreLanguage` is decidable, with `headCheckBool corePerformativeNames` as the decider. -/
def coreLanguage_decidable : IsDecidable coreLanguage where
  decide_ := headCheckBool corePerformativeNames
  sound := coreLanguage_sound
  complete := coreLanguage_complete

private theorem metaLanguage_sound (e : SExpr)
    (h : headCheckBool ["meta"] e = true) :
    metaLanguage e := by
  match e with
  | .atom _ => simp [headCheckBool] at h
  | .list [] => simp [headCheckBool] at h
  | .list (.list _ :: _) => simp [headCheckBool] at h
  | .list (.atom (.num _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.str _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.bool _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.keyword _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.symbol s) :: args) =>
    simp only [headCheckBool] at h
    have hmem : s ∈ ["meta"] := List.mem_of_elem_eq_true h
    simp at hmem
    subst hmem
    exact ⟨args, rfl⟩

private theorem metaLanguage_complete (e : SExpr) (h : metaLanguage e) :
    headCheckBool ["meta"] e = true := by
  obtain ⟨args, rfl⟩ := h
  simp [headCheckBool, List.contains, List.elem]

/-- `metaLanguage` is decidable, with `headCheckBool ["meta"]` as the decider. -/
def metaLanguage_decidable : IsDecidable metaLanguage where
  decide_ := headCheckBool ["meta"]
  sound := metaLanguage_sound
  complete := metaLanguage_complete

private theorem wrappedLanguage_sound (e : SExpr)
    (h : headCheckBool ["envelope", "signed", "with-limits"] e = true) :
    wrappedLanguage e := by
  match e with
  | .atom _ => simp [headCheckBool] at h
  | .list [] => simp [headCheckBool] at h
  | .list (.list _ :: _) => simp [headCheckBool] at h
  | .list (.atom (.num _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.str _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.bool _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.keyword _) :: _) => simp [headCheckBool] at h
  | .list (.atom (.symbol s) :: args) =>
    simp only [headCheckBool] at h
    have hmem : s ∈ ["envelope", "signed", "with-limits"] := List.mem_of_elem_eq_true h
    simp at hmem
    rcases hmem with rfl | rfl | rfl
    · exact ⟨"envelope", args, Or.inl rfl, rfl⟩
    · exact ⟨"signed", args, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨"with-limits", args, Or.inr (Or.inr rfl), rfl⟩

private theorem wrappedLanguage_complete (e : SExpr) (h : wrappedLanguage e) :
    headCheckBool ["envelope", "signed", "with-limits"] e = true := by
  obtain ⟨w, args, hw, rfl⟩ := h
  cases hw with
  | inl h => subst h; simp [headCheckBool, List.contains, List.elem]
  | inr h => cases h with
    | inl h => subst h; simp [headCheckBool, List.contains, List.elem]
    | inr h => subst h; simp [headCheckBool, List.contains, List.elem]

/-- `wrappedLanguage` is decidable, with `headCheckBool` over the wrapper heads as the decider. -/
def wrappedLanguage_decidable : IsDecidable wrappedLanguage where
  decide_ := headCheckBool ["envelope", "signed", "with-limits"]
  sound := wrappedLanguage_sound
  complete := wrappedLanguage_complete

private theorem langLanguage_sound (d : Dialect) (e : SExpr)
    (h : langLanguageBool d e = true) :
    langLanguage d e := by
  unfold langLanguageBool langCheckBool at h
  split at h
  · next dn perf rest =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hmem⟩ := h
    exact ⟨perf, rest, rfl, List.mem_of_elem_eq_true hmem⟩
  · simp at h

private theorem langLanguage_complete (d : Dialect) (e : SExpr)
    (h : langLanguage d e) :
    langLanguageBool d e = true := by
  obtain ⟨perf, args, rfl, hmem⟩ := h
  have hcontains : d.performativeNames.contains perf = true :=
    List.elem_eq_true_of_mem hmem
  simpa [langLanguageBool, langCheckBool] using hcontains

/-- `langLanguage d` is decidable, with `langLanguageBool d` as the decider. -/
def langLanguage_decidable (d : Dialect) : IsDecidable (langLanguage d) where
  decide_ := langLanguageBool d
  sound := langLanguage_sound d
  complete := langLanguage_complete d

/-- Core language is a DCFL via headCheckDetParser. -/
def coreLanguage_isDCFL : IsDCFL coreLanguage where
  parser := headCheckDetParser corePerformativeNames
  sound := by
    intro e h
    rw [headCheck_agrees] at h
    exact coreLanguage_sound e h
  complete := by
    intro e h
    rw [headCheck_agrees]
    exact coreLanguage_complete e h
/-- Lang language is a DCFL via langDetParser. -/
def langLanguage_isDCFL (d : Dialect) : IsDCFL (langLanguage d) where
  parser := langDetParser d.name d.performativeNames
  sound := by
    intro e h
    have h' : langCheckBool d.name d.performativeNames e = true := by
      simpa [langCheck_agrees] using h
    exact langLanguage_sound d e (by simpa [langLanguageBool] using h')
  complete := by
    intro e h
    have h' : langCheckBool d.name d.performativeNames e = true := by
      simpa [langLanguageBool] using (langLanguage_complete d e h)
    simpa [langCheck_agrees] using h'



-- ============================================================
-- Section 7: Tag-based union theorems
-- ============================================================

/-- The union of two decidable languages is decidable. -/
-- `_hne`/`_ht1`/`_ht2` record the disjoint-tag precondition of the Section 7
-- tagged-union construction; the decidability proof (a Boolean `||`) does not
-- need them, so they are kept for interface documentation, not deleted.
@[nolint unusedArguments]
def decidable_union_tagged (L1 L2 : SExpr → Prop) (t1 t2 : MsgTag)
    (_hne : t1 ≠ t2)
    (h1 : IsDecidable L1) (h2 : IsDecidable L2)
    (_ht1 : ∀ e, L1 e → Tagged t1 e)
    (_ht2 : ∀ e, L2 e → Tagged t2 e) :
    IsDecidable (fun e => L1 e ∨ L2 e) where
  decide_ := fun e => h1.decide_ e || h2.decide_ e
  sound := by
    intro e h
    simp only [Bool.or_eq_true] at h
    cases h with
    | inl h1e => exact Or.inl (h1.sound e h1e)
    | inr h2e => exact Or.inr (h2.sound e h2e)
  complete := by
    intro e h
    simp only [Bool.or_eq_true]
    cases h with
    | inl h1e => exact Or.inl (h1.complete e h1e)
    | inr h2e => exact Or.inr (h2.complete e h2e)

/-- DCFL union gives decidable. -/
def dcfl_union_decidable (L1 L2 : SExpr → Prop)
    (h1 : IsDCFL L1) (h2 : IsDCFL L2) :
    IsDecidable (fun e => L1 e ∨ L2 e) where
  decide_ := fun e => h1.parser.run (tokenize e) || h2.parser.run (tokenize e)
  sound := by
    intro e h
    simp only [Bool.or_eq_true] at h
    cases h with
    | inl h1e => exact Or.inl (h1.sound e h1e)
    | inr h2e => exact Or.inr (h2.sound e h2e)
  complete := by
    intro e h
    simp only [Bool.or_eq_true]
    cases h with
    | inl h1e => exact Or.inl (h1.complete e h1e)
    | inr h2e => exact Or.inr (h2.complete e h2e)

-- ============================================================
-- Section 8: The preservation theorem
-- ============================================================

/-- Bool decider for the full agent language. -/
def agentLanguageDecide (a : Agent) (e : SExpr) : Bool :=
  headCheckBool corePerformativeNames e ||
  headCheckBool ["meta"] e ||
  headCheckBool ["envelope", "signed", "with-limits"] e ||
  a.dialects.any (fun d => langLanguageBool d e)

private theorem agentLanguage_sound' (a : Agent) (e : SExpr)
    (h : agentLanguageDecide a e = true) :
    agentLanguage a e := by
  simp only [agentLanguageDecide, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl (coreLanguage_sound e h)
  · exact Or.inr (Or.inl (metaLanguage_sound e h))
  · exact Or.inr (Or.inr (Or.inl (wrappedLanguage_sound e h)))
  · simp only [List.any_eq_true] at h
    obtain ⟨d, hd_mem, hd_acc⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨d, hd_mem, langLanguage_sound d e hd_acc⟩))

private theorem agentLanguage_complete' (a : Agent) (e : SExpr)
    (h : agentLanguage a e) :
    agentLanguageDecide a e = true := by
  simp only [agentLanguageDecide, Bool.or_eq_true]
  rcases h with h | h | h | ⟨d, hd_mem, hd_lang⟩
  · exact Or.inl (Or.inl (Or.inl (coreLanguage_complete e h)))
  · exact Or.inl (Or.inl (Or.inr (metaLanguage_complete e h)))
  · exact Or.inl (Or.inr (wrappedLanguage_complete e h))
  · exact Or.inr (by simp only [List.any_eq_true]; exact ⟨d, hd_mem, langLanguage_complete d e hd_lang⟩)

/-- The agent language is decidable. -/
def agentLanguage_isDecidable (a : Agent) : IsDecidable (agentLanguage a) where
  decide_ := agentLanguageDecide a
  sound := agentLanguage_sound' a
  complete := agentLanguage_complete' a

/-- **Main theorem**: installing any dialect preserves the decidability
    of the agent's language.

    Decidability is a property of the `Bool`-valued decider for
    `agentLanguage`, which is total on all inputs for any agent. It
    does not compose through `verifyR3`, `wellFormed`, or dialect-name
    freshness — those are irrelevant to whether the decider returns a
    value. The previous formulation of this theorem carried three
    vestigial premises (`_hwf`, `_hFresh`, `_hR3`) that the proof did
    not consume; they were removed in the Lean-audit fix session. -/
def decidable_preserved (a : Agent) (d : Dialect) :
    IsDecidable (agentLanguage (a.installDialect d)) :=
  agentLanguage_isDecidable (a.installDialect d)

-- ============================================================
-- Supplementary: tag-based reasoning for dialect dispatch
-- ============================================================

theorem msgTag_dialect_msg (dname : String) (inner : SExpr) :
    msgTag (.list [.atom (.symbol "lang"), .atom (.symbol dname), inner]) =
    some (MsgTag.lang dname) := by
  simp [msgTag, stringToCorePerformative]

theorem msgTag_simple_msg (head : String) (args : List SExpr)
    (hne_core : stringToCorePerformative head = none)
    (hne_meta : head ≠ "meta")
    (hne_env : head ≠ "envelope") (hne_sig : head ≠ "signed")
    (hne_wl : head ≠ "with-limits") (hne_lang : head ≠ "lang") :
    msgTag (.list (.atom (.symbol head) :: args)) = some (MsgTag.simple head) := by
  simp only [msgTag, hne_core]
  have h1 : (head == "meta") = false := by simp [hne_meta]
  have h2 : (head == "envelope" || head == "signed" || head == "with-limits") = false := by
    simp [hne_env, hne_sig, hne_wl]
  have h3 : (head == "lang") = false := by simp [hne_lang]
  simp [h1, h2, h3]

theorem tag_lang_implies_dialect_parse (dname : String) (inner : SExpr) (rest : List SExpr) :
    ∃ msg, parseMessage (.list (.atom (.symbol "lang") :: .atom (.symbol dname) :: inner :: rest))
           = some msg ∧
           msg.type = MessageType.dialect :=
  ⟨{ type := .dialect
    , performative := .custom "lang"
    , params := .atom (.symbol dname) :: inner :: rest },
   by simp [parseMessage], rfl⟩

theorem msgTag_consistent_core (head : String) (cp : CorePerformative) (args : List SExpr) (msg : Message)
    (htag : msgTag (.list (.atom (.symbol head) :: args)) = some (MsgTag.core cp))
    (hparse : parseMessage (.list (.atom (.symbol head) :: args)) = some msg) :
    msg.type = MessageType.simple := by
  have hne_meta : head ≠ "meta" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  have hne_lang : head ≠ "lang" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
    split at htag <;> simp at htag
  have hne_env : head ≠ "envelope" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  have hne_sig : head ≠ "signed" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  have hne_wl : head ≠ "with-limits" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  simp only [parseMessage] at hparse
  have h1 : (head == "meta") = false := by simp [hne_meta]
  have h2 : (head == "lang") = false := by simp [hne_lang]
  have h3 : (head == "envelope" || head == "signed" || head == "with-limits") = false := by
    simp [hne_env, hne_sig, hne_wl]
  simp [h1, h2, h3] at hparse
  cases hparse; rfl

theorem msgTag_consistent_meta (args : List SExpr) (msg : Message)
    (hparse : parseMessage (.list (.atom (.symbol "meta") :: args)) = some msg) :
    msg.type = MessageType.metaMsg := by
  simp [parseMessage] at hparse
  cases hparse; rfl

theorem msgTag_consistent_wrapped (head : String) (args : List SExpr) (msg : Message)
    (hwrap : head = "envelope" ∨ head = "signed" ∨ head = "with-limits")
    (hparse : parseMessage (.list (.atom (.symbol head) :: args)) = some msg) :
    msg.type = MessageType.wrapped := by
  rcases hwrap with rfl | rfl | rfl <;> simp [parseMessage] at hparse <;> cases hparse <;> rfl

theorem msgTag_consistent_lang (dname : String) (rest : List SExpr) (msg : Message)
    (hparse : parseMessage (.list (.atom (.symbol "lang") :: .atom (.symbol dname) :: rest)) = some msg) :
    msg.type = MessageType.dialect := by
  simp [parseMessage] at hparse
  cases hparse; rfl

theorem msgTag_consistent_simple (head : String) (args : List SExpr) (msg : Message)
    (htag : msgTag (.list (.atom (.symbol head) :: args)) = some (MsgTag.simple head))
    (hparse : parseMessage (.list (.atom (.symbol head) :: args)) = some msg) :
    msg.type = MessageType.simple := by
  have hne_meta : head ≠ "meta" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  have hne_env : head ≠ "envelope" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  have hne_sig : head ≠ "signed" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  have hne_wl : head ≠ "with-limits" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
  have hne_lang : head ≠ "lang" := by
    intro heq; subst heq; simp [msgTag, stringToCorePerformative] at htag
    split at htag <;> simp at htag
  simp only [parseMessage] at hparse
  have h1 : (head == "meta") = false := by simp [hne_meta]
  have h2 : (head == "lang") = false := by simp [hne_lang]
  have h3 : (head == "envelope" || head == "signed" || head == "with-limits") = false := by
    simp [hne_env, hne_sig, hne_wl]
  simp [h1, h2, h3] at hparse
  cases hparse; rfl

theorem fresh_dialect_names_disjoint (a : Agent) (d : Dialect)
    (hFresh : d.name ∉ a.dialects.map Dialect.name) :
    ∀ d' ∈ a.dialects, d'.name ≠ d.name := by
  intro d' hd' heq
  apply hFresh
  simp [List.mem_map]
  exact ⟨d', hd', heq⟩

theorem r3_fresh_unambiguous (d : Dialect)
    (hR3 : verifyR3 d = true)
    (hNotBase : d.name ≠ "cbcl-base")
    (pname : String)
    (hInD : d.definesPerformative pname = true)
    (hCore : isCorePerformativeName pname = true) :
    False := by
  have := core_performative_not_in_r3_dialect d hNotBase hR3 pname hCore
  rw [this] at hInD
  exact absurd hInD (by decide)

-- ============================================================
-- Section 9: State-99 absorption for agentDetParser
-- ============================================================

private theorem agent99_step (a : Agent) (tok : Token) (stack : List Nat) :
    ((agentDetParser a).runStep (99, stack) tok).1 = 99 := by
  -- State 99 < langOffset (200), so decodeLangState 99 = none.
  -- agentDetParser falls through to headCheckDetParser, which absorbs at 99.
  have hdecode : decodeLangState 99 = none := by simp [decodeLangState, langOffset]
  cases stack with
  | nil =>
    cases tok <;> simp [DetParser.runStep, agentDetParser, hdecode, headCheckDetParser]
  | cons t r =>
    cases tok <;> simp [DetParser.runStep, agentDetParser, hdecode, headCheckDetParser]

private theorem agent99_foldl_pair (a : Agent) (tokens : List Token) (stack : List Nat) :
    ∃ s', List.foldl (agentDetParser a).runStep (99, stack) tokens = (99, s') := by
  induction tokens generalizing stack with
  | nil => exact ⟨stack, rfl⟩
  | cons tok rest ih =>
    simp only [List.foldl]
    have hstep : ∃ s', (agentDetParser a).runStep (99, stack) tok = (99, s') :=
      ⟨_, Prod.ext (agent99_step a tok stack) rfl⟩
    obtain ⟨s1, hs1⟩ := hstep; rw [hs1]; exact ih s1

private theorem agent_accept_99 (a : Agent) (stack : List Nat) :
    (agentDetParser a).accept 99 stack = false := by
  show (agentDetParser a).accept 99 stack = false
  simp only [agentDetParser]
  -- The accept function matches stack against [0] and all other patterns return false
  -- For stack = [0], it checks state == 3 and isLangAcceptState state
  -- 99 ≠ 3 and isLangAcceptState 99 = false
  cases stack with
  | nil => rfl
  | cons s rest =>
    -- Need to determine if s :: rest matches [0]
    cases rest with
    | cons _ _ =>
      -- s :: _ :: _ can't match [0]
      simp
    | nil =>
      -- stack = [s]
      cases s with
      | zero =>
        -- stack = [0], need to evaluate the conditionals
        simp [isLangAcceptState, decodeLangState, langOffset]
      | succ n =>
        -- stack = [n+1], doesn't match [0]
        simp

private theorem agent_run_false_99 (a : Agent) (tokens : List Token) (stack : List Nat) :
    (agentDetParser a).accept
      (List.foldl (agentDetParser a).runStep (99, stack) tokens).1
      (List.foldl (agentDetParser a).runStep (99, stack) tokens).2 = false := by
  obtain ⟨s', hs'⟩ := agent99_foldl_pair a tokens stack
  rw [hs']; exact agent_accept_99 a _

-- ============================================================
-- Section 10: agentDetParser agrees with agentLanguageDecide
-- ============================================================

/-- In state 2, agentDetParser agrees with headCheckDetParser (state 2 is not 1,
    and decodeLangState 2 = none since 2 < 200 = langOffset). -/
private def agent_process_aux (a : Agent) :
    (e : SExpr) → ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (agentDetParser a).runStep (2, stack) (tokenize e) = (2, stack) :=
  @SExpr.rec
    (fun e => ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (agentDetParser a).runStep (2, stack) (tokenize e) = (2, stack))
    (fun xs => ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (agentDetParser a).runStep (2, stack)
        ((xs.map tokenize).flatten) = (2, stack))
    (fun atom stack hne => by
      obtain ⟨top, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      cases atom <;>
        simp [tokenize, DetParser.runStep, agentDetParser, decodeLangState, langOffset,
              headCheckDetParser])
    (fun xs ih_xs stack hne => by
      obtain ⟨top, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [tokenize]
      rw [List.foldl_append, List.foldl_append]
      have h1 : List.foldl (agentDetParser a).runStep (2, top :: rest) [Token.lparen]
          = (2, 2 :: top :: rest) := by
        simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset, headCheckDetParser]
      rw [h1, ih_xs (2 :: top :: rest) (by simp)]
      simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset, headCheckDetParser])
    (fun stack _ => by simp)
    (fun x xs ih_x ih_xs stack hne => by
      show List.foldl _ (2, stack) ((tokenize x).append ((xs.map tokenize).flatten)) = (2, stack)
      rw [List.append_eq, List.foldl_append, ih_x stack hne]
      exact ih_xs stack hne)

private theorem agent_process_sexpr (a : Agent) (e : SExpr)
    (stack : List Nat) (hne : stack ≠ []) :
    List.foldl (agentDetParser a).runStep (2, stack) (tokenize e) = (2, stack) :=
  agent_process_aux a e stack hne

private theorem agent_process_sexprs (a : Agent) (es : List SExpr)
    (stack : List Nat) (hne : stack ≠ []) :
    List.foldl (agentDetParser a).runStep (2, stack)
               ((es.map tokenize).flatten) = (2, stack) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    show List.foldl _ (2, stack) ((tokenize e).append ((es.map tokenize).flatten)) = (2, stack)
    rw [List.append_eq, List.foldl_append, agent_process_sexpr a e stack hne]; exact ih

-- ============================================================
-- Section 10: agentDetParser agrees with agentLanguageDecide
-- ============================================================

private theorem headCheckBool_agentHeadNames_split (s : String) (xs : List SExpr) :
    headCheckBool agentHeadNames (.list (.atom (.symbol s) :: xs)) =
      (headCheckBool corePerformativeNames (.list (.atom (.symbol s) :: xs)) ||
       headCheckBool ["meta"] (.list (.atom (.symbol s) :: xs)) ||
       headCheckBool ["envelope", "signed", "with-limits"] (.list (.atom (.symbol s) :: xs))) := by
  simp only [headCheckBool, agentHeadNames, List.contains_append, Bool.or_assoc]
  congr 1
  simp only [List.contains, List.elem]
  cases (s == "meta") <;> simp

private theorem lang_not_in_agentHeadNames : "lang" ∉ agentHeadNames := by
  simp [agentHeadNames, corePerformativeNames, List.mem_cons]

private theorem agentLanguageDecide_rw (a : Agent) (e : SExpr) :
    agentLanguageDecide a e =
      (headCheckBool agentHeadNames e ||
       a.dialects.any (fun d => langCheckBool d.name d.performativeNames e)) := by
  simp only [agentLanguageDecide, langLanguageBool]
  cases e with
  | atom _ => simp [headCheckBool]
  | list xs =>
    cases xs with
    | nil => simp [headCheckBool]
    | cons x xs =>
      cases x with
      | list _ => simp [headCheckBool]
      | atom a' =>
        cases a' with
        | symbol s =>
          simp [headCheckBool_agentHeadNames_split, Bool.or_assoc]
        | str _ => simp [headCheckBool]
        | num _ => simp [headCheckBool]
        | bool _ => simp [headCheckBool]
        | keyword _ => simp [headCheckBool]

private theorem findDialectIdx_none_means {ds : List Dialect} {dn : String}
    (h : findDialectIdx ds dn = none) :
    ∀ d ∈ ds, d.name ≠ dn := by
  induction ds with
  | nil => intro d hd; cases hd
  | cons d0 ds ih =>
    intro d hd hname
    have hne0 : d0.name ≠ dn := by
      intro heq
      simp [findDialectIdx, beq_iff_eq.mpr heq] at h
    have hfds : findDialectIdx ds dn = none := by
      simp [findDialectIdx, show (d0.name == dn) = false from by simp [hne0]] at h
      cases hfds : findDialectIdx ds dn with
      | none => rfl
      | some i => simp [hfds] at h
    cases List.mem_cons.mp hd with
    | inl heq => subst heq; exact hne0 hname
    | inr hd' => exact ih hfds d hd' hname

private theorem langCheckBool_name_mismatch (d : Dialect) (dn : String)
    (hne : d.name ≠ dn) (xs : List SExpr) :
    langCheckBool d.name d.performativeNames
      (.list (.atom (.symbol "lang") :: .atom (.symbol dn) :: xs)) = false := by
  cases xs with
  | nil => simp [langCheckBool]
  | cons x xs' =>
    cases xs' with
    | cons _ _ => simp [langCheckBool]
    | nil =>
      cases x with
      | atom _ => simp [langCheckBool]
      | list ws =>
        cases ws with
        | nil => simp [langCheckBool]
        | cons w _ =>
          cases w with
          | list _ => simp [langCheckBool]
          | atom aw =>
            cases aw with
            | symbol _ =>
              simp only [langCheckBool]
              have : (dn == d.name) = false := by simp [Ne.symm hne]
              simp [this]
            | _ => simp [langCheckBool]

private theorem no_dialect_lang_false (ds : List Dialect) (dn : String) (xs : List SExpr)
    (h : findDialectIdx ds dn = none) :
    ds.any (fun d => langCheckBool d.name d.performativeNames
      (.list (.atom (.symbol "lang") :: .atom (.symbol dn) :: xs))) = false := by
  rw [List.any_eq_false]
  intro d hd
  rw [langCheckBool_name_mismatch d dn (findDialectIdx_none_means h d hd) xs]
  decide

private theorem listGet?_mem {α : Type} {xs : List α} {n : Nat} {x : α}
    (h : listGet? xs n = some x) : x ∈ xs := by
  induction xs generalizing n with
  | nil => cases h
  | cons y ys ih =>
    cases n with
    | zero => simp [listGet?] at h; subst h; exact List.Mem.head _
    | succ n => exact List.Mem.tail _ (ih (by simpa [listGet?] using h))

private theorem findDialectIdx_unique_eq {ds : List Dialect} {dn : String} {idx : Nat}
    {d d' : Dialect}
    (hnd : (ds.map Dialect.name).Nodup)
    (hfind : findDialectIdx ds dn = some idx)
    (hget : listGet? ds idx = some d)
    (_hname : d.name = dn)
    (hmem : d' ∈ ds) (hname' : d'.name = dn) : d' = d := by
  have ⟨idx', hidx', hget'⟩ := findDialectIdx_unique hnd hmem hname'
  have : idx' = idx := by
    have := hfind; rw [hidx'] at this; exact Option.some.inj this
  subst this
  have := hget; rw [hget'] at this; exact Option.some.inj this

private theorem langCheckBool_true_name {dname dn : String} {perfNames : List String}
    {xs : List SExpr}
    (h : langCheckBool dname perfNames
      (.list (.atom (.symbol "lang") :: .atom (.symbol dn) :: xs)) = true) :
    dname = dn := by
  cases xs with
  | nil => simp [langCheckBool] at h
  | cons x rest =>
    cases rest with
    | cons _ _ => simp [langCheckBool] at h
    | nil =>
      cases x with
      | atom _ => simp [langCheckBool] at h
      | list ws =>
        cases ws with
        | nil => simp [langCheckBool] at h
        | cons w _ =>
          cases w with
          | list _ => simp [langCheckBool] at h
          | atom aw =>
            cases aw with
            | symbol _ =>
              simp only [langCheckBool, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.symm
            | str _ => simp [langCheckBool] at h
            | num _ => simp [langCheckBool] at h
            | bool _ => simp [langCheckBool] at h
            | keyword _ => simp [langCheckBool] at h

private theorem agent_accept_lang_eq (a : Agent) (idx : Nat) (s : Nat) (stack : List Nat)
    (hs : s < langStride) :
    (agentDetParser a).accept (langState idx s) stack =
      (langDetParser "" []).accept s stack := by
  simp only [agentDetParser, langDetParser]
  cases stack with
  | nil => simp
  | cons s0 rest =>
    cases rest with
    | cons _ _ => simp
    | nil =>
      cases s0 with
      | zero =>
        have hne3 : (langState idx s == 3) = false := by
          simp [langState, langOffset, langStride]; omega
        rw [isLangAcceptState_langState idx s hs]
        simp [hne3]
        by_cases h : s = 7
        · subst h; rfl
        · simp [h]
      | succ _ => simp

private theorem lang_accept_invariant (dname dname' : String) (perfNames perfNames' : List String)
    (s : Nat) (stack : List Nat) :
    (langDetParser dname perfNames).accept s stack =
      (langDetParser dname' perfNames').accept s stack := by
  simp [langDetParser]

-- Helper: for any list of dialects, langCheckBool universally false => any is false
private theorem any_langCheckBool_false_of
    (ds : List Dialect) (e : SExpr)
    (hfalse : ∀ d : Dialect, langCheckBool d.name d.performativeNames e = false) :
    ds.any (fun d => langCheckBool d.name d.performativeNames e) = false := by
  rw [List.any_eq_false]
  intro d _
  rw [hfalse d]
  decide

-- Helper: (x :: xs).map f).flatten = f x ++ (xs.map f).flatten
private theorem map_flatten_cons {α β : Type} (f : α → List β) (x : α) (xs : List α) :
    ((x :: xs).map f).flatten = f x ++ (xs.map f).flatten := by
  simp [List.map]

-- Helper to get `List.foldl f s [x] = f s x` as a rewrite
private theorem foldl_singleton {α β : Type} (f : α → β → α) (s : α) (x : β) :
    List.foldl f s [x] = f s x := by
  simp [List.foldl]

-- Generalized state-99 helpers
private theorem agent99_step_general (a : Agent) (config : Nat × List Nat) (tok : Token)
    (h : config.1 = 99) :
    ((agentDetParser a).runStep config tok).1 = 99 := by
  obtain ⟨s, stack⟩ := config; simp at h; subst h
  exact agent99_step a tok stack

private theorem agent99_foldl_general (a : Agent) (config : Nat × List Nat) (tokens : List Token)
    (h : config.1 = 99) :
    (List.foldl (agentDetParser a).runStep config tokens).1 = 99 := by
  induction tokens generalizing config with
  | nil => simpa
  | cons tok rest ih =>
    simp only [List.foldl]
    exact ih _ (agent99_step_general a config tok h)

private theorem agent_accept_fst_99 (a : Agent) (config : Nat × List Nat) (h : config.1 = 99) :
    (agentDetParser a).accept config.1 config.2 = false := by
  rw [h]; exact agent_accept_99 a _

-- langCheckBool_not_lang: when the head symbol is not "lang", langCheckBool is always false
private theorem langCheckBool_not_lang {s : String} (hs : s ≠ "lang") (dname : String)
    (perfNames : List String) (xs : List SExpr) :
    langCheckBool dname perfNames (.list (.atom (.symbol s) :: xs)) = false := by
  unfold langCheckBool
  split
  · rename_i heq
    -- The match succeeded, meaning the expression matched the pattern
    -- [atom (symbol "lang"), atom (symbol dn), list (atom (symbol perf) :: _)]
    -- This means s = "lang", contradicting hs
    simp at heq
    exact absurd heq.1 hs
  · rfl

theorem agentDetParser_agrees (a : Agent) (hnu : a.namesUnique) (e : SExpr) :
    (agentDetParser a).run (tokenize e) = agentLanguageDecide a e := by
  rw [agentLanguageDecide_rw]
  cases e with
  | atom at_ =>
    simp only [headCheckBool, Bool.false_or]
    rw [any_langCheckBool_false_of a.dialects _ (fun d => by cases at_ <;> simp [langCheckBool])]
    cases at_ <;> simp [DetParser.run, tokenize, List.foldl, DetParser.runStep, agentDetParser,
      decodeLangState, langOffset, headCheckDetParser]
  | list xs =>
    unfold DetParser.run
    simp only [tokenize]
    rw [List.foldl_append, List.foldl_append]
    simp only [List.foldl]
    have h_init : (agentDetParser a).runStep
        ((agentDetParser a).initState, (agentDetParser a).initStack)
        Token.lparen = (1, [1, 0]) := by
      simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset, headCheckDetParser]
    rw [h_init]
    cases xs with
    | nil =>
      simp only [headCheckBool, Bool.false_or, List.map, List.flatten]
      rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
      simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
            headCheckDetParser, isLangAcceptState]
    | cons x xs =>
      rw [map_flatten_cons, List.foldl_append]
      cases x with
      | list ys =>
        simp only [headCheckBool, tokenize]
        rw [List.foldl_append, List.foldl_append]
        simp only [List.foldl]
        have h_lp : (agentDetParser a).runStep (1, [1, 0]) Token.lparen
            = (99, [0]) := by
          simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset, headCheckDetParser]
        rw [h_lp]
        rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
        simp only [Bool.false_or]
        -- State is 99 after h_lp. Use general 99-absorption.
        -- Goal has a complex expression but the state is always 99.
        -- Let config = final state after all remaining tokens
        -- config.1 = 99 by agent99_foldl_general / agent99_step_general
        apply agent_accept_fst_99
        apply agent99_step_general
        apply agent99_foldl_general
        apply agent99_step_general
        apply agent99_foldl_general
        rfl
      | atom at_ =>
        cases at_ with
        | symbol s =>
          simp only [tokenize, List.foldl]
          by_cases hslang : s = "lang"
          · subst hslang
            have hhc : headCheckBool agentHeadNames
                (.list (.atom (.symbol "lang") :: xs)) = false := by
              simp [headCheckBool]; exact fun h => absurd h lang_not_in_agentHeadNames
            simp only [hhc, Bool.false_or]
            have h_step1 : (agentDetParser a).runStep (1, [1, 0]) (.sym "lang")
                = (langState 0 0, [1, 0]) := by
              simp [DetParser.runStep, agentDetParser, langState, langOffset, langStride]
            rw [h_step1]
            cases xs with
            | nil =>
              rw [any_langCheckBool_false_of _ _ (fun d => by simp [langCheckBool])]
              simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset, langStride,
                    langState, isLangAcceptState, List.map]
            | cons x2 xs2 =>
              rw [map_flatten_cons, List.foldl_append]
              cases x2 with
              | list ys2 =>
                simp only [tokenize]
                rw [List.foldl_append, List.foldl_append]
                simp only [List.foldl]
                have h_lp : (agentDetParser a).runStep (langState 0 0, [1, 0]) Token.lparen
                    = (99, [0]) := by
                  simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                        langStride, langState]
                rw [h_lp]
                rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
                apply agent_accept_fst_99
                apply agent99_step_general
                apply agent99_foldl_general
                apply agent99_step_general
                apply agent99_foldl_general
                rfl
              | atom at2 =>
                cases at2 with
                | symbol dn =>
                  simp only [tokenize, List.foldl]
                  cases hfind : findDialectIdx a.dialects dn with
                  | none =>
                    have h_step2 : (agentDetParser a).runStep (langState 0 0, [1, 0]) (.sym dn)
                        = (99, [0]) := by
                      simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                            langStride, langState, hfind]
                    rw [h_step2, no_dialect_lang_false a.dialects dn xs2 hfind]
                    apply agent_accept_fst_99
                    apply agent99_step_general
                    apply agent99_foldl_general
                    rfl
                  | some idx =>
                    obtain ⟨d, hget, hname⟩ := findDialectIdx_get? hfind
                    have h_step2 : (agentDetParser a).runStep (langState 0 0, [1, 0]) (.sym dn)
                        = (langState idx 3, [1, 0]) := by
                      simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                            langStride, langState, hfind]
                    rw [h_step2]
                    have hslt3 : (3 : Nat) < langStride := by simp [langStride]
                    have hne3 : (3 : Nat) ≠ 0 := by decide
                    -- Use agentDetParser_run_lang_aux for the FULL remaining tokens including rparen
                    have h_full := agentDetParser_run_lang_aux a d idx 3
                      ((xs2.map tokenize).flatten ++ [Token.rparen]) [1, 0] hne3 hslt3 hget
                    rw [List.foldl_append, foldl_singleton] at h_full
                    -- h_full says the agent runStep pair equals a let expression.
                    -- We need to extract .1 and .2.
                    -- The let in h_full doesn't auto-reduce; we need to help it.
                    -- Instead, rewrite h_full's RHS to reduce the let.
                    have h_full' : (agentDetParser a).runStep
                        (List.foldl (agentDetParser a).runStep (langState idx 3, [1, 0])
                          ((xs2.map tokenize).flatten))
                        Token.rparen =
                        (langState idx
                          ((langDetParser d.name d.performativeNames).runStep
                            (List.foldl (langDetParser d.name d.performativeNames).runStep
                              (3, [1, 0]) ((xs2.map tokenize).flatten))
                            Token.rparen).1,
                         ((langDetParser d.name d.performativeNames).runStep
                            (List.foldl (langDetParser d.name d.performativeNames).runStep
                              (3, [1, 0]) ((xs2.map tokenize).flatten))
                            Token.rparen).2) := by
                      rw [h_full]
                      -- Now LHS = RHS but RHS has the let reduced
                      simp only [List.foldl_append, foldl_singleton]
                    rw [h_full']
                    -- Get the state bound for accept
                    have hrf_lt : ((langDetParser d.name d.performativeNames).runStep
                        (List.foldl (langDetParser d.name d.performativeNames).runStep
                          (3, [1, 0]) ((xs2.map tokenize).flatten))
                        Token.rparen).1 < langStride := by
                      have h := langDetParser_step_state_lt d.name d.performativeNames
                        (List.foldl (langDetParser d.name d.performativeNames).runStep
                          (3, [1, 0]) ((xs2.map tokenize).flatten)).1
                        Token.rparen
                        (List.foldl (langDetParser d.name d.performativeNames).runStep
                          (3, [1, 0]) ((xs2.map tokenize).flatten)).2.head?
                      simpa [DetParser.runStep] using h
                    -- Relate accept
                    rw [agent_accept_lang_eq a idx _ _ hrf_lt]
                    rw [lang_accept_invariant "" d.name [] d.performativeNames]
                    -- Use langCheck_agrees
                    have hlca := langCheck_agrees d.name d.performativeNames
                      (.list (.atom (.symbol "lang") :: .atom (.symbol dn) :: xs2))
                    unfold DetParser.run at hlca
                    simp only [tokenize] at hlca
                    rw [List.foldl_append, List.foldl_append] at hlca
                    simp only [List.foldl] at hlca
                    have hlp : (langDetParser d.name d.performativeNames).runStep
                        ((langDetParser d.name d.performativeNames).initState,
                         (langDetParser d.name d.performativeNames).initStack)
                        Token.lparen = (1, [1, 0]) := by
                      simp [DetParser.runStep, langDetParser]
                    rw [hlp] at hlca
                    rw [map_flatten_cons] at hlca
                    rw [List.foldl_append] at hlca
                    simp only [tokenize, List.foldl] at hlca
                    -- Now hlca has: runStep (1,[1,0]) (sym "lang") applied, then foldl over (map tokenize (sym dn :: xs2)).flatten
                    -- Split the (sym dn :: xs2) cons
                    rw [map_flatten_cons] at hlca
                    rw [List.foldl_append] at hlca
                    simp only [tokenize, List.foldl] at hlca
                    -- Now we have: runStep (runStep ... (sym "lang")) (sym dn) = (3, [1,0])
                    have hlang_step :
                        (langDetParser d.name d.performativeNames).runStep
                          ((langDetParser d.name d.performativeNames).runStep (1, [1, 0])
                            (Token.sym "lang"))
                          (Token.sym dn) = (3, [1, 0]) := by
                      simp [DetParser.runStep, langDetParser, hname]
                    rw [hlang_step] at hlca
                    rw [hlca]
                    -- Goal: langCheckBool d.name ... = any (...)
                    symm; rw [Bool.eq_iff_iff]; constructor
                    · intro hany
                      rw [List.any_eq_true] at hany
                      obtain ⟨d', hd'mem, hd'check⟩ := hany
                      have hd'name : d'.name = dn := langCheckBool_true_name hd'check
                      have : d' = d :=
                        findDialectIdx_unique_eq hnu hfind hget hname hd'mem hd'name
                      subst this; exact hd'check
                    · intro hcheck
                      rw [List.any_eq_true]
                      exact ⟨d, listGet?_mem hget, hcheck⟩
                | str u =>
                  simp only [tokenize, List.foldl]
                  have h_step : (agentDetParser a).runStep (langState 0 0, [1, 0]) (.str u)
                      = (99, [0]) := by
                    simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                          langStride, langState]
                  rw [h_step]
                  rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
                  apply agent_accept_fst_99
                  apply agent99_step_general
                  apply agent99_foldl_general
                  rfl
                | num n =>
                  simp only [tokenize, List.foldl]
                  have h_step : (agentDetParser a).runStep (langState 0 0, [1, 0]) (.num n)
                      = (99, [0]) := by
                    simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                          langStride, langState]
                  rw [h_step]
                  rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
                  apply agent_accept_fst_99
                  apply agent99_step_general
                  apply agent99_foldl_general
                  rfl
                | bool b =>
                  simp only [tokenize, List.foldl]
                  have h_step : (agentDetParser a).runStep (langState 0 0, [1, 0]) (.bool_ b)
                      = (99, [0]) := by
                    simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                          langStride, langState]
                  rw [h_step]
                  rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
                  apply agent_accept_fst_99
                  apply agent99_step_general
                  apply agent99_foldl_general
                  rfl
                | keyword k =>
                  simp only [tokenize, List.foldl]
                  have h_step : (agentDetParser a).runStep (langState 0 0, [1, 0]) (.kw k)
                      = (99, [0]) := by
                    simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                          langStride, langState]
                  rw [h_step]
                  rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
                  apply agent_accept_fst_99
                  apply agent99_step_general
                  apply agent99_foldl_general
                  rfl
          · have hlang_any_false : a.dialects.any (fun d => langCheckBool d.name d.performativeNames
                (.list (.atom (.symbol s) :: xs))) = false :=
              any_langCheckBool_false_of _ _ (fun d => langCheckBool_not_lang hslang _ _ _)
            have h_step1 : (agentDetParser a).runStep (1, [1, 0]) (.sym s) =
                (headCheckDetParser agentHeadNames).runStep (1, [1, 0]) (.sym s) := by
              show (let r := (agentDetParser a).step 1 (.sym s) (some 1);
                    (r.1, r.2 ++ [0])) =
                   (let r := (headCheckDetParser agentHeadNames).step 1 (.sym s) (some 1);
                    (r.1, r.2 ++ [0]))
              congr 1
              simp [agentDetParser, if_neg hslang]
            rw [h_step1]
            by_cases hc : agentHeadNames.contains s = true
            · have hm := List.mem_of_elem_eq_true hc
              have h_hstep : (headCheckDetParser agentHeadNames).runStep (1, [1, 0]) (.sym s)
                  = (2, [1, 0]) := by
                simp [DetParser.runStep, headCheckDetParser, hm]
              rw [h_hstep]
              rw [agent_process_sexprs a xs [1, 0] (by simp)]
              -- After processing xs tokens, state is (2, [1, 0])
              -- Then rparen step gives accept state
              -- headCheckBool is true, so RHS is true || ... = true
              have hhead : headCheckBool agentHeadNames
                  (.list (.atom (.symbol s) :: xs)) = true := by
                simp [headCheckBool, hm]
              rw [hhead, hlang_any_false]
              simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                    headCheckDetParser]
            · simp only [Bool.not_eq_true] at hc
              have hnm : s ∉ agentHeadNames := by
                intro hm
                have := List.elem_eq_true_of_mem hm
                rw [List.contains] at hc
                exact absurd this (by rw [Bool.not_eq_true]; exact hc)
              have h_hstep : (headCheckDetParser agentHeadNames).runStep (1, [1, 0]) (.sym s)
                  = (99, [0]) := by
                simp [DetParser.runStep, headCheckDetParser, hnm]
              rw [h_hstep]
              rw [show headCheckBool agentHeadNames
                  (.list (.atom (.symbol s) :: xs)) = false from by
                simp [headCheckBool, hnm]]
              simp only [Bool.false_or]
              rw [hlang_any_false]
              apply agent_accept_fst_99
              apply agent99_step_general
              apply agent99_foldl_general
              rfl
        | str u =>
          simp only [tokenize, List.foldl]
          have h_step : (agentDetParser a).runStep (1, [1, 0]) (.str u) = (99, [0]) := by
            simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                  headCheckDetParser]
          rw [h_step]; simp [headCheckBool]
          rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
          apply agent_accept_fst_99
          apply agent99_step_general
          apply agent99_foldl_general
          rfl
        | num n =>
          simp only [tokenize, List.foldl]
          have h_step : (agentDetParser a).runStep (1, [1, 0]) (.num n) = (99, [0]) := by
            simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                  headCheckDetParser]
          rw [h_step]; simp [headCheckBool]
          rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
          apply agent_accept_fst_99
          apply agent99_step_general
          apply agent99_foldl_general
          rfl
        | bool b =>
          simp only [tokenize, List.foldl]
          have h_step : (agentDetParser a).runStep (1, [1, 0]) (.bool_ b) = (99, [0]) := by
            simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                  headCheckDetParser]
          rw [h_step]; simp [headCheckBool]
          rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
          apply agent_accept_fst_99
          apply agent99_step_general
          apply agent99_foldl_general
          rfl
        | keyword k =>
          simp only [tokenize, List.foldl]
          have h_step : (agentDetParser a).runStep (1, [1, 0]) (.kw k) = (99, [0]) := by
            simp [DetParser.runStep, agentDetParser, decodeLangState, langOffset,
                  headCheckDetParser]
          rw [h_step]; simp [headCheckBool]
          rw [any_langCheckBool_false_of a.dialects _ (fun d => by simp [langCheckBool])]
          apply agent_accept_fst_99
          apply agent99_step_general
          apply agent99_foldl_general
          rfl

-- ============================================================
-- Section 11: IsDCFL instance and DCFL preservation
-- ============================================================

/-- Given unique dialect names, `agentLanguage a` is a DCFL, recognized by `agentDetParser a`. -/
def agentLanguage_isDCFL (a : Agent) (hnu : a.namesUnique) : IsDCFL (agentLanguage a) where
  parser := agentDetParser a
  sound := fun e h => by
    have := agentDetParser_agrees a hnu e
    rw [this] at h
    exact agentLanguage_sound' a e h
  complete := fun e h => by
    have := agentDetParser_agrees a hnu e
    rw [this]
    exact agentLanguage_complete' a e h

private theorem namesUnique_installDialect {a : Agent} {d : Dialect}
    (hnu : a.namesUnique)
    (hFresh : d.name ∉ a.dialects.map Dialect.name) :
    (a.installDialect d).namesUnique := by
  simp only [Agent.namesUnique, Agent.installDialect, List.map_append, List.map]
  rw [List.nodup_append]
  refine ⟨hnu, List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩, ?_⟩
  · exact fun h => by cases h
  · intro x hx y hy
    simp [List.mem_cons] at hy
    subst hy; intro heq; exact hFresh (heq ▸ hx)

/-- **Main theorem**: installing a dialect with a fresh name into an
    agent with unique dialect names preserves DCFL membership.

    DCFL is a closure property of the grammar union and depends only on
    uniqueness of dialect names (for deterministic dispatch) and
    freshness of the incoming name. Earlier versions of this theorem
    carried `_hwf : a.wellFormed` and `_hR3 : verifyR3 d = true` as
    premises; neither was consumed by the proof. They were removed in
    the Lean-audit fix session because R3 is a semantic-core constraint
    on performative names, not a structural constraint on grammar
    tokens — it is at the wrong layer to participate in a DCFL closure
    proof. See the camera-ready paper's Section 4 for the prose
    context; the next public revision should narrow the prose claim to
    match this theorem. -/
def dcfl_preserved (a : Agent) (d : Dialect)
    (hnu : a.namesUnique)
    (hFresh : d.name ∉ a.dialects.map Dialect.name) :
    IsDCFL (agentLanguage (a.installDialect d)) :=
  agentLanguage_isDCFL (a.installDialect d) (namesUnique_installDialect hnu hFresh)

end CBCL
