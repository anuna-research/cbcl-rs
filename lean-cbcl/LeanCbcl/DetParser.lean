import LeanCbcl.SExpr

/-!
# Deterministic Pushdown Parser for CBCL

Defines a token-stream representation of S-expressions and a deterministic
pushdown automaton (DPDA) framework.  Provides concrete DPDAs for head-symbol
checking and lang-wrapped dialect messages, together with correctness proofs
that each DPDA agrees with its Boolean reference validator.
-/

namespace CBCL

-- ============================================================
-- Section 1: Token type
-- ============================================================

inductive Token where
  | lparen | rparen
  | sym : String → Token
  | str : String → Token
  | num : Int → Token
  | bool_ : Bool → Token
  | kw : String → Token
  deriving BEq, DecidableEq, Repr, Inhabited

-- ============================================================
-- Section 2: tokenize
-- ============================================================

def tokenize : SExpr → List Token
  | .atom (.symbol s)  => [.sym s]
  | .atom (.str s)     => [.str s]
  | .atom (.num n)     => [.num n]
  | .atom (.bool b)    => [.bool_ b]
  | .atom (.keyword k) => [.kw k]
  | .list xs => [.lparen] ++ (xs.map tokenize).flatten ++ [.rparen]

-- ============================================================
-- Section 3: DetParser structure
-- ============================================================

structure DetParser where
  step : Nat → Token → Option Nat → Nat × List Nat
  accept : Nat → List Nat → Bool
  initState : Nat := 0
  initStack : List Nat := [0]

def DetParser.runStep (p : DetParser) (config : Nat × List Nat) (tok : Token) : Nat × List Nat :=
  let (state, stack) := config
  let (state', pushSyms) := p.step state tok stack.head?
  (state', pushSyms ++ stack.drop 1)

def DetParser.run (p : DetParser) (tokens : List Token) : Bool :=
  let final := tokens.foldl p.runStep (p.initState, p.initStack)
  p.accept final.1 final.2

-- ============================================================
-- Section 4: IsDCFL and IsDecidable
-- ============================================================

structure IsDCFL (L : SExpr → Prop) where
  parser : DetParser
  sound : ∀ e, parser.run (tokenize e) = true → L e
  complete : ∀ e, L e → parser.run (tokenize e) = true

structure IsDecidable (L : SExpr → Prop) where
  decide_ : SExpr → Bool
  sound : ∀ e, decide_ e = true → L e
  complete : ∀ e, L e → decide_ e = true

def IsDCFL.toDecidable {L : SExpr → Prop} (h : IsDCFL L) : IsDecidable L where
  decide_ := fun e => h.parser.run (tokenize e)
  sound := h.sound
  complete := h.complete

-- ============================================================
-- Section 5: Basic tokenize properties
-- ============================================================

theorem tokenize_atom_len (a : Atom) : (tokenize (.atom a)).length = 1 := by
  cases a <;> simp [tokenize]

theorem tokenize_list_len (xs : List SExpr) : (tokenize (.list xs)).length ≥ 2 := by
  simp [tokenize]

theorem tokenize_list_head (xs : List SExpr) :
    (tokenize (.list xs)).head? = some Token.lparen := by
  simp [tokenize]

theorem tokenize_list_last (xs : List SExpr) :
    (tokenize (.list xs)).getLast? = some Token.rparen := by
  simp only [tokenize]
  rw [List.getLast?_append]
  simp

-- ============================================================
-- Section 6: headCheckDetParser
-- ============================================================

def headCheckDetParser (heads : List String) : DetParser where
  step := fun state tok top =>
    match state, tok, top with
    | 0, .lparen, some 0 => (1, [1, 0])
    | 1, .sym s, some 1  => if heads.contains s then (2, [1]) else (99, [])
    | 2, .lparen, some s  => (2, [2, s])
    | 2, .rparen, some 2  => (2, [])
    | 2, .rparen, some 1  => (3, [])
    | 2, _, some s         => (2, [s])
    | _, _, _              => (99, [])
  accept := fun state stack =>
    match state, stack with
    | 3, [0] => true
    | _, _   => false

def headCheckBool (heads : List String) (e : SExpr) : Bool :=
  match e with
  | .list (.atom (.symbol s) :: _) => heads.contains s
  | _ => false

-- ============================================================
-- Section 7: contains / membership helpers
-- ============================================================

private theorem contains_to_mem {l : List String} {a : String}
    (h : l.contains a = true) : a ∈ l :=
  List.mem_of_elem_eq_true h

private theorem not_contains_to_not_mem {l : List String} {a : String}
    (h : l.contains a = false) : a ∉ l := by
  intro hm
  have h2 : List.elem a l = true := List.elem_eq_true_of_mem hm
  change List.elem a l = false at h
  rw [h2] at h; exact absurd h (by decide)

-- ============================================================
-- Section 8: state-99 rejection lemmas (generic for any DPDA with absorbing 99)
-- ============================================================

private theorem hc99_step (heads : List String) (tok : Token) (stack : List Nat) :
    ((headCheckDetParser heads).runStep (99, stack) tok).1 = 99 := by
  cases stack with
  | nil => cases tok <;> simp [DetParser.runStep, headCheckDetParser]
  | cons t r => cases tok <;> simp [DetParser.runStep, headCheckDetParser]

private theorem hc99_foldl_pair (heads : List String) (tokens : List Token) (stack : List Nat) :
    ∃ s', List.foldl (headCheckDetParser heads).runStep (99, stack) tokens = (99, s') := by
  induction tokens generalizing stack with
  | nil => exact ⟨stack, rfl⟩
  | cons tok rest ih =>
    simp only [List.foldl]
    have hstep : ∃ s', (headCheckDetParser heads).runStep (99, stack) tok = (99, s') :=
      ⟨_, Prod.ext (hc99_step heads tok stack) rfl⟩
    obtain ⟨s1, hs1⟩ := hstep; rw [hs1]; exact ih s1

private theorem hc_accept_99 (heads : List String) (stack : List Nat) :
    (headCheckDetParser heads).accept 99 stack = false := by
  simp [headCheckDetParser]

private theorem hc_run_false_99 (heads : List String) (tokens : List Token) (stack : List Nat) :
    (headCheckDetParser heads).accept
      (List.foldl (headCheckDetParser heads).runStep (99, stack) tokens).1
      (List.foldl (headCheckDetParser heads).runStep (99, stack) tokens).2 = false := by
  obtain ⟨s', hs'⟩ := hc99_foldl_pair heads tokens stack
  rw [hs']; exact hc_accept_99 heads _

private theorem hc_step_false_99 (heads : List String) (tok : Token) (stack : List Nat) :
    (headCheckDetParser heads).accept
      ((headCheckDetParser heads).runStep (99, stack) tok).1
      ((headCheckDetParser heads).runStep (99, stack) tok).2 = false := by
  have h := hc99_step heads tok stack
  have heq : (headCheckDetParser heads).runStep (99, stack) tok =
    (99, ((headCheckDetParser heads).runStep (99, stack) tok).2) := Prod.ext h rfl
  rw [heq]; exact hc_accept_99 heads _

-- ============================================================
-- Section 9: headCheck process_sexpr (structural induction via SExpr.rec)
-- ============================================================

def headCheck_process_aux (heads : List String) :
    (e : SExpr) → ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (headCheckDetParser heads).runStep (2, stack) (tokenize e) = (2, stack) :=
  @SExpr.rec
    (fun e => ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (headCheckDetParser heads).runStep (2, stack) (tokenize e) = (2, stack))
    (fun xs => ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (headCheckDetParser heads).runStep (2, stack)
        ((xs.map tokenize).flatten) = (2, stack))
    (fun a stack hne => by
      obtain ⟨top, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      cases a <;> simp [tokenize, DetParser.runStep, headCheckDetParser])
    (fun xs ih_xs stack hne => by
      obtain ⟨top, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [tokenize]
      rw [List.foldl_append, List.foldl_append]
      have h1 : List.foldl (headCheckDetParser heads).runStep (2, top :: rest) [Token.lparen]
          = (2, 2 :: top :: rest) := by simp [DetParser.runStep, headCheckDetParser]
      rw [h1, ih_xs (2 :: top :: rest) (by simp)]
      simp [DetParser.runStep, headCheckDetParser])
    (fun stack _ => by simp)
    (fun x xs ih_x ih_xs stack hne => by
      show List.foldl _ (2, stack) ((tokenize x).append ((xs.map tokenize).flatten)) = (2, stack)
      rw [List.append_eq, List.foldl_append, ih_x stack hne]
      exact ih_xs stack hne)

theorem headCheck_process_sexpr (heads : List String) (e : SExpr)
    (stack : List Nat) (hne : stack ≠ []) :
    List.foldl (headCheckDetParser heads).runStep (2, stack) (tokenize e) = (2, stack) :=
  headCheck_process_aux heads e stack hne

theorem headCheck_process_sexprs (heads : List String) (es : List SExpr)
    (stack : List Nat) (hne : stack ≠ []) :
    List.foldl (headCheckDetParser heads).runStep (2, stack)
               ((es.map tokenize).flatten) = (2, stack) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    show List.foldl _ (2, stack) ((tokenize e).append ((es.map tokenize).flatten)) = (2, stack)
    rw [List.append_eq, List.foldl_append, headCheck_process_sexpr heads e stack hne]; exact ih

-- ============================================================
-- Section 10: headCheck_agrees
-- ============================================================

theorem headCheck_agrees (heads : List String) (e : SExpr) :
    (headCheckDetParser heads).run (tokenize e) = headCheckBool heads e := by
  cases e with
  | atom a =>
    cases a <;> simp [headCheckBool, DetParser.run, tokenize, List.foldl,
                       DetParser.runStep, headCheckDetParser]
  | list xs =>
    unfold DetParser.run
    simp only [tokenize]
    rw [List.foldl_append, List.foldl_append]
    have h_init : List.foldl (headCheckDetParser heads).runStep
        ((headCheckDetParser heads).initState, (headCheckDetParser heads).initStack)
        [Token.lparen] = (1, [1, 0]) := by
      simp [DetParser.runStep, headCheckDetParser]
    rw [h_init]
    cases xs with
    | nil =>
      simp [headCheckBool, DetParser.runStep, headCheckDetParser]
    | cons x xs =>
      -- Inner tokens = tokenize x ++ (xs.map tokenize).flatten
      show (headCheckDetParser heads).accept
          (List.foldl (headCheckDetParser heads).runStep
            (List.foldl (headCheckDetParser heads).runStep (1, [1, 0])
              ((tokenize x).append ((xs.map tokenize).flatten))) [Token.rparen]).1
          (List.foldl (headCheckDetParser heads).runStep
            (List.foldl (headCheckDetParser heads).runStep (1, [1, 0])
              ((tokenize x).append ((xs.map tokenize).flatten))) [Token.rparen]).2 =
        headCheckBool heads (.list (x :: xs))
      rw [List.append_eq, List.foldl_append]
      cases x with
      | atom a =>
        cases a with
        | symbol s =>
          -- tokenize (.atom (.symbol s)) = [.sym s]
          simp only [tokenize, List.foldl]
          by_cases hc : heads.contains s = true
          · have hm := contains_to_mem hc
            have h_step : (headCheckDetParser heads).runStep (1, [1, 0]) (.sym s) = (2, [1, 0]) := by
              simp [DetParser.runStep, headCheckDetParser, hm]
            rw [h_step, headCheck_process_sexprs heads xs [1, 0] (by simp)]
            simp [headCheckBool, DetParser.runStep, headCheckDetParser, hm]
          · simp only [Bool.not_eq_true] at hc
            have hnm := not_contains_to_not_mem hc
            have h_step : (headCheckDetParser heads).runStep (1, [1, 0]) (.sym s) = (99, [0]) := by
              simp [DetParser.runStep, headCheckDetParser, hnm]
            rw [h_step, show headCheckBool heads (.list (.atom (.symbol s) :: xs)) = false from by
              simp [headCheckBool, hnm]]
            obtain ⟨s1, hs1⟩ := hc99_foldl_pair heads ((xs.map tokenize).flatten) [0]
            rw [hs1]; simp [DetParser.runStep, headCheckDetParser]
        | str s =>
          simp only [tokenize, List.foldl]
          have h_step : (headCheckDetParser heads).runStep (1, [1, 0]) (.str s) = (99, [0]) := by
            simp [DetParser.runStep, headCheckDetParser]
          rw [h_step, show headCheckBool heads (.list (.atom (.str s) :: xs)) = false from by
            simp [headCheckBool]]
          obtain ⟨s1, hs1⟩ := hc99_foldl_pair heads ((xs.map tokenize).flatten) [0]
          rw [hs1]; simp [DetParser.runStep, headCheckDetParser]
        | num n =>
          simp only [tokenize, List.foldl]
          have h_step : (headCheckDetParser heads).runStep (1, [1, 0]) (.num n) = (99, [0]) := by
            simp [DetParser.runStep, headCheckDetParser]
          rw [h_step, show headCheckBool heads (.list (.atom (.num n) :: xs)) = false from by
            simp [headCheckBool]]
          obtain ⟨s1, hs1⟩ := hc99_foldl_pair heads ((xs.map tokenize).flatten) [0]
          rw [hs1]; simp [DetParser.runStep, headCheckDetParser]
        | bool b =>
          simp only [tokenize, List.foldl]
          have h_step : (headCheckDetParser heads).runStep (1, [1, 0]) (.bool_ b) = (99, [0]) := by
            simp [DetParser.runStep, headCheckDetParser]
          rw [h_step, show headCheckBool heads (.list (.atom (.bool b) :: xs)) = false from by
            simp [headCheckBool]]
          obtain ⟨s1, hs1⟩ := hc99_foldl_pair heads ((xs.map tokenize).flatten) [0]
          rw [hs1]; simp [DetParser.runStep, headCheckDetParser]
        | keyword k =>
          simp only [tokenize, List.foldl]
          have h_step : (headCheckDetParser heads).runStep (1, [1, 0]) (.kw k) = (99, [0]) := by
            simp [DetParser.runStep, headCheckDetParser]
          rw [h_step, show headCheckBool heads (.list (.atom (.keyword k) :: xs)) = false from by
            simp [headCheckBool]]
          obtain ⟨s1, hs1⟩ := hc99_foldl_pair heads ((xs.map tokenize).flatten) [0]
          rw [hs1]; simp [DetParser.runStep, headCheckDetParser]
      | list ys =>
        -- tokenize (.list ys) = [.lparen] ++ inner ++ [.rparen]
        simp only [tokenize]
        rw [List.foldl_append, List.foldl_append]
        -- foldl (1, [1, 0]) [.lparen] = (99, [0]) since state 1 + lparen → 99
        have h_lp : List.foldl (headCheckDetParser heads).runStep (1, [1, 0]) [Token.lparen]
            = (99, [0]) := by
          simp [DetParser.runStep, headCheckDetParser]
        rw [h_lp, show headCheckBool heads (.list (.list ys :: xs)) = false from by
          simp [headCheckBool]]
        obtain ⟨s1, hs1⟩ := hc99_foldl_pair heads ((ys.map tokenize).flatten) [0]
        rw [hs1]
        obtain ⟨s2, hs2⟩ := hc99_foldl_pair heads [Token.rparen] s1
        rw [hs2]
        obtain ⟨s3, hs3⟩ := hc99_foldl_pair heads ((xs.map tokenize).flatten) s2
        rw [hs3]; simp [DetParser.runStep, headCheckDetParser]

-- ============================================================
-- Section 11: langDetParser
-- ============================================================

def langDetParser (dname : String) (perfNames : List String) : DetParser where
  step := fun state tok top =>
    match state, tok, top with
    | 0, .lparen, some 0  => (1, [1, 0])
    | 1, .sym s, some 1   => if s == "lang" then (2, [1]) else (99, [])
    | 2, .sym s, some 1   => if s == dname then (3, [1]) else (99, [])
    | 3, .lparen, some 1  => (4, [2, 1])
    | 4, .sym s, some 2   => if perfNames.contains s then (5, [2]) else (99, [])
    | 5, .lparen, some s   => (5, [3, s])
    | 5, .rparen, some 3   => (5, [])
    | 5, .rparen, some 2   => (6, [])
    | 5, _, some s          => (5, [s])
    | 6, .rparen, some 1   => (7, [])
    | _, _, _               => (99, [])
  accept := fun state stack =>
    match state, stack with
    | 7, [0] => true
    | _, _   => false

@[simp] theorem lang_step_lang_eq_lt (a : String) :
    ((if a = "lang" then (2, [1]) else (99, [])).1 : Nat) < 200 := by
  by_cases h : a = "lang" <;> simp [h]

@[simp] theorem lang_step_lang_eq_ne_zero (a : String) :
    ((if a = "lang" then (2, [1]) else (99, [])).1 : Nat) ≠ 0 := by
  by_cases h : a = "lang" <;> simp [h]

@[simp] theorem lang_step_dname_eq_lt (a dname : String) :
    ((if a = dname then (3, [1]) else (99, [])).1 : Nat) < 200 := by
  by_cases h : a = dname <;> simp [h]

@[simp] theorem lang_step_dname_eq_ne_zero (a dname : String) :
    ((if a = dname then (3, [1]) else (99, [])).1 : Nat) ≠ 0 := by
  by_cases h : a = dname <;> simp [h]

@[simp] theorem lang_step_perf_mem_lt (a : String) (perfNames : List String) :
    ((if a ∈ perfNames then (5, [2]) else (99, [])).1 : Nat) < 200 := by
  by_cases h : a ∈ perfNames <;> simp [h]

@[simp] theorem lang_step_perf_mem_ne_zero (a : String) (perfNames : List String) :
    ((if a ∈ perfNames then (5, [2]) else (99, [])).1 : Nat) ≠ 0 := by
  by_cases h : a ∈ perfNames <;> simp [h]

@[simp] theorem lang_step_lang_lt (a : String) :
    ((if a == "lang" then (2, [1]) else (99, [])).1 : Nat) < 200 := by
  by_cases h : a == "lang" <;> simp [h]

@[simp] theorem lang_step_lang_ne_zero (a : String) :
    ((if a == "lang" then (2, [1]) else (99, [])).1 : Nat) ≠ 0 := by
  by_cases h : a == "lang" <;> simp [h]

@[simp] theorem lang_step_dname_lt (a dname : String) :
    ((if a == dname then (3, [1]) else (99, [])).1 : Nat) < 200 := by
  by_cases h : a == dname <;> simp [h]

@[simp] theorem lang_step_dname_ne_zero (a dname : String) :
    ((if a == dname then (3, [1]) else (99, [])).1 : Nat) ≠ 0 := by
  by_cases h : a == dname <;> simp [h]

@[simp] theorem lang_step_perf_lt (a : String) (perfNames : List String) :
    ((if perfNames.contains a then (5, [2]) else (99, [])).1 : Nat) < 200 := by
  cases h : perfNames.contains a <;> simp

@[simp] theorem lang_step_perf_ne_zero (a : String) (perfNames : List String) :
    ((if perfNames.contains a then (5, [2]) else (99, [])).1 : Nat) ≠ 0 := by
  cases h : perfNames.contains a <;> simp

@[simp] theorem one_lt_200 : (1 : Nat) < 200 := by decide
@[simp] theorem two_lt_200 : (2 : Nat) < 200 := by decide
@[simp] theorem three_lt_200 : (3 : Nat) < 200 := by decide
@[simp] theorem four_lt_200 : (4 : Nat) < 200 := by decide
@[simp] theorem five_lt_200 : (5 : Nat) < 200 := by decide
@[simp] theorem six_lt_200 : (6 : Nat) < 200 := by decide
@[simp] theorem seven_lt_200 : (7 : Nat) < 200 := by decide
@[simp] theorem ninetyNine_lt_200 : (99 : Nat) < 200 := by decide

@[simp] theorem one_ne_zero : (1 : Nat) ≠ 0 := by decide
@[simp] theorem two_ne_zero : (2 : Nat) ≠ 0 := by decide
@[simp] theorem three_ne_zero : (3 : Nat) ≠ 0 := by decide
@[simp] theorem four_ne_zero : (4 : Nat) ≠ 0 := by decide
@[simp] theorem five_ne_zero : (5 : Nat) ≠ 0 := by decide
@[simp] theorem six_ne_zero : (6 : Nat) ≠ 0 := by decide
@[simp] theorem seven_ne_zero : (7 : Nat) ≠ 0 := by decide
@[simp] theorem ninetyNine_ne_zero : (99 : Nat) ≠ 0 := by decide

set_option maxHeartbeats 1000000

theorem langDetParser_step_state_lt (dname : String) (perfNames : List String)
    (s : Nat) (tok : Token) (top : Option Nat) :
    ((langDetParser dname perfNames).step s tok top).1 < 200 := by
  cases s with
  | zero =>
    cases tok <;> cases top with
    | none => simp [langDetParser]
    | some val =>
      cases val with
      | zero => simp [langDetParser]
      | succ val1 =>
        cases val1 with
        | zero => simp [langDetParser]
        | succ val2 =>
          cases val2 with
          | zero => simp [langDetParser]
          | succ val3 =>
            cases val3 with
            | zero => simp [langDetParser]
            | succ val4 => simp [langDetParser]

  | succ s1 =>
    cases s1 with
    | zero =>
      cases tok <;> cases top with
      | none => simp [langDetParser]
      | some val =>
        cases val with
        | zero => simp [langDetParser]
        | succ val1 =>
          cases val1 with
          | zero => simp [langDetParser]
          | succ val2 =>
            cases val2 with
            | zero => simp [langDetParser]
            | succ val3 =>
              cases val3 with
              | zero => simp [langDetParser]
              | succ val4 => simp [langDetParser]

    | succ s2 =>
      cases s2 with
      | zero =>
        cases tok <;> cases top with
        | none => simp [langDetParser]
        | some val =>
          cases val with
          | zero => simp [langDetParser]
          | succ val1 =>
            cases val1 with
            | zero => simp [langDetParser]
            | succ val2 =>
              cases val2 with
              | zero => simp [langDetParser]
              | succ val3 =>
                cases val3 with
                | zero => simp [langDetParser]
                | succ val4 => simp [langDetParser]

      | succ s3 =>
        cases s3 with
        | zero =>
          cases tok <;> cases top with
          | none => simp [langDetParser]
          | some val =>
            cases val with
            | zero => simp [langDetParser]
            | succ val1 =>
              cases val1 with
              | zero => simp [langDetParser]
              | succ val2 =>
                cases val2 with
                | zero => simp [langDetParser]
                | succ val3 =>
                  cases val3 with
                  | zero => simp [langDetParser]
                  | succ val4 => simp [langDetParser]

        | succ s4 =>
          cases s4 with
          | zero =>
            cases tok <;> cases top with
            | none => simp [langDetParser]
            | some val =>
              cases val with
              | zero => simp [langDetParser]
              | succ val1 =>
                cases val1 with
                | zero => simp [langDetParser]
                | succ val2 =>
                  cases val2 with
                  | zero => simp [langDetParser]
                  | succ val3 =>
                    cases val3 with
                    | zero => simp [langDetParser]
                    | succ val4 => simp [langDetParser]

          | succ s5 =>
            cases s5 with
            | zero =>
              cases tok <;> cases top with
              | none => simp [langDetParser]
              | some val =>
                cases val with
                | zero => simp [langDetParser]
                | succ val1 =>
                  cases val1 with
                  | zero => simp [langDetParser]
                  | succ val2 =>
                    cases val2 with
                    | zero => simp [langDetParser]
                    | succ val3 =>
                      cases val3 with
                      | zero => simp [langDetParser]
                      | succ val4 => simp [langDetParser]

            | succ s6 =>
              cases s6 with
              | zero =>
                cases tok <;> cases top with
                | none => simp [langDetParser]
                | some val =>
                  cases val with
                  | zero => simp [langDetParser]
                  | succ val1 =>
                    cases val1 with
                    | zero => simp [langDetParser]
                    | succ val2 =>
                      cases val2 with
                      | zero => simp [langDetParser]
                      | succ val3 =>
                        cases val3 with
                        | zero => simp [langDetParser]
                        | succ val4 => simp [langDetParser]

              | succ s7 =>
                cases tok <;> cases top with
                | none => simp [langDetParser]
                | some val =>
                  cases val with
                  | zero => simp [langDetParser]
                  | succ val1 =>
                    cases val1 with
                    | zero => simp [langDetParser]
                    | succ val2 =>
                      cases val2 with
                      | zero => simp [langDetParser]
                      | succ val3 =>
                        cases val3 with
                        | zero => simp [langDetParser]
                        | succ val4 => simp [langDetParser]


theorem langDetParser_step_state_ne_zero (dname : String) (perfNames : List String)
    (s : Nat) (tok : Token) (top : Option Nat) :
    ((langDetParser dname perfNames).step s tok top).1 ≠ 0 := by
  cases s with
  | zero =>
    cases tok <;> cases top with
    | none => simp [langDetParser]
    | some val =>
      cases val with
      | zero => simp [langDetParser]
      | succ val1 =>
        cases val1 with
        | zero => simp [langDetParser]
        | succ val2 =>
          cases val2 with
          | zero => simp [langDetParser]
          | succ val3 =>
            cases val3 with
            | zero => simp [langDetParser]
            | succ val4 => simp [langDetParser]

  | succ s1 =>
    cases s1 with
    | zero =>
      cases tok <;> cases top with
      | none => simp [langDetParser]
      | some val =>
        cases val with
        | zero => simp [langDetParser]
        | succ val1 =>
          cases val1 with
          | zero => simp [langDetParser]
          | succ val2 =>
            cases val2 with
            | zero => simp [langDetParser]
            | succ val3 =>
              cases val3 with
              | zero => simp [langDetParser]
              | succ val4 => simp [langDetParser]

    | succ s2 =>
      cases s2 with
      | zero =>
        cases tok <;> cases top with
        | none => simp [langDetParser]
        | some val =>
          cases val with
          | zero => simp [langDetParser]
          | succ val1 =>
            cases val1 with
            | zero => simp [langDetParser]
            | succ val2 =>
              cases val2 with
              | zero => simp [langDetParser]
              | succ val3 =>
                cases val3 with
                | zero => simp [langDetParser]
                | succ val4 => simp [langDetParser]

      | succ s3 =>
        cases s3 with
        | zero =>
          cases tok <;> cases top with
          | none => simp [langDetParser]
          | some val =>
            cases val with
            | zero => simp [langDetParser]
            | succ val1 =>
              cases val1 with
              | zero => simp [langDetParser]
              | succ val2 =>
                cases val2 with
                | zero => simp [langDetParser]
                | succ val3 =>
                  cases val3 with
                  | zero => simp [langDetParser]
                  | succ val4 => simp [langDetParser]

        | succ s4 =>
          cases s4 with
          | zero =>
            cases tok <;> cases top with
            | none => simp [langDetParser]
            | some val =>
              cases val with
              | zero => simp [langDetParser]
              | succ val1 =>
                cases val1 with
                | zero => simp [langDetParser]
                | succ val2 =>
                  cases val2 with
                  | zero => simp [langDetParser]
                  | succ val3 =>
                    cases val3 with
                    | zero => simp [langDetParser]
                    | succ val4 => simp [langDetParser]

          | succ s5 =>
            cases s5 with
            | zero =>
              cases tok <;> cases top with
              | none => simp [langDetParser]
              | some val =>
                cases val with
                | zero => simp [langDetParser]
                | succ val1 =>
                  cases val1 with
                  | zero => simp [langDetParser]
                  | succ val2 =>
                    cases val2 with
                    | zero => simp [langDetParser]
                    | succ val3 =>
                      cases val3 with
                      | zero => simp [langDetParser]
                      | succ val4 => simp [langDetParser]

            | succ s6 =>
              cases s6 with
              | zero =>
                cases tok <;> cases top with
                | none => simp [langDetParser]
                | some val =>
                  cases val with
                  | zero => simp [langDetParser]
                  | succ val1 =>
                    cases val1 with
                    | zero => simp [langDetParser]
                    | succ val2 =>
                      cases val2 with
                      | zero => simp [langDetParser]
                      | succ val3 =>
                        cases val3 with
                        | zero => simp [langDetParser]
                        | succ val4 => simp [langDetParser]

              | succ s7 =>
                cases tok <;> cases top with
                | none => simp [langDetParser]
                | some val =>
                  cases val with
                  | zero => simp [langDetParser]
                  | succ val1 =>
                    cases val1 with
                    | zero => simp [langDetParser]
                    | succ val2 =>
                      cases val2 with
                      | zero => simp [langDetParser]
                      | succ val3 =>
                        cases val3 with
                        | zero => simp [langDetParser]
                        | succ val4 => simp [langDetParser]


set_option maxHeartbeats 200000

def langCheckBool (dname : String) (perfNames : List String) (e : SExpr) : Bool :=
  match e with
  | .list [.atom (.symbol "lang"), .atom (.symbol dn), .list (.atom (.symbol perf) :: _)] =>
      dn == dname && perfNames.contains perf
  | _ => false

-- ============================================================
-- Section 12: langDetParser state-99 rejection
-- ============================================================

private theorem lang99_step (dn : String) (pn : List String) (tok : Token) (stack : List Nat) :
    ((langDetParser dn pn).runStep (99, stack) tok).1 = 99 := by
  cases stack with
  | nil => cases tok <;> simp [DetParser.runStep, langDetParser]
  | cons t r => cases tok <;> simp [DetParser.runStep, langDetParser]

private theorem lang99_runStep (dn : String) (pn : List String) (tok : Token) (stack : List Nat) :
    ∃ s', (langDetParser dn pn).runStep (99, stack) tok = (99, s') :=
  ⟨_, Prod.ext (lang99_step dn pn tok stack) rfl⟩

private theorem lang99_foldl_pair (dn : String) (pn : List String) (tokens : List Token)
    (stack : List Nat) :
    ∃ s', List.foldl (langDetParser dn pn).runStep (99, stack) tokens = (99, s') := by
  induction tokens generalizing stack with
  | nil => exact ⟨stack, rfl⟩
  | cons tok rest ih =>
    simp only [List.foldl]
    have hstep : ∃ s', (langDetParser dn pn).runStep (99, stack) tok = (99, s') :=
      ⟨_, Prod.ext (lang99_step dn pn tok stack) rfl⟩
    obtain ⟨s1, hs1⟩ := hstep; rw [hs1]; exact ih s1

private theorem lang_accept_99 (dn : String) (pn : List String) (stack : List Nat) :
    (langDetParser dn pn).accept 99 stack = false := by
  simp [langDetParser]

private theorem lang_run_false_99 (dn : String) (pn : List String) (tokens : List Token)
    (stack : List Nat) :
    (langDetParser dn pn).accept
      (List.foldl (langDetParser dn pn).runStep (99, stack) tokens).1
      (List.foldl (langDetParser dn pn).runStep (99, stack) tokens).2 = false := by
  obtain ⟨s', hs'⟩ := lang99_foldl_pair dn pn tokens stack
  rw [hs']; exact lang_accept_99 dn pn _

private theorem lang_step_false_99 (dn : String) (pn : List String) (tok : Token) (stack : List Nat) :
    (langDetParser dn pn).accept
      ((langDetParser dn pn).runStep (99, stack) tok).1
      ((langDetParser dn pn).runStep (99, stack) tok).2 = false := by
  have h := lang99_step dn pn tok stack
  have heq : (langDetParser dn pn).runStep (99, stack) tok =
    (99, ((langDetParser dn pn).runStep (99, stack) tok).2) := Prod.ext h rfl
  rw [heq]; exact lang_accept_99 dn pn _

-- State 6 rejection: state 6 goes to 99 on any non-(rparen, some 1) token
-- Actually, after processing the third element, if there are extra elements,
-- the first token of the extra element hits state 6. For any SExpr token stream,
-- the first token is either lparen (for list) or a data token (for atom).
-- State 6 only transitions to 7 on (.rparen, some 1), all others → 99.
private theorem lang6_step (dn : String) (pn : List String) (tok : Token) (htok : tok ≠ .rparen)
    (stack : List Nat) :
    ((langDetParser dn pn).runStep (6, stack) tok).1 = 99 := by
  cases stack with
  | nil => cases tok <;> simp_all [DetParser.runStep, langDetParser]
  | cons t r =>
    cases tok with
    | rparen => exact absurd rfl htok
    | lparen => simp [DetParser.runStep, langDetParser]
    | sym s => simp [DetParser.runStep, langDetParser]
    | str s => simp [DetParser.runStep, langDetParser]
    | num n => simp [DetParser.runStep, langDetParser]
    | bool_ b => simp [DetParser.runStep, langDetParser]
    | kw k => simp [DetParser.runStep, langDetParser]

private theorem lang6_foldl_pair (dn : String) (pn : List String) (tok : Token) (htok : tok ≠ .rparen)
    (rest : List Token) (stack : List Nat) :
    ∃ s', List.foldl (langDetParser dn pn).runStep (6, stack) (tok :: rest) = (99, s') := by
  simp only [List.foldl]
  have hstep : ∃ s', (langDetParser dn pn).runStep (6, stack) tok = (99, s') :=
    ⟨_, Prod.ext (lang6_step dn pn tok htok stack) rfl⟩
  obtain ⟨s1, hs1⟩ := hstep; rw [hs1]
  exact lang99_foldl_pair dn pn rest s1

-- ============================================================
-- Section 13: lang process_sexpr (structural induction)
-- ============================================================

def lang_process_aux (dn : String) (pn : List String) :
    (e : SExpr) → ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (langDetParser dn pn).runStep (5, stack) (tokenize e) = (5, stack) :=
  @SExpr.rec
    (fun e => ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (langDetParser dn pn).runStep (5, stack) (tokenize e) = (5, stack))
    (fun xs => ∀ (stack : List Nat), stack ≠ [] →
      List.foldl (langDetParser dn pn).runStep (5, stack)
        ((xs.map tokenize).flatten) = (5, stack))
    (fun a stack hne => by
      obtain ⟨top, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      cases a <;> simp [tokenize, DetParser.runStep, langDetParser])
    (fun xs ih_xs stack hne => by
      obtain ⟨top, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [tokenize]
      rw [List.foldl_append, List.foldl_append]
      have h1 : List.foldl (langDetParser dn pn).runStep (5, top :: rest) [Token.lparen]
          = (5, 3 :: top :: rest) := by simp [DetParser.runStep, langDetParser]
      rw [h1, ih_xs (3 :: top :: rest) (by simp)]
      simp [DetParser.runStep, langDetParser])
    (fun stack _ => by simp)
    (fun x xs ih_x ih_xs stack hne => by
      show List.foldl _ (5, stack) ((tokenize x).append ((xs.map tokenize).flatten)) = (5, stack)
      rw [List.append_eq, List.foldl_append, ih_x stack hne]
      exact ih_xs stack hne)

theorem lang_process_sexpr (dn : String) (pn : List String) (e : SExpr)
    (stack : List Nat) (hne : stack ≠ []) :
    List.foldl (langDetParser dn pn).runStep (5, stack) (tokenize e) = (5, stack) :=
  lang_process_aux dn pn e stack hne

theorem lang_process_sexprs (dn : String) (pn : List String) (es : List SExpr)
    (stack : List Nat) (hne : stack ≠ []) :
    List.foldl (langDetParser dn pn).runStep (5, stack)
               ((es.map tokenize).flatten) = (5, stack) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    show List.foldl _ (5, stack) ((tokenize e).append ((es.map tokenize).flatten)) = (5, stack)
    rw [List.append_eq, List.foldl_append, lang_process_sexpr dn pn e stack hne]; exact ih

-- ============================================================
-- Section 14: langCheck_agrees
-- ============================================================

-- Helper: collapse long foldl chains from state 99
private theorem lang_chain_99 (dn : String) (pn : List String)
    (t1 t2 t3 : List Token) (stack : List Nat) :
    (langDetParser dn pn).accept
      (List.foldl (langDetParser dn pn).runStep
        (List.foldl (langDetParser dn pn).runStep
          (List.foldl (langDetParser dn pn).runStep (99, stack) t1) t2) t3).1
      (List.foldl (langDetParser dn pn).runStep
        (List.foldl (langDetParser dn pn).runStep
          (List.foldl (langDetParser dn pn).runStep (99, stack) t1) t2) t3).2 = false := by
  obtain ⟨s1, hs1⟩ := lang99_foldl_pair dn pn t1 stack; rw [hs1]
  obtain ⟨s2, hs2⟩ := lang99_foldl_pair dn pn t2 s1; rw [hs2]
  exact lang_run_false_99 dn pn t3 s2

-- Tactic for rejecting from state 99 after one step yields 99
private theorem lang_reject_after_step (dn : String) (pn : List String) (config : Nat × List Nat)
    (rest : List Token) (h : config.1 = 99) :
    (langDetParser dn pn).accept
      (List.foldl (langDetParser dn pn).runStep config rest).1
      (List.foldl (langDetParser dn pn).runStep config rest).2 = false := by
  have : config = (99, config.2) := Prod.ext h rfl
  rw [this]; exact lang_run_false_99 dn pn rest config.2

theorem langCheck_agrees (dname : String) (perfNames : List String) (e : SExpr) :
    (langDetParser dname perfNames).run (tokenize e) = langCheckBool dname perfNames e := by
  cases e with
  | atom a =>
    cases a <;> simp [langCheckBool, DetParser.run, tokenize, List.foldl,
                       DetParser.runStep, langDetParser]
  | list xs =>
    unfold DetParser.run
    simp only [tokenize]
    rw [List.foldl_append, List.foldl_append]
    have h_init : List.foldl (langDetParser dname perfNames).runStep
        ((langDetParser dname perfNames).initState, (langDetParser dname perfNames).initStack)
        [Token.lparen] = (1, [1, 0]) := by
      simp [DetParser.runStep, langDetParser]
    rw [h_init]
    cases xs with
    | nil =>
      simp [langCheckBool, DetParser.runStep, langDetParser]
    | cons x1 xs1 =>
      show (langDetParser dname perfNames).accept
          (List.foldl (langDetParser dname perfNames).runStep
            (List.foldl (langDetParser dname perfNames).runStep (1, [1, 0])
              ((tokenize x1).append ((xs1.map tokenize).flatten))) [Token.rparen]).1
          (List.foldl (langDetParser dname perfNames).runStep
            (List.foldl (langDetParser dname perfNames).runStep (1, [1, 0])
              ((tokenize x1).append ((xs1.map tokenize).flatten))) [Token.rparen]).2 =
        langCheckBool dname perfNames (.list (x1 :: xs1))
      rw [List.append_eq, List.foldl_append]
      -- x1 must be .atom (.symbol "lang")
      cases x1 with
      | list ys =>
        simp only [langCheckBool, tokenize]
        rw [List.foldl_append, List.foldl_append]
        have : List.foldl (langDetParser dname perfNames).runStep (1, [1, 0]) [Token.lparen]
            = (99, [0]) := by simp [DetParser.runStep, langDetParser]
        rw [this]
        obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((ys.map tokenize).flatten) [0]; rw [hs1]
        obtain ⟨s2, hs2⟩ := lang99_foldl_pair dname perfNames [Token.rparen] s1; rw [hs2]
        obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs1.map tokenize).flatten) s2; rw [hs3]
        simp [DetParser.runStep, langDetParser]
      | atom a1 =>
        cases a1 with
        | symbol s1 =>
          simp only [tokenize, List.foldl]
          by_cases hs1 : s1 = "lang"
          · subst hs1
            have h_step1 : (langDetParser dname perfNames).runStep (1, [1, 0]) (.sym "lang") = (2, [1, 0]) := by
              simp [DetParser.runStep, langDetParser]
            rw [h_step1]
            -- Now state 2. Next must be .atom (.symbol dname)
            cases xs1 with
            | nil =>
              simp [langCheckBool, DetParser.runStep, langDetParser]
            | cons x2 xs2 =>
              show (langDetParser dname perfNames).accept
                (List.foldl (langDetParser dname perfNames).runStep
                  (List.foldl (langDetParser dname perfNames).runStep (2, [1, 0])
                    ((tokenize x2).append ((xs2.map tokenize).flatten))) [Token.rparen]).1
                (List.foldl (langDetParser dname perfNames).runStep
                  (List.foldl (langDetParser dname perfNames).runStep (2, [1, 0])
                    ((tokenize x2).append ((xs2.map tokenize).flatten))) [Token.rparen]).2 =
                langCheckBool dname perfNames (SExpr.list ([.atom (.symbol "lang"), x2] ++ xs2))
              rw [List.append_eq, List.foldl_append]
              cases x2 with
              | list ys =>
                simp only [langCheckBool, tokenize]
                rw [List.foldl_append, List.foldl_append]
                have : List.foldl (langDetParser dname perfNames).runStep (2, [1, 0]) [Token.lparen]
                    = (99, [0]) := by simp [DetParser.runStep, langDetParser]
                rw [this]
                obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((ys.map tokenize).flatten) [0]; rw [hs1]
                obtain ⟨s2, hs2⟩ := lang99_foldl_pair dname perfNames [Token.rparen] s1; rw [hs2]
                obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs2.map tokenize).flatten) s2; rw [hs3]
                simp [DetParser.runStep, langDetParser]
              | atom a2 =>
                cases a2 with
                | symbol t =>
                  simp only [tokenize, List.foldl]
                  by_cases ht : t = dname
                  · -- t = dname
                    have h_step2 : (langDetParser dname perfNames).runStep (2, [1, 0]) (.sym t) = (3, [1, 0]) := by
                      simp [DetParser.runStep, langDetParser, ht]
                    rw [h_step2]
                    -- Now state 3. Third must be .list (.atom (.symbol perf) :: args)
                    cases xs2 with
                    | nil =>
                      simp [langCheckBool, DetParser.runStep, langDetParser]
                    | cons x3 xs3 =>
                      rw [ht]  -- replace t with dname in the goal
                      show (langDetParser dname perfNames).accept
                        (List.foldl (langDetParser dname perfNames).runStep
                          (List.foldl (langDetParser dname perfNames).runStep (3, [1, 0])
                            ((tokenize x3).append ((xs3.map tokenize).flatten))) [Token.rparen]).1
                        (List.foldl (langDetParser dname perfNames).runStep
                          (List.foldl (langDetParser dname perfNames).runStep (3, [1, 0])
                            ((tokenize x3).append ((xs3.map tokenize).flatten))) [Token.rparen]).2 =
                        langCheckBool dname perfNames (.list (.atom (.symbol "lang") :: .atom (.symbol dname) :: x3 :: xs3))
                      rw [List.append_eq, List.foldl_append]
                      cases x3 with
                      | atom c =>
                        -- Not a list → reject
                        simp only [langCheckBool]
                        cases c with
                        | symbol u =>
                          simp only [tokenize, List.foldl]
                          have : (langDetParser dname perfNames).runStep (3, [1, 0]) (.sym u) = (99, [0]) := by
                            simp [DetParser.runStep, langDetParser]
                          rw [this]
                          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) [0]; rw [hs1]
                          simp [DetParser.runStep, langDetParser]
                        | str u =>
                          simp only [tokenize, List.foldl]
                          have : (langDetParser dname perfNames).runStep (3, [1, 0]) (.str u) = (99, [0]) := by
                            simp [DetParser.runStep, langDetParser]
                          rw [this]
                          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) [0]; rw [hs1]
                          simp [DetParser.runStep, langDetParser]
                        | num n =>
                          simp only [tokenize, List.foldl]
                          have : (langDetParser dname perfNames).runStep (3, [1, 0]) (.num n) = (99, [0]) := by
                            simp [DetParser.runStep, langDetParser]
                          rw [this]
                          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) [0]; rw [hs1]
                          simp [DetParser.runStep, langDetParser]
                        | bool b =>
                          simp only [tokenize, List.foldl]
                          have : (langDetParser dname perfNames).runStep (3, [1, 0]) (.bool_ b) = (99, [0]) := by
                            simp [DetParser.runStep, langDetParser]
                          rw [this]
                          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) [0]; rw [hs1]
                          simp [DetParser.runStep, langDetParser]
                        | keyword k =>
                          simp only [tokenize, List.foldl]
                          have : (langDetParser dname perfNames).runStep (3, [1, 0]) (.kw k) = (99, [0]) := by
                            simp [DetParser.runStep, langDetParser]
                          rw [this]
                          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) [0]; rw [hs1]
                          simp [DetParser.runStep, langDetParser]
                      | list ws =>
                        -- Third element is a list: tokenize = [lparen] ++ inner ++ [rparen]
                        simp only [tokenize]
                        rw [List.foldl_append, List.foldl_append]
                        -- state 3 + lparen with some 1 → (4, [2, 1])
                        have h_lp3 : List.foldl (langDetParser dname perfNames).runStep (3, [1, 0]) [Token.lparen]
                            = (4, [2, 1, 0]) := by
                          simp [DetParser.runStep, langDetParser]
                        rw [h_lp3]
                        cases ws with
                        | nil =>
                          -- Empty inner list → rparen takes us from state 4 to 99
                          -- Compute the step after empty inner + rparen
                          have h_nil_rp : (langDetParser dname perfNames).runStep (4, [2, 1, 0]) Token.rparen = (99, [1, 0]) := by
                            simp [DetParser.runStep, langDetParser]
                          simp only [List.flatten, List.map, List.foldl, langCheckBool]
                          rw [h_nil_rp]
                          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) [1, 0]
                          rw [hs1]
                          simp [DetParser.runStep, langDetParser]
                        | cons w ws' =>
                          -- Process first inner element: split (w :: ws').map(tokenize).flatten
                          -- into tokenize(w) ++ ws'.map(tokenize).flatten
                          rw [show ((w :: ws').map tokenize).flatten = (tokenize w).append ((ws'.map tokenize).flatten) from rfl]
                          rw [List.append_eq, List.foldl_append]
                          cases w with
                          | list vs =>
                            -- Inner head is list → state 4 + lparen → 99
                            simp only [langCheckBool, tokenize]
                            rw [List.foldl_append, List.foldl_append]
                            have : List.foldl (langDetParser dname perfNames).runStep (4, [2, 1, 0]) [Token.lparen]
                                = (99, [1, 0]) := by
                              simp [DetParser.runStep, langDetParser]
                            rw [this]
                            obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((vs.map tokenize).flatten) [1, 0]; rw [hs1]
                            obtain ⟨s2, hs2⟩ := lang99_foldl_pair dname perfNames [Token.rparen] s1; rw [hs2]
                            obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((ws'.map tokenize).flatten) s2; rw [hs3]
                            obtain ⟨s4, hs4⟩ := lang99_foldl_pair dname perfNames [Token.rparen] s3; rw [hs4]
                            obtain ⟨s5, hs5⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) s4; rw [hs5]
                            simp [DetParser.runStep, langDetParser]
                          | atom d =>
                            cases d with
                            | symbol perf =>
                              simp only [tokenize, List.foldl]
                              by_cases hp : perfNames.contains perf = true
                              · have hpm := contains_to_mem hp
                                have h_step4 : (langDetParser dname perfNames).runStep (4, [2, 1, 0]) (.sym perf) = (5, [2, 1, 0]) := by
                                  simp [DetParser.runStep, langDetParser, hpm]
                                rw [h_step4, lang_process_sexprs dname perfNames ws' [2, 1, 0] (by simp)]
                                -- After inner rparen: state 5 + rparen with some 2 → (6, [1, 0])
                                simp only [DetParser.runStep, langDetParser, List.head?, List.drop]
                                -- Now state 6, stack [1, 0]
                                -- Process xs3 then outer rparen
                                cases xs3 with
                                | nil =>
                                  -- Outer rparen: state 6 + rparen with some 1 → (7, [0])
                                  simp [langCheckBool, hpm]
                                | cons x4 xs4 =>
                                  -- Extra elements → reject
                                  simp only [langCheckBool]
                                  -- First token of tokenize x4 hits state 6
                                  -- Any token except rparen-with-some-1 → 99
                                  -- tokenize x4 starts with either lparen (if list) or a data token (if atom)
                                  -- Neither is rparen, so state 6 → 99
                                  show (langDetParser dname perfNames).accept
                                    (List.foldl (langDetParser dname perfNames).runStep
                                      (List.foldl (langDetParser dname perfNames).runStep (6, [1, 0])
                                        ((tokenize x4).append ((xs4.map tokenize).flatten))) [Token.rparen]).1
                                    (List.foldl (langDetParser dname perfNames).runStep
                                      (List.foldl (langDetParser dname perfNames).runStep (6, [1, 0])
                                        ((tokenize x4).append ((xs4.map tokenize).flatten))) [Token.rparen]).2 = false
                                  rw [List.append_eq, List.foldl_append]
                                  -- tokenize x4 is non-empty and starts with non-rparen
                                  cases x4 with
                                  | atom a4 =>
                                    cases a4 with
                                    | symbol u =>
                                      simp only [tokenize, List.foldl]
                                      have : (langDetParser dname perfNames).runStep (6, [1, 0]) (.sym u) = (99, [0]) := by
                                        simp [DetParser.runStep, langDetParser]
                                      rw [this]
                                      obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs4.map tokenize).flatten) [0]; rw [hs1]
                                      simp [DetParser.runStep, langDetParser]
                                    | str u =>
                                      simp only [tokenize, List.foldl]
                                      have : (langDetParser dname perfNames).runStep (6, [1, 0]) (.str u) = (99, [0]) := by
                                        simp [DetParser.runStep, langDetParser]
                                      rw [this]
                                      obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs4.map tokenize).flatten) [0]; rw [hs1]
                                      simp [DetParser.runStep, langDetParser]
                                    | num n =>
                                      simp only [tokenize, List.foldl]
                                      have : (langDetParser dname perfNames).runStep (6, [1, 0]) (.num n) = (99, [0]) := by
                                        simp [DetParser.runStep, langDetParser]
                                      rw [this]
                                      obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs4.map tokenize).flatten) [0]; rw [hs1]
                                      simp [DetParser.runStep, langDetParser]
                                    | bool b =>
                                      simp only [tokenize, List.foldl]
                                      have : (langDetParser dname perfNames).runStep (6, [1, 0]) (.bool_ b) = (99, [0]) := by
                                        simp [DetParser.runStep, langDetParser]
                                      rw [this]
                                      obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs4.map tokenize).flatten) [0]; rw [hs1]
                                      simp [DetParser.runStep, langDetParser]
                                    | keyword k =>
                                      simp only [tokenize, List.foldl]
                                      have : (langDetParser dname perfNames).runStep (6, [1, 0]) (.kw k) = (99, [0]) := by
                                        simp [DetParser.runStep, langDetParser]
                                      rw [this]
                                      obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs4.map tokenize).flatten) [0]; rw [hs1]
                                      simp [DetParser.runStep, langDetParser]
                                  | list zs =>
                                    simp only [tokenize]
                                    rw [List.foldl_append, List.foldl_append]
                                    have : List.foldl (langDetParser dname perfNames).runStep (6, [1, 0]) [Token.lparen]
                                        = (99, [0]) := by
                                      simp [DetParser.runStep, langDetParser]
                                    rw [this]
                                    obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((zs.map tokenize).flatten) [0]; rw [hs1]
                                    obtain ⟨s2, hs2⟩ := lang99_foldl_pair dname perfNames [Token.rparen] s1; rw [hs2]
                                    obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs4.map tokenize).flatten) s2; rw [hs3]
                                    simp [DetParser.runStep, langDetParser]
                              · simp only [Bool.not_eq_true] at hp
                                have hnpm := not_contains_to_not_mem hp
                                have h_step4 : (langDetParser dname perfNames).runStep (4, [2, 1, 0]) (.sym perf) = (99, [1, 0]) := by
                                  simp [DetParser.runStep, langDetParser, hnpm]
                                rw [h_step4]
                                rw [show langCheckBool dname perfNames (.list (.atom (.symbol "lang") :: .atom (.symbol dname) :: .list (.atom (.symbol perf) :: ws') :: xs3)) = false from by
                                  cases xs3 with | nil => simp [langCheckBool, hnpm] | cons _ _ => simp [langCheckBool]]
                                obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((ws'.map tokenize).flatten) [1, 0]; rw [hs1]
                                obtain ⟨s2, hs2⟩ := lang99_runStep dname perfNames Token.rparen s1; rw [hs2]
                                obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) s2; rw [hs3]
                                exact lang_step_false_99 dname perfNames Token.rparen s3
                            | str u =>
                              simp only [langCheckBool, tokenize, List.foldl]
                              have : (langDetParser dname perfNames).runStep (4, [2, 1, 0]) (.str u) = (99, [1, 0]) := by
                                simp [DetParser.runStep, langDetParser]
                              rw [this]
                              obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((ws'.map tokenize).flatten) [1, 0]; rw [hs1]
                              obtain ⟨s2, hs2⟩ := lang99_runStep dname perfNames Token.rparen s1; rw [hs2]
                              obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) s2; rw [hs3]
                              exact lang_step_false_99 dname perfNames Token.rparen s3
                            | num n =>
                              simp only [langCheckBool, tokenize, List.foldl]
                              have : (langDetParser dname perfNames).runStep (4, [2, 1, 0]) (.num n) = (99, [1, 0]) := by
                                simp [DetParser.runStep, langDetParser]
                              rw [this]
                              obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((ws'.map tokenize).flatten) [1, 0]; rw [hs1]
                              obtain ⟨s2, hs2⟩ := lang99_runStep dname perfNames Token.rparen s1; rw [hs2]
                              obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) s2; rw [hs3]
                              exact lang_step_false_99 dname perfNames Token.rparen s3
                            | bool b =>
                              simp only [langCheckBool, tokenize, List.foldl]
                              have : (langDetParser dname perfNames).runStep (4, [2, 1, 0]) (.bool_ b) = (99, [1, 0]) := by
                                simp [DetParser.runStep, langDetParser]
                              rw [this]
                              obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((ws'.map tokenize).flatten) [1, 0]; rw [hs1]
                              obtain ⟨s2, hs2⟩ := lang99_runStep dname perfNames Token.rparen s1; rw [hs2]
                              obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) s2; rw [hs3]
                              exact lang_step_false_99 dname perfNames Token.rparen s3
                            | keyword k =>
                              simp only [langCheckBool, tokenize, List.foldl]
                              have : (langDetParser dname perfNames).runStep (4, [2, 1, 0]) (.kw k) = (99, [1, 0]) := by
                                simp [DetParser.runStep, langDetParser]
                              rw [this]
                              obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((ws'.map tokenize).flatten) [1, 0]; rw [hs1]
                              obtain ⟨s2, hs2⟩ := lang99_runStep dname perfNames Token.rparen s1; rw [hs2]
                              obtain ⟨s3, hs3⟩ := lang99_foldl_pair dname perfNames ((xs3.map tokenize).flatten) s2; rw [hs3]
                              exact lang_step_false_99 dname perfNames Token.rparen s3
                  · -- t ≠ dname
                    have h_step2 : (langDetParser dname perfNames).runStep (2, [1, 0]) (.sym t) = (99, [0]) := by
                      simp [DetParser.runStep, langDetParser, ht]
                    rw [h_step2]
                    have hlcb : langCheckBool dname perfNames (SExpr.list ([.atom (.symbol "lang"), .atom (.symbol t)] ++ xs2)) = false := by
                      cases xs2 with
                      | nil => simp [langCheckBool]
                      | cons hd tl => cases tl with
                        | cons _ _ => simp [langCheckBool]
                        | nil => cases hd with
                          | atom _ => simp [langCheckBool]
                          | list ws => cases ws with
                            | nil => simp [langCheckBool]
                            | cons w _ => cases w with
                              | atom a => cases a with
                                | symbol _ =>
                                  have hne : (t == dname) = false := by
                                    simpa [beq_iff_eq] using ht
                                  simp [langCheckBool, hne]
                                | _ => simp [langCheckBool]
                              | list _ => simp [langCheckBool]
                    rw [hlcb]
                    obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs2.map tokenize).flatten) [0]; rw [hs1]
                    simp [DetParser.runStep, langDetParser]
                | str u =>
                  simp only [langCheckBool, tokenize, List.foldl]
                  have : (langDetParser dname perfNames).runStep (2, [1, 0]) (.str u) = (99, [0]) := by
                    simp [DetParser.runStep, langDetParser]
                  rw [this]
                  obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs2.map tokenize).flatten) [0]; rw [hs1]
                  simp [DetParser.runStep, langDetParser]
                | num n =>
                  simp only [langCheckBool, tokenize, List.foldl]
                  have : (langDetParser dname perfNames).runStep (2, [1, 0]) (.num n) = (99, [0]) := by
                    simp [DetParser.runStep, langDetParser]
                  rw [this]
                  obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs2.map tokenize).flatten) [0]; rw [hs1]
                  simp [DetParser.runStep, langDetParser]
                | bool b =>
                  simp only [langCheckBool, tokenize, List.foldl]
                  have : (langDetParser dname perfNames).runStep (2, [1, 0]) (.bool_ b) = (99, [0]) := by
                    simp [DetParser.runStep, langDetParser]
                  rw [this]
                  obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs2.map tokenize).flatten) [0]; rw [hs1]
                  simp [DetParser.runStep, langDetParser]
                | keyword k =>
                  simp only [langCheckBool, tokenize, List.foldl]
                  have : (langDetParser dname perfNames).runStep (2, [1, 0]) (.kw k) = (99, [0]) := by
                    simp [DetParser.runStep, langDetParser]
                  rw [this]
                  obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs2.map tokenize).flatten) [0]; rw [hs1]
                  simp [DetParser.runStep, langDetParser]
          · -- s1 ≠ "lang"
            have h_step1 : (langDetParser dname perfNames).runStep (1, [1, 0]) (.sym s1) = (99, [0]) := by
              simp [DetParser.runStep, langDetParser, hs1]
            rw [h_step1, show langCheckBool dname perfNames (.list (.atom (.symbol s1) :: xs1)) = false from by
              simp [langCheckBool, hs1]]
            obtain ⟨s1', hs1'⟩ := lang99_foldl_pair dname perfNames ((xs1.map tokenize).flatten) [0]; rw [hs1']
            simp [DetParser.runStep, langDetParser]
        -- Non-symbol atom tokens in position 1
        | str s =>
          simp only [langCheckBool, tokenize, List.foldl]
          have : (langDetParser dname perfNames).runStep (1, [1, 0]) (.str s) = (99, [0]) := by
            simp [DetParser.runStep, langDetParser]
          rw [this]
          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs1.map tokenize).flatten) [0]; rw [hs1]
          simp [DetParser.runStep, langDetParser]
        | num n =>
          simp only [langCheckBool, tokenize, List.foldl]
          have : (langDetParser dname perfNames).runStep (1, [1, 0]) (.num n) = (99, [0]) := by
            simp [DetParser.runStep, langDetParser]
          rw [this]
          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs1.map tokenize).flatten) [0]; rw [hs1]
          simp [DetParser.runStep, langDetParser]
        | bool b =>
          simp only [langCheckBool, tokenize, List.foldl]
          have : (langDetParser dname perfNames).runStep (1, [1, 0]) (.bool_ b) = (99, [0]) := by
            simp [DetParser.runStep, langDetParser]
          rw [this]
          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs1.map tokenize).flatten) [0]; rw [hs1]
          simp [DetParser.runStep, langDetParser]
        | keyword k =>
          simp only [langCheckBool, tokenize, List.foldl]
          have : (langDetParser dname perfNames).runStep (1, [1, 0]) (.kw k) = (99, [0]) := by
            simp [DetParser.runStep, langDetParser]
          rw [this]
          obtain ⟨s1, hs1⟩ := lang99_foldl_pair dname perfNames ((xs1.map tokenize).flatten) [0]; rw [hs1]
          simp [DetParser.runStep, langDetParser]

end CBCL
