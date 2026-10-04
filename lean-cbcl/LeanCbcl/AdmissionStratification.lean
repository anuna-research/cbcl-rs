import LeanCbcl.State
import LeanCbcl.R6DCFLPreservation

/-!
# Admission never reads state (SPEC-019 REQ-1914, ADR-1909)

`State.lean` models the fold and the binder; `R6DCFLPreservation.lean` proves
the store trace language of a role-annotated protocol regular. This file
connects them: it says what admission may read, proves that an admission of
that form gives verdicts no state rule can influence and keeps the store
language regular (hence trace-DCFL), and shows that both properties fail
for admissions that read a rule's value.

## The interface (§1)

An `Admission` is a **shape stage** `Act → Bool`, which sees one act, and a
**causal stage** `List Skeleton → Act → Verdict`, which sees the accepted
set only through each act's `Skeleton`: its address, verb, signer, and
predecessors. A skeleton has no keyword fields and no `:replaces`, and those
are all any state rule reads (`State.Act.get`, `keyOf`, `replacers`). So the
interface is stratification as a type: `admit_ignores_data` rewrites every
accepted act's data arbitrarily and the verdict does not move, while
`fold_reads_data` shows a rule that does.

## Regularity (§2–§3)

Stratification alone is not enough for regularity: a causal stage could
still count verbs in the skeletons. What keeps the language regular is that
the deployed causal stage reads the accepted set only through *membership*
of names, as `R6DCFLPreservation.enabled` does. `r7Admission` is that
admission: the R7 receipt as its shape stage (closed field sets and string
bounds, SPEC-019 R.4) and `enabled` over the accepted verbs as its causal
stage, `pending` when not yet enabled (valid-sticky, ADR-602).

* `storeAccepts_iff`: a store is accepted by `r7Admission` iff it is in
  `LocalStoreTrace`: every act passes the shape stage, and the verbs are in
  R6's `StoreTrace`.
* `localStoreTrace_regular`: for **any** message-local shape stage, that
  language is regular, by a product of the shape flag with R6's store
  automaton. Hence `r7Store_regular` and `r7Store_isTraceDCFL`.
* `r7Admission_sticky`: an accepted verdict stays accepted as the store
  grows.

## Necessity (§4–§5)

* `countGated_not_regular`: an admission that accepts `b` only while
  `State.count "b" ≤ State.count "a"` (one counter rule fed back into
  acceptance) has a store language no `FinDFA` recognises. Pigeonhole on the
  automaton's finite carrier, no pumping lemma needed. (This language is
  still one-counter, so context-free; two counters fed back give the
  non-context-free `#a = #b = #c`, which is not mechanised here.)
* `domain_feedback_not_sticky`: the pre-ADR-1909 admission, which enforced
  an opener-drawn domain by reading `last propose :options`, accepts a vote
  and then rejects it once a concurrent opener with a greater address
  arrives. Feedback breaks valid-stickiness before it breaks regularity.

## Correspondence (disclosed)

`r7Admission`'s causal stage is R6's name-level abstraction: the citation
shape is existentially quantified below the alphabet, exactly as in
`StoreTrace`. The receipt models the closed field set and the string bound;
list and number bounds and the `:replaces` address check are further
message-local conjuncts, covered by `localStoreTrace_regular` for any shape
stage. That the Rust `state_exports::admit` has this form is checked by
TEST-1914 (`crates/cbcl-parser/tests/admission_state_free.rs`), not proved.

Axioms: at most `propext, Classical.choice, Quot.sound` (`AxiomAudit.lean`).
-/

namespace CBCL
namespace AdmissionStratification

open State
open R6DCFLPreservation

/-! ## §1 The interface: one act, and the accepted set's skeletons -/

/-- What the causal stage may see of an accepted act: its causal structure,
never its data. -/
structure Skeleton where
  /-- Content address. -/
  addr : Nat
  /-- The performative. -/
  verb : String
  /-- The authenticated signer. -/
  signer : String
  /-- The `:caused-by` addresses. -/
  preds : List Nat
  deriving DecidableEq

/-- The skeleton of an act. -/
def skel (a : Act) : Skeleton := ⟨a.addr, a.verb, a.signer, a.preds⟩

/-- An admission verdict (SPEC-019 R.7 `admit`). -/
inductive Verdict where
  | accepted
  | pending
  | rejected
  deriving DecidableEq, Repr

/-- An admission of the stratified form: a shape stage over one act and a
causal stage over the accepted skeletons. -/
structure Admission where
  /-- The shape stage: R5 shape and R7 receipt, the message alone. -/
  shape : Act → Bool
  /-- The causal stage: the act against the accepted set's skeletons. -/
  causal : List Skeleton → Act → Verdict

/-- Admit one act against an accepted set. -/
def Admission.admit (adm : Admission) (A : List Act) (a : Act) : Verdict :=
  if adm.shape a then adm.causal (A.map skel) a else .rejected

/-- Accepted sets with the same skeletons get the same verdicts. -/
theorem admit_skeleton_invariant (adm : Admission) {A B : List Act}
    (h : A.map skel = B.map skel) (a : Act) : adm.admit A a = adm.admit B a := by
  simp only [Admission.admit, h]

/-- Replace an act's data: its keyword fields and its `:replaces`. -/
def withData (f : Act → List (String × Val)) (g : Act → List Nat) (a : Act) : Act :=
  { a with fields := f a, replaces := g a }

/-- Rewriting data leaves every skeleton as it was. -/
theorem map_skel_withData (f : Act → List (String × Val)) (g : Act → List Nat)
    (A : List Act) : (A.map (withData f g)).map skel = A.map skel := by
  induction A with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, ih]; rfl

/-- **Stratification** (REQ-1914): rewriting every accepted act's data, all
that any state rule reads, moves no verdict. -/
theorem admit_ignores_data (adm : Admission) (f : Act → List (String × Val))
    (g : Act → List Nat) (A : List Act) (a : Act) :
    adm.admit (A.map (withData f g)) a = adm.admit A a :=
  admit_skeleton_invariant adm (map_skel_withData f g A) a

/-- The same rewrite does move the fold: here, `last open :title`. -/
theorem fold_reads_data :
    ∃ (f : Act → List (String × Val)) (A : List Act),
      last "open" "title" (A.map (withData f (·.replaces))) ≠ last "open" "title" A :=
  ⟨fun _ => [("title", .str "b")],
   [⟨0, "open", "@o", [], [("title", .str "a")], []⟩], by decide⟩

/-! ## §2 The R7 admission and its store language -/

/-- The static footprint the R7 receipt reads (SPEC-019 R.4). -/
structure Footprint where
  /-- Verbs any rule or domain names: their field sets are closed. -/
  stateVerbs : List String
  /-- The declared keyword fields of a verb. -/
  declared : String → List String
  /-- `max-string`. -/
  maxString : Nat

/-- A field value within the string bound. -/
def withinBound (n : Nat) : Val → Bool
  | .str s => decide (s.length ≤ n)
  | _ => true

/-- The R7 receipt: a state-bearing verb carries only declared fields, each
within bounds. It reads the act and the footprint, nothing else. -/
def receipt (fp : Footprint) (a : Act) : Bool :=
  !(fp.stateVerbs.contains a.verb) ||
    a.fields.all (fun kv => (fp.declared a.verb).contains kv.1 && withinBound fp.maxString kv.2)

/-- The causal stage at R6's name level: enabled by the accepted verbs, else
pending (out-of-order arrival is `Unknown`, then `Valid`; ADR-602). -/
def causalStage (P : RoleProtocol) (S : List Skeleton) (a : Act) : Verdict :=
  if enabled P (fun x => (S.map Skeleton.verb).contains x) a.verb then .accepted else .pending

/-- The admission of SPEC-019 R.7 over any message-local shape stage. -/
def r7Admission (ok : Act → Bool) (P : RoleProtocol) : Admission := ⟨ok, causalStage P⟩

/-- The store language: every act passes the shape stage, and the verbs form
an R6 store trace. -/
def LocalStoreTrace (ok : Act → Bool) (P : RoleProtocol) (w : List Act) : Prop :=
  (∀ a ∈ w, ok a = true) ∧ StoreTrace P (w.map Act.verb)

/-- The skeletons' verbs are the acts' verbs. -/
theorem map_verb_skel (w : List Act) : (w.map skel).map Skeleton.verb = w.map Act.verb := by
  induction w with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, ih]; rfl

/-- A store is accepted, every act `accepted` against the completed store,
iff it is in `LocalStoreTrace`. -/
theorem storeAccepts_iff (ok : Act → Bool) (P : RoleProtocol) (w : List Act) :
    (∀ a ∈ w, (r7Admission ok P).admit w a = .accepted) ↔ LocalStoreTrace ok P w := by
  simp only [Admission.admit, r7Admission, causalStage, map_verb_skel]
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun t ht => ?_⟩
    · have := h a ha
      cases hok : ok a <;> simp_all
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      have := h a ha
      cases hok : ok a <;> cases hen : enabled P (fun x => (w.map Act.verb).contains x) a.verb <;>
        simp_all
  · rintro ⟨hok, hst⟩ a ha
    have hen := hst a.verb (List.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [if_pos (hok a ha), if_pos hen]

/-! ## §3 Regularity: a message-local stage keeps the store language regular -/

/-- The product step: the shape flag, and R6's canonical store state. -/
def localStep (ok : Act → Bool) (P : RoleProtocol) (s : Bool × List String) (a : Act) :
    Bool × List String :=
  (s.1 && ok a, storeStep P s.2 a.verb)

/-- The product automaton over acts. Its carrier is the shape flag times
R6's finite carrier. -/
def localDFA (ok : Act → Bool) (P : RoleProtocol) : FinDFA Act (Bool × List String) where
  step := localStep ok P
  start := (true, [])
  accept := fun s => s.1 && (storeDFA P).accept s.2
  states := [true, false].flatMap (fun b => (storeDFA P).states.map (fun c => (b, c)))
  start_mem := List.mem_flatMap.mpr
    ⟨true, by simp, List.mem_map.mpr ⟨[], (storeDFA P).start_mem, rfl⟩⟩
  closed := by
    intro s hs a
    obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp hs
    obtain ⟨c, hcs, rfl⟩ := List.mem_map.mp hb
    refine List.mem_flatMap.mpr ⟨b && ok a, ?_, List.mem_map.mpr ⟨_, (storeDFA P).closed c hcs a.verb, rfl⟩⟩
    cases b <;> cases ok a <;> simp

/-- The product run is the conjunction of the shape stage over the word with
R6's store run over its verbs. -/
theorem localDFA_foldl (ok : Act → Bool) (P : RoleProtocol) :
    ∀ (w : List Act) (b : Bool) (c : List String),
      w.foldl (localStep ok P) (b, c) = (b && w.all ok, (w.map Act.verb).foldl (storeStep P) c) := by
  intro w
  induction w with
  | nil => intro b c; simp
  | cons a rest ih =>
    intro b c
    simp only [List.foldl_cons, localStep, ih, List.all_cons, List.map_cons, Bool.and_assoc]

/-- The product automaton recognises exactly `LocalStoreTrace`. -/
theorem localStoreTrace_iff_run (ok : Act → Bool) (P : RoleProtocol) (w : List Act) :
    LocalStoreTrace ok P w ↔ (localDFA ok P).run w = true := by
  have hrun : (localDFA ok P).run w = (w.all ok && (storeDFA P).run (w.map Act.verb)) := by
    show (localDFA ok P).accept (w.foldl (localStep ok P) (true, [])) = _
    rw [localDFA_foldl]
    simp [localDFA, FinDFA.run, storeDFA]
  rw [hrun, Bool.and_eq_true, ← storeTrace_iff_run, List.all_eq_true]
  rfl

/-- **A message-local stage keeps the store language regular**, for any
shape stage: R6's `storeTrace_regular` extended to the R7 receipt. -/
def localStoreTrace_regular (ok : Act → Bool) (P : RoleProtocol) :
    IsRegular Act (Bool × List String) (LocalStoreTrace ok P) where
  M := localDFA ok P
  sound := fun w h => (localStoreTrace_iff_run ok P w).mpr h
  complete := fun w h => (localStoreTrace_iff_run ok P w).mp h

/-- **The R7 store language is regular**: the stores `r7Admission` accepts. -/
def r7Store_regular (fp : Footprint) (P : RoleProtocol) :
    IsRegular Act (Bool × List String)
      (fun w => ∀ a ∈ w, (r7Admission (receipt fp) P).admit w a = .accepted) where
  M := localDFA (receipt fp) P
  sound := fun w h => (storeAccepts_iff _ P w).mpr ((localStoreTrace_iff_run _ P w).mpr h)
  complete := fun w h => (localStoreTrace_iff_run _ P w).mp ((storeAccepts_iff _ P w).mp h)

/-- Hence trace-DCFL (`IsRegular.toTraceDCFL`). -/
def r7Store_isTraceDCFL (fp : Footprint) (P : RoleProtocol) :
    IsTraceDCFL Act (Bool × List String) Unit
      (fun w => ∀ a ∈ w, (r7Admission (receipt fp) P).admit w a = .accepted) :=
  (r7Store_regular fp P).toTraceDCFL

/-- **Valid-sticky**: an accepted verdict survives store growth. -/
theorem r7Admission_sticky (ok : Act → Bool) (P : RoleProtocol) {A B : List Act}
    (hsub : ∀ x ∈ A, x ∈ B) {a : Act} (h : (r7Admission ok P).admit A a = .accepted) :
    (r7Admission ok P).admit B a = .accepted := by
  simp only [Admission.admit, r7Admission, causalStage, map_verb_skel] at h ⊢
  cases hok : ok a with
  | false => rw [hok] at h; simp at h
  | true =>
    cases hen : enabled P (fun x => (A.map Act.verb).contains x) a.verb with
    | false => rw [hok, hen] at h; simp at h
    | true =>
      have hB : enabled P (fun x => (B.map Act.verb).contains x) a.verb = true := by
        refine enabled_mono (fun x hx => ?_) hen
        rw [List.contains_iff_mem] at hx ⊢
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact List.mem_map.mpr ⟨y, hsub y hy, rfl⟩
      rw [if_pos rfl, if_pos hB]

/-! ## §4 Necessity: a counter fed back into acceptance is not regular -/

/-- Pigeonhole on a finite carrier: `n` values in a list shorter than `n`
repeat. -/
theorem pigeonhole {σ : Type} (f : Nat → σ) :
    ∀ (n : Nat) (S : List σ), (∀ i < n, f i ∈ S) → S.length < n →
      ∃ i j, i < j ∧ j < n ∧ f i = f j := by
  classical
  intro n
  induction n with
  | zero => intro S _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro S hmem hlen
    by_cases hrep : ∃ i, i < n ∧ f i = f n
    · obtain ⟨i, hi, he⟩ := hrep
      exact ⟨i, n, hi, Nat.lt_succ_self n, he⟩
    · have hne : ∀ i < n, f i ≠ f n := fun i hi he => hrep ⟨i, hi, he⟩
      have hfn : f n ∈ S := hmem n (Nat.lt_succ_self n)
      have hlen' : (S.erase (f n)).length < n := by
        rw [List.length_erase_of_mem hfn]
        have : 0 < S.length := List.length_pos_of_mem hfn
        omega
      obtain ⟨i, j, hij, hj, he⟩ := ih (S.erase (f n))
        (fun i hi => (List.mem_erase_of_ne (hne i hi)).mpr (hmem i (Nat.lt_succ_of_lt hi))) hlen'
      exact ⟨i, j, hij, Nat.lt_succ_of_lt hj, he⟩

/-- The `k`-th `a` act. Even addresses: with `actB`, a word of them is a
store (`NodupAddr`). -/
def actA (k : Nat) : Act := ⟨2 * k, "a", "@x", [], [], []⟩
/-- The `k`-th `b` act, at an odd address. -/
def actB (k : Nat) : Act := ⟨2 * k + 1, "b", "@x", [], [], []⟩

/-- The store language of an admission that accepts `b` only while the
`count b` rule is at most the `count a` rule. -/
def CountGated (w : List Act) : Prop := count "b" w ≤ count "a" w

/-- Filtering by a constant `true` keeps everything. -/
theorem filter_const_true (l : List Nat) : (l.filter fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons x rest ih => simp [ih]

/-- Filtering by a constant `false` keeps nothing. -/
theorem filter_const_false (l : List Nat) : (l.filter fun _ => false) = [] := by
  induction l with
  | nil => rfl
  | cons x rest ih => simp [ih]

/-- The `count` rule over `i` `a` acts then `j` `b` acts. -/
theorem count_as_bs (v : String) (i j : Nat) :
    count v ((List.range i).map actA ++ (List.range j).map actB) =
      (if v = "a" then i else 0) + (if v = "b" then j else 0) := by
  simp only [count, size, acts, List.filter_append, List.length_append, List.filter_map]
  by_cases ha : v = "a"
  · subst ha
    simp [Function.comp_def, actA, actB, filter_const_true, filter_const_false]
  · by_cases hb : v = "b"
    · subst hb
      simp [Function.comp_def, actA, actB, filter_const_true, filter_const_false]
    · have h1 : ("a" == v) = false := by simp; exact fun h => ha h.symm
      have h2 : ("b" == v) = false := by simp; exact fun h => hb h.symm
      simp [Function.comp_def, actA, actB, h1, h2, ha, hb]

/-- **One counter fed back into acceptance leaves the regular class.** -/
theorem countGated_not_regular {σ : Type} (R : IsRegular Act σ CountGated) : False := by
  let f : Nat → σ := fun i => ((List.range i).map actA).foldl R.M.step R.M.start
  obtain ⟨i, j, hij, -, heq⟩ :=
    pigeonhole f (R.M.states.length + 1) R.M.states
      (fun i _ => R.M.foldl_mem _ R.M.start_mem) (Nat.lt_succ_self _)
  have hj : R.M.run ((List.range j).map actA ++ (List.range j).map actB) = true :=
    R.complete _ (by unfold CountGated; rw [count_as_bs, count_as_bs]; simp)
  have hi : R.M.run ((List.range i).map actA ++ (List.range j).map actB) = true := by
    unfold FinDFA.run at hj ⊢
    rw [List.foldl_append] at hj ⊢
    show R.M.accept (((List.range j).map actB).foldl R.M.step (f i)) = true
    rw [heq]
    exact hj
  have := R.sound _ hi
  unfold CountGated at this
  rw [count_as_bs, count_as_bs] at this
  simp at this
  omega

/-! ## §5 Necessity: a domain enforced at admission is not valid-sticky -/

/-- The pre-ADR-1909 admission: a vote is accepted only if its `:choice` is
in the opener's `:options`, read by `last propose :options`. -/
def domainAdmit (A : List Act) (a : Act) : Verdict :=
  if inDomain "choice" (allowedOf "propose" "options" A) a then .accepted else .rejected

/-- An opener offering one option. -/
def opener1 : Act := ⟨1, "propose", "@o", [], [("options", .list [.str "tacos"])], []⟩
/-- A concurrent opener at a greater address, offering another. -/
def opener2 : Act := ⟨2, "propose", "@o", [], [("options", .list [.str "ramen"])], []⟩
/-- A vote for the first opener's option. -/
def vote : Act := ⟨3, "vote", "@v", [1], [("choice", .str "tacos")], []⟩

/-- **Feedback breaks valid-stickiness**: the vote is accepted, then rejected
when a concurrent opener with a greater address arrives. -/
theorem domain_feedback_not_sticky :
    domainAdmit [opener1] vote = .accepted ∧ domainAdmit [opener1, opener2] vote = .rejected := by
  decide

end AdmissionStratification
end CBCL
