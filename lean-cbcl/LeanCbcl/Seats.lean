/-
  SPEC-020 capability seats — the warrant-state function over a SET of admitted meta acts.

  Mirrors SPEC-020 v0.7.1 REQ-2017 (warrant state), REQ-2037 (contests), REQ-2040/2045
  (terminations are admitted meta acts) and the seat status used by REQ-2046/2047
  (round membership and discharge). Self-contained: Lean core only, in the style of
  `LeanCbcl/EPP.lean`; a set of admitted meta acts is a structure of predicates. The
  admission verdict, the conservative extension of SPEC-014 and the anchor walk are in
  `LeanCbcl/SeatsAdmission.lean`.

  What is modelled. A thread's warrants form a forest: every non-root warrant has a chain
  parent (the warrant its grant was issued under); a `Moved` or `Reseated` warrant replaces a
  warrant and inherits that warrant's chain parent. The admitted meta acts of one authority
  past are a set `S`. From `S` alone the spec defines which warrants are issued, which are
  removed, which have a successor, and which are live. There is no orderer: the only
  inputs are `S` and the static forest.

  What is proved (safety level).
  * `successor_unique`  — a warrant has at most one successor (REQ-2017 step 3).
  * `removed_mono`      — removal is monotone in `S`: more admitted meta acts never
                          revive a warrant (REQ-2023, remove-wins).
  * `live_parent`       — a live warrant's chain parent is live (REQ-2017 step 5).
  * `live_of_superset`  — a warrant issued in `S` and live in a superset `S'` is live in `S`.
  * `status_trichotomy` — a terminated warrant is moved, emptied or contested, and never
                          two of these (REQ-2037, Terminology "emptied seat").
  * `live_empty`        — over no meta acts exactly the root warrants are live: the
                          SPEC-014 world (REQ-2001, REQ-2034).
  * Order independence of `warrant_state` is by construction: every definition is a
    function of the set `S`, so there is no order to depend on (NFR-2001).

  Seats (section `Seats`), under `WellFormed F S`: a seat's issued principal warrants form
  one chain from its origin (`reach_origin`, `reach_total`), so
  * `terminal_unique`       — a seat has at most one terminal warrant (Terminology);
  * `terminal_of_live`      — a live principal warrant of a seat is its terminal warrant;
  * `seat_status_trichotomy`— a seat with a terminal warrant is exactly one of live,
                              emptied or contested (Terminology "Seat status");
  * `member_of_contested`   — a contested seat stays a member (REQ-2037, REQ-2046);
  * `member_of_live`        — a seat with a live principal warrant is never discharged,
                              so an accepted transfer empties nothing (REQ-2047).

  What is NOT modelled: admission of the meta acts themselves (signatures, policy,
  narrowing, recipients), that every seat has a terminal warrant (needs the meta-act set
  finite; the Rust core's sets are), and liveness over infinite traces. Those stay with
  the Rust core and its property tests (TEST-2041) and with Open.
-/

namespace LeanCbcl.Seats

/-- The static forest of warrant identities of one thread. `Warrant` is the type of warrant ids
    (`Root`, `Grant h`, `Moved h`, `Reseated h` in the Rust core); `Grant` is the type
    of grant hashes. -/
structure Forest (Warrant Grant : Type) where
  /-- Root warrants come from the cast. -/
  rootWarrant : Warrant → Prop
  /-- Chain parent: the warrant a granted warrant was issued under. Root warrants have none. -/
  parent : Warrant → Option Warrant
  /-- The warrant a `Moved` or `Reseated` warrant replaces, if any. -/
  replaces : Warrant → Option Warrant
  /-- A replacing warrant inherits the chain parent of the warrant it replaces
      (Terminology "Chain": the replaced warrant is swapped for the replacement). -/
  replaces_parent : ∀ Y X, replaces Y = some X → parent Y = parent X
  /-- A root warrant has no chain parent. -/
  root_no_parent : ∀ X, rootWarrant X → parent X = none
  /-- A root warrant replaces nothing: it comes from the cast, not from a meta act. -/
  root_no_replaces : ∀ X, rootWarrant X → replaces X = none

/-- A set of admitted meta acts, as predicates. Admission (REQ-2007–2012, REQ-2040,
    REQ-2045, REQ-2031) is assumed: every act here was `Valid` in its own authority
    past. Two accepts of one transfer by one holder are one act (REQ-2045). -/
structure MetaSet (Warrant Grant : Type) where
  /-- `grantIssued g X`: an admitted `proxy`, `share` or `appoint` grant `g` issuing warrant `X`. -/
  grantIssued : Grant → Warrant → Prop
  /-- `transferFrom g X`: an admitted `transfer` grant `g` offering warrant `X`. -/
  transferFrom : Grant → Warrant → Prop
  /-- `accept g Y`: an admitted accept of transfer `g`, whose `Moved` warrant is `Y`. -/
  accept : Grant → Warrant → Prop
  /-- An admitted `resign` of warrant `X`. -/
  resign : Warrant → Prop
  /-- An admitted `revoke` naming the grant of warrant `X`. -/
  revoke : Warrant → Prop
  /-- `reseat X Y`: an admitted `reseat` naming warrant `X`, whose `Reseated` warrant is `Y`. -/
  reseat : Warrant → Warrant → Prop

variable {Warrant Grant : Type} (F : Forest Warrant Grant)

/-- `S ⊆ S'` pointwise on every family of meta acts. -/
def MetaSet.Sub (S S' : MetaSet Warrant Grant) : Prop :=
  (∀ g X, S.grantIssued g X → S'.grantIssued g X) ∧
  (∀ g X, S.transferFrom g X → S'.transferFrom g X) ∧
  (∀ g Y, S.accept g Y → S'.accept g Y) ∧
  (∀ X, S.resign X → S'.resign X) ∧
  (∀ X, S.revoke X → S'.revoke X) ∧
  (∀ X Y, S.reseat X Y → S'.reseat X Y)

/-- The empty set of meta acts: a thread whose roles are all policy-free (REQ-2001)
    admits no meta act, so its authority pasts yield this set. -/
def MetaSet.empty : MetaSet Warrant Grant where
  grantIssued _ _ := False
  transferFrom _ _ := False
  accept _ _ := False
  resign _ := False
  revoke _ := False
  reseat _ _ := False

/-- Cross-constraints between the forest and a set of admitted meta acts, which admission
    guarantees: a `Reseated` warrant replaces the warrant its reseat names (REQ-2032), a
    `Moved` warrant replaces the warrant its transfer offered (REQ-2045), and a grant issues
    a fresh warrant that replaces nothing. -/
structure WellFormed (F : Forest Warrant Grant) (S : MetaSet Warrant Grant) : Prop where
  reseat_replaces : ∀ X Y, S.reseat X Y → F.replaces Y = some X
  accept_replaces : ∀ g X Y, S.transferFrom g X → S.accept g Y → F.replaces Y = some X
  grant_no_replaces : ∀ g X, S.grantIssued g X → F.replaces X = none

section Terminations
variable (S : MetaSet Warrant Grant)

/-- An accept termination of `X`: an admitted accept of an admitted transfer from `X`,
    issuing `Y`. -/
def acceptTerm (X Y : Warrant) : Prop := ∃ g, S.transferFrom g X ∧ S.accept g Y
/-- A resign or revoke of `X` ("kill"). -/
def killTerm (X : Warrant) : Prop := S.resign X ∨ S.revoke X
/-- A reseat naming `X`. -/
def reseatTerm (X : Warrant) : Prop := ∃ Y, S.reseat X Y
/-- `X` has some termination in `S` (REQ-2017 step 2). -/
def terminated (X : Warrant) : Prop :=
  (∃ Y, acceptTerm S X Y) ∨ killTerm S X ∨ reseatTerm S X

/-- Exactly one reseat names `X`, issuing `Y`. -/
def uniqueReseat (X Y : Warrant) : Prop :=
  S.reseat X Y ∧ ∀ Y', S.reseat X Y' → Y' = Y
/-- Exactly one accept terminates `X`, issuing `Y`. -/
def uniqueAccept (X Y : Warrant) : Prop :=
  acceptTerm S X Y ∧ ∀ Y', acceptTerm S X Y' → Y' = Y

/-- REQ-2017 step 3 / REQ-2037. A single reseat dominates every other termination.
    Otherwise, with no reseat and no kill, a single accept moves the warrant. -/
def successor (X Y : Warrant) : Prop :=
  uniqueReseat S X Y ∨
  (¬ reseatTerm S X ∧ ¬ killTerm S X ∧ uniqueAccept S X Y)

/-- REQ-2017 step 1. Issued warrants: roots; grants whose parent is issued; and the
    successor of an issued warrant. Inductive, so issuance along a replacement chain is
    well founded and a contested warrant issues nothing at any depth. -/
inductive issued : Warrant → Prop
  | root {X} : F.rootWarrant X → issued X
  | grant {g X Z} : S.grantIssued g X → F.parent X = some Z → issued Z → issued X
  | succ {X Y} : issued X → successor S X Y → F.replaces Y = some X → issued Y

/-- REQ-2017 step 4. A warrant is removed when it has a termination, or when its chain
    parent is removed (cascade closure). -/
inductive removed : Warrant → Prop
  | direct {X} : terminated S X → removed X
  | cascade {X Z} : F.parent X = some Z → removed Z → removed X

/-- REQ-2017 step 5. -/
def live (X : Warrant) : Prop := issued F S X ∧ ¬ removed F S X

/-- A terminated warrant with no successor is *emptied* when a kill is among its
    terminations, and *contested* otherwise (two or more accepts, or two or more
    reseats, and no kill). -/
def moved (X : Warrant) : Prop := ∃ Y, successor S X Y
def emptied (X : Warrant) : Prop := terminated S X ∧ ¬ moved S X ∧ killTerm S X
def contested (X : Warrant) : Prop := terminated S X ∧ ¬ moved S X ∧ ¬ killTerm S X

end Terminations

/-! ### Theorems -/

section Theorems
variable (S S' : MetaSet Warrant Grant)

/-- REQ-2017 step 3: at most one successor. -/
theorem successor_unique {X Y Y' : Warrant}
    (h : successor S X Y) (h' : successor S X Y') : Y = Y' := by
  rcases h with hr | ⟨hnr, _, ha⟩
  · rcases h' with hr' | ⟨hnr', _, _⟩
    · exact hr'.2 Y hr.1
    · exact absurd ⟨Y, hr.1⟩ hnr'
  · rcases h' with hr' | ⟨_, _, ha'⟩
    · exact absurd ⟨Y', hr'.1⟩ hnr
    · exact ha'.2 Y ha.1

theorem acceptTerm_mono (hS : S.Sub S') {X Y : Warrant} (h : acceptTerm S X Y) :
    acceptTerm S' X Y := by
  obtain ⟨g, ht, ha⟩ := h
  exact ⟨g, hS.2.1 g X ht, hS.2.2.1 g Y ha⟩

theorem killTerm_mono (hS : S.Sub S') {X : Warrant} (h : killTerm S X) : killTerm S' X := by
  rcases h with h | h
  · exact Or.inl (hS.2.2.2.1 X h)
  · exact Or.inr (hS.2.2.2.2.1 X h)

theorem reseatTerm_mono (hS : S.Sub S') {X : Warrant} (h : reseatTerm S X) : reseatTerm S' X := by
  obtain ⟨Y, h⟩ := h
  exact ⟨Y, hS.2.2.2.2.2 X Y h⟩

theorem terminated_mono (hS : S.Sub S') {X : Warrant} (h : terminated S X) : terminated S' X := by
  rcases h with ⟨Y, h⟩ | h | h
  · exact Or.inl ⟨Y, acceptTerm_mono S S' hS h⟩
  · exact Or.inr (Or.inl (killTerm_mono S S' hS h))
  · exact Or.inr (Or.inr (reseatTerm_mono S S' hS h))

/-- REQ-2023 / ADR-2005 (remove-wins): removal is monotone in the set of admitted meta
    acts. A later-seen accept, resign, revoke or reseat never revives a removed warrant. -/
theorem removed_mono (hS : S.Sub S') {X : Warrant} (h : removed F S X) : removed F S' X := by
  induction h with
  | direct ht => exact removed.direct (terminated_mono S S' hS ht)
  | cascade hp _ ih => exact removed.cascade hp ih

/-- An issued warrant's chain parent is issued. -/
theorem issued_parent {X Z : Warrant} (h : issued F S X) (hp : F.parent X = some Z) :
    issued F S Z := by
  induction h generalizing Z with
  | root hr => rw [F.root_no_parent _ hr] at hp; cases hp
  | grant _ hp' hz _ => rw [hp'] at hp; cases hp; exact hz
  | succ _ _ hrep ih => exact ih (by rw [← F.replaces_parent _ _ hrep]; exact hp)

/-- REQ-2017 step 5: a live warrant's chain parent is live. -/
theorem live_parent {X Z : Warrant} (h : live F S X) (hp : F.parent X = some Z) : live F S Z := by
  refine ⟨issued_parent F S h.1 hp, fun hr => h.2 (removed.cascade hp hr)⟩

/-- A warrant issued in `S` and live in a superset `S'` is live in `S`. Together with
    `removed_mono` this is the admission-side reading of monotonicity (REQ-2024): a
    verdict computed over a smaller authority past is never contradicted on liveness
    by a larger one, except through issuance, which the larger past may withdraw by a
    contest. -/
theorem live_of_superset (hS : S.Sub S') {X : Warrant} (hi : issued F S X) (hl : live F S' X) :
    live F S X :=
  ⟨hi, fun hr => hl.2 (removed_mono F S S' hS hr)⟩

/-- A terminated warrant is exactly one of moved, emptied or contested. -/
theorem status_trichotomy {X : Warrant} (ht : terminated S X) :
    (moved S X ∧ ¬ emptied S X ∧ ¬ contested S X) ∨
    (emptied S X ∧ ¬ moved S X ∧ ¬ contested S X) ∨
    (contested S X ∧ ¬ moved S X ∧ ¬ emptied S X) := by
  by_cases hm : moved S X
  · exact Or.inl ⟨hm, fun he => he.2.1 hm, fun hc => hc.2.1 hm⟩
  · by_cases hk : killTerm S X
    · exact Or.inr (Or.inl ⟨⟨ht, hm, hk⟩, hm, fun hc => hc.2.2 hk⟩)
    · exact Or.inr (Or.inr ⟨⟨ht, hm, hk⟩, hm, fun he => hk he.2.2⟩)

/-- REQ-2037: a single reseat issues a successor whatever else terminates the warrant. -/
theorem reseat_dominates {X Y : Warrant} (h : uniqueReseat S X Y) : successor S X Y :=
  Or.inl h

/-- REQ-2037: a resign or revoke blocks every accept-based successor. -/
theorem kill_blocks_accept {X Y : Warrant} (hk : killTerm S X) (hnr : ¬ reseatTerm S X) :
    ¬ successor S X Y := by
  intro h
  rcases h with hr | ⟨_, hnk, _⟩
  · exact hnr ⟨Y, hr.1⟩
  · exact hnk hk

/-- REQ-2037: two accepts issuing different warrants contest the seat. -/
theorem two_accepts_contest {X Y Y' : Warrant} (h : acceptTerm S X Y) (h' : acceptTerm S X Y')
    (hne : Y ≠ Y') (hnr : ¬ reseatTerm S X) (hnk : ¬ killTerm S X) : contested S X := by
  refine ⟨Or.inl ⟨Y, h⟩, ?_, hnk⟩
  rintro ⟨Z, hs⟩
  rcases hs with hr | ⟨_, _, ha⟩
  · exact hnr ⟨Z, hr.1⟩
  · exact hne ((ha.2 Y h).trans (ha.2 Y' h').symm)

/-- A warrant with a successor is terminated: the reseat or the accept that issued the
    successor is one of its terminations. -/
theorem terminated_of_successor {X Y : Warrant} (hs : successor S X Y) : terminated S X := by
  rcases hs with hr | ⟨_, _, ha⟩
  · exact Or.inr (Or.inr ⟨Y, hr.1⟩)
  · exact Or.inl ⟨Y, ha.1⟩

/-- Under well-formedness a successor replaces the warrant it succeeds. -/
theorem successor_replaces (wf : WellFormed F S) {X Y : Warrant} (hs : successor S X Y) :
    F.replaces Y = some X := by
  rcases hs with hr | ⟨_, _, ha⟩
  · exact wf.reseat_replaces X Y hr.1
  · obtain ⟨g, ht, hacc⟩ := ha.1
    exact wf.accept_replaces g X Y ht hacc

/-- The successor of an issued warrant is issued (REQ-2017 step 1, third clause). -/
theorem issued_of_successor (wf : WellFormed F S) {X Y : Warrant} (hi : issued F S X)
    (hs : successor S X Y) : issued F S Y :=
  issued.succ hi hs (successor_replaces F S wf hs)

/-- An issued warrant that replaces `X` was issued as the successor of `X`, and `X` is
    issued: the only way into `issued` for a replacing warrant is step 3. -/
theorem issued_replaces_inv (wf : WellFormed F S) {X Y : Warrant} (hi : issued F S Y)
    (hrep : F.replaces Y = some X) : issued F S X ∧ successor S X Y := by
  cases hi with
  | root hr => rw [F.root_no_replaces _ hr] at hrep; cases hrep
  | grant hg _ _ => rw [wf.grant_no_replaces _ _ hg] at hrep; cases hrep
  | succ hiX hs hrep' => rw [hrep'] at hrep; cases hrep; exact ⟨hiX, hs⟩

/-- REQ-2001 / REQ-2034: over the empty meta-act set exactly the root warrants are live.
    This is the SPEC-014 world: every cast binding holds, nothing else exists. -/
theorem live_empty {X : Warrant} : live F MetaSet.empty X ↔ F.rootWarrant X := by
  constructor
  · rintro ⟨hi, _⟩
    cases hi with
    | root hr => exact hr
    | grant hg _ _ => exact hg.elim
    | succ _ hs _ =>
      rcases hs with hr | ⟨_, _, ha⟩
      · exact hr.1.elim
      · obtain ⟨_, ht, _⟩ := ha.1
        exact ht.elim
  · intro hr
    refine ⟨issued.root hr, fun hrem => ?_⟩
    clear hr
    induction hrem with
    | direct ht =>
      rcases ht with ⟨_, _, ht, _⟩ | (h | h) | ⟨_, h⟩
      · exact ht
      · exact h
      · exact h
      · exact h
    | cascade _ _ ih => exact ih

end Theorems

/-! ### Seats and round membership (REQ-2046, REQ-2047) -/

section Seats
variable {Seat : Type} (S : MetaSet Warrant Grant)

/-- Which warrant opened each seat: the cast's root warrant for a root seat, or the
    warrant a `share` or `appoint` grant issued. -/
structure SeatMap (Warrant Seat : Type) where
  origin : Seat → Warrant

variable (P : SeatMap Warrant Seat)

/-- The principal warrants of a seat: its origin, and every warrant that replaces one of
    them. A proxy warrant replaces nothing and opens no seat, so it is in no seat: it acts
    in its delegator's (ADR-2007). -/
inductive inSeat (p : Seat) : Warrant → Prop
  | origin : inSeat p (P.origin p)
  | step {X Y} : inSeat p X → F.replaces Y = some X → inSeat p Y

/-- The terminal warrant of a seat: an issued principal warrant with no issued successor. -/
def terminalWarrant (p : Seat) (X : Warrant) : Prop :=
  inSeat F P p X ∧ issued F S X ∧ ¬ ∃ Y, successor S X Y ∧ issued F S Y

/-- A seat is live when its terminal warrant is live. -/
def seatLive (p : Seat) : Prop := ∃ X, terminalWarrant F S P p X ∧ live F S X
/-- A seat is contested when its terminal warrant is contested. -/
def seatContested (p : Seat) : Prop := ∃ X, terminalWarrant F S P p X ∧ contested S X
/-- A seat is emptied when its terminal warrant is removed and not contested
    (Terminology "emptied seat"). Cascade removal counts as emptied. -/
def seatEmptied (p : Seat) : Prop :=
  ∃ X, terminalWarrant F S P p X ∧ removed F S X ∧ ¬ contested S X

/-- `reach X Y`: `Y` is `X`, or follows it through issued successors. -/
inductive reach : Warrant → Warrant → Prop
  | refl {X} : reach X X
  | step {X Y Z} : reach X Y → successor S Y Z → issued F S Z → reach X Z

/-- Every issued principal warrant of a seat descends from the seat's origin through
    issued successors: the seat's issued warrants form one chain. -/
theorem reach_origin (wf : WellFormed F S) {p : Seat} {X : Warrant} (h : inSeat F P p X)
    (hi : issued F S X) : reach F S (P.origin p) X := by
  induction h with
  | origin => exact reach.refl
  | step _ hrep ih =>
    obtain ⟨hiX, hs⟩ := issued_replaces_inv F S wf hi hrep
    exact reach.step (ih hiX) hs hi

/-- A reach is empty, or starts with one issued successor step. -/
theorem reach_first {X Y : Warrant} (h : reach F S X Y) :
    X = Y ∨ ∃ Z, successor S X Z ∧ issued F S Z ∧ reach F S Z Y := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ hs hi ih =>
    rcases ih with rfl | ⟨W, hsW, hiW, hrW⟩
    · exact Or.inr ⟨_, hs, hi, reach.refl⟩
    · exact Or.inr ⟨W, hsW, hiW, reach.step hrW hs hi⟩

/-- Two warrants reached from one warrant are comparable: successors are unique, so the
    chain never forks. -/
theorem reach_total {X Y Z : Warrant} (h : reach F S X Y) (h' : reach F S X Z) :
    reach F S Y Z ∨ reach F S Z Y := by
  induction h' with
  | refl => exact Or.inr h
  | step _ hs hi ih =>
    rcases ih with hYZ | hZY
    · exact Or.inl (reach.step hYZ hs hi)
    · rcases reach_first F S hZY with rfl | ⟨W, hsW, _, hrW⟩
      · exact Or.inl (reach.step reach.refl hs hi)
      · rw [successor_unique S hsW hs] at hrW
        exact Or.inr hrW

/-- Terminology "Terminal warrant": a seat has at most one. -/
theorem terminal_unique (wf : WellFormed F S) {p : Seat} {X X' : Warrant}
    (h : terminalWarrant F S P p X) (h' : terminalWarrant F S P p X') : X = X' := by
  have r := reach_origin F S P wf h.1 h.2.1
  have r' := reach_origin F S P wf h'.1 h'.2.1
  rcases reach_total F S r r' with hr | hr
  · rcases reach_first F S hr with heq | ⟨Z, hs, hi, _⟩
    · exact heq
    · exact absurd ⟨Z, hs, hi⟩ h.2.2
  · rcases reach_first F S hr with heq | ⟨Z, hs, hi, _⟩
    · exact heq.symm
    · exact absurd ⟨Z, hs, hi⟩ h'.2.2

/-- A terminal warrant has no successor at all: any successor of an issued warrant is
    issued. -/
theorem terminal_not_moved (wf : WellFormed F S) {p : Seat} {X : Warrant}
    (h : terminalWarrant F S P p X) : ¬ moved S X := by
  rintro ⟨Y, hs⟩
  exact h.2.2 ⟨Y, hs, issued_of_successor F S wf h.2.1 hs⟩

/-- A live principal warrant of a seat is the seat's terminal warrant. In particular an
    accepted transfer empties nothing (REQ-2047): the live `Moved` warrant is terminal. -/
theorem terminal_of_live (wf : WellFormed F S) {p : Seat} {X Y : Warrant}
    (hY : inSeat F P p Y) (hl : live F S Y) (ht : terminalWarrant F S P p X) : X = Y := by
  have r := reach_origin F S P wf hY hl.1
  have r' := reach_origin F S P wf ht.1 ht.2.1
  rcases reach_total F S r r' with hr | hr
  · rcases reach_first F S hr with heq | ⟨Z, hs, _, _⟩
    · exact heq.symm
    · exact absurd (removed.direct (terminated_of_successor S hs)) hl.2
  · rcases reach_first F S hr with heq | ⟨Z, hs, hi, _⟩
    · exact heq
    · exact absurd ⟨Z, hs, hi⟩ ht.2.2

/-- Terminology "Seat status": a seat with a terminal warrant is exactly one of live,
    emptied or contested. -/
theorem seat_status_trichotomy (wf : WellFormed F S) {p : Seat} {X : Warrant}
    (ht : terminalWarrant F S P p X) :
    (seatLive F S P p ∧ ¬ seatEmptied F S P p ∧ ¬ seatContested F S P p) ∨
    (seatEmptied F S P p ∧ ¬ seatLive F S P p ∧ ¬ seatContested F S P p) ∨
    (seatContested F S P p ∧ ¬ seatLive F S P p ∧ ¬ seatEmptied F S P p) := by
  have uniq : ∀ {X'}, terminalWarrant F S P p X' → X' = X :=
    fun ht' => terminal_unique F S P wf ht' ht
  by_cases hr : removed F S X
  · by_cases hc : contested S X
    · refine Or.inr (Or.inr ⟨⟨X, ht, hc⟩, ?_, ?_⟩)
      · rintro ⟨X', ht', hl⟩; rw [uniq ht'] at hl; exact hl.2 hr
      · rintro ⟨X', ht', _, hnc⟩; rw [uniq ht'] at hnc; exact hnc hc
    · refine Or.inr (Or.inl ⟨⟨X, ht, hr, hc⟩, ?_, ?_⟩)
      · rintro ⟨X', ht', hl⟩; rw [uniq ht'] at hl; exact hl.2 hr
      · rintro ⟨X', ht', hc'⟩; rw [uniq ht'] at hc'; exact hc hc'
  · refine Or.inl ⟨⟨X, ht, ht.2.1, hr⟩, ?_, ?_⟩
    · rintro ⟨X', ht', hr', _⟩; rw [uniq ht'] at hr'; exact hr hr'
    · rintro ⟨X', ht', hc⟩; rw [uniq ht'] at hc; exact hr (removed.direct hc.1)

/-- A seat holding a live principal warrant is live, and neither emptied nor contested. -/
theorem seatLive_of_live (wf : WellFormed F S) {p : Seat} {X Y : Warrant}
    (hY : inSeat F P p Y) (hl : live F S Y) (ht : terminalWarrant F S P p X) :
    seatLive F S P p ∧ ¬ seatEmptied F S P p ∧ ¬ seatContested F S P p := by
  rcases seat_status_trichotomy F S P wf ht with h | ⟨⟨X', ht', hr, _⟩, _⟩ | ⟨⟨X', ht', hc⟩, _⟩
  · exact h
  · rw [terminal_of_live F S P wf hY hl ht'] at hr; exact absurd hr hl.2
  · rw [terminal_of_live F S P wf hY hl ht'] at hc
    exact absurd (removed.direct hc.1) hl.2

/-- Round membership (REQ-2046): the seats of the counted role present in the
    anchor's authority past and not emptied there. `present p` is "root seat or
    created by a grant in `A(anchor)`", supplied by the caller. Contested seats
    stay members. -/
def member (present : Seat → Prop) (p : Seat) : Prop := present p ∧ ¬ seatEmptied F S P p

/-- Membership is a function of the anchor's meta-act set: trivially, since every
    ingredient is. Stated so the obligation is visible. -/
theorem member_functional (present : Seat → Prop) (p : Seat) :
    member F S P present p ↔ (present p ∧ ¬ seatEmptied F S P p) := Iff.rfl

/-- REQ-2037 / REQ-2046: a contested seat stays a member of every round it is present in. -/
theorem member_of_contested (wf : WellFormed F S) {present : Seat → Prop} {p : Seat}
    (hp : present p) (hc : seatContested F S P p) : member F S P present p := by
  refine ⟨hp, fun he => ?_⟩
  obtain ⟨X, ht, hc⟩ := hc
  rcases seat_status_trichotomy F S P wf ht with ⟨_, _, hnc⟩ | ⟨_, _, hnc⟩ | ⟨_, _, hne⟩
  · exact hnc ⟨X, ht, hc⟩
  · exact hnc ⟨X, ht, hc⟩
  · exact hne he

/-- REQ-2047: a seat holding a live principal warrant is a member whenever present. An
    accepted transfer therefore never discharges the seat. -/
theorem member_of_live (wf : WellFormed F S) {present : Seat → Prop} {p : Seat} {X Y : Warrant}
    (hp : present p) (hY : inSeat F P p Y) (hl : live F S Y) (ht : terminalWarrant F S P p X) :
    member F S P present p :=
  ⟨hp, (seatLive_of_live F S P wf hY hl ht).2.1⟩

end Seats

end LeanCbcl.Seats
