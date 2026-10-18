/-
  SPEC-020 capability seats — the warrant-state function over a SET of admitted meta acts.

  Mirrors SPEC-020 v0.7.0 REQ-2017 (warrant state), REQ-2037 (contests), REQ-2040/2045
  (terminations are admitted meta acts) and the seat status used by REQ-2046/2047
  (round membership and discharge). Self-contained: Lean core only, in the style of
  `LeanCbcl/EPP.lean`; a set of admitted meta acts is a structure of predicates.

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
  * Order independence of `warrant_state` is by construction: every definition is a
    function of the set `S`, so there is no order to depend on (NFR-2001).

  What is NOT modelled: admission of the meta acts themselves (signatures, policy,
  narrowing, recipients), anchor walks, and liveness over infinite traces. Those stay
  with the Rust core and its property tests (TEST-2041) and with Open.
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

end Theorems

/-! ### Seats and round membership (REQ-2046, REQ-2047) -/

section Seats
variable {Seat : Type} (S : MetaSet Warrant Grant)

/-- Which seat each principal warrant belongs to. Proxy warrants are not principal and
    are not mapped. -/
structure SeatMap (Warrant Seat : Type) where
  principalOf : Warrant → Option Seat

variable (P : SeatMap Warrant Seat)

/-- The terminal warrant of a seat: an issued principal warrant with no issued successor. -/
def terminalWarrant (p : Seat) (X : Warrant) : Prop :=
  P.principalOf X = some p ∧ issued F S X ∧ ¬ ∃ Y, successor S X Y ∧ issued F S Y

/-- A seat is live when its terminal warrant is live. -/
def seatLive (p : Seat) : Prop := ∃ X, terminalWarrant F S P p X ∧ live F S X
/-- A seat is contested when its terminal warrant is contested. -/
def seatContested (p : Seat) : Prop := ∃ X, terminalWarrant F S P p X ∧ contested S X
/-- A seat is emptied when its terminal warrant is removed and not contested
    (Terminology "emptied seat"). Cascade removal counts as emptied. -/
def seatEmptied (p : Seat) : Prop :=
  ∃ X, terminalWarrant F S P p X ∧ removed F S X ∧ ¬ contested S X

/-- Round membership (REQ-2046): the seats of the counted role present in the
    anchor's authority past and not emptied there. `present p` is "root seat or
    created by a grant in `A(anchor)`", supplied by the caller. Contested seats
    stay members. -/
def member (present : Seat → Prop) (p : Seat) : Prop := present p ∧ ¬ seatEmptied F S P p

/-- Membership is a function of the anchor's meta-act set: trivially, since every
    ingredient is. Stated so the obligation is visible. -/
theorem member_functional (present : Seat → Prop) (p : Seat) :
    member F S P present p ↔ (present p ∧ ¬ seatEmptied F S P p) := Iff.rfl

end Seats

end LeanCbcl.Seats
