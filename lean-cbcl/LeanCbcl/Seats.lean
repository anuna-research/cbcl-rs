/-
  SPEC-020 capability seats — the seat-state function over a SET of admitted meta acts.

  Mirrors SPEC-020 v0.6.0 REQ-2017 (seat state), REQ-2037 (contests), REQ-2040/2045
  (terminations are admitted meta acts) and the position status used by REQ-2046/2047
  (round membership and discharge). Self-contained: Lean core only, in the style of
  `LeanCbcl/EPP.lean`; a set of admitted meta acts is a structure of predicates.

  What is modelled. A thread's seats form a forest: every non-root seat has a chain
  parent (the seat its grant was issued under); a `Moved` or `Reseated` seat replaces a
  seat and inherits that seat's chain parent. The admitted meta acts of one authority
  past are a set `S`. From `S` alone the spec defines which seats are issued, which are
  removed, which have a successor, and which are live. There is no orderer: the only
  inputs are `S` and the static forest.

  What is proved (safety level).
  * `successor_unique`  — a seat has at most one successor (REQ-2017 step 3).
  * `removed_mono`      — removal is monotone in `S`: more admitted meta acts never
                          revive a seat (REQ-2023, remove-wins).
  * `live_parent`       — a live seat's chain parent is live (REQ-2017 step 5).
  * `live_of_superset`  — a seat issued in `S` and live in a superset `S'` is live in `S`.
  * `status_trichotomy` — a terminated seat is moved, emptied or contested, and never
                          two of these (REQ-2037, Terminology "emptied position").
  * Order independence of `seat_state` is by construction: every definition is a
    function of the set `S`, so there is no order to depend on (NFR-2001).

  What is NOT modelled: admission of the meta acts themselves (signatures, policy,
  narrowing, recipients), anchor walks, and liveness over infinite traces. Those stay
  with the Rust core and its property tests (TEST-2041) and with Open.
-/

namespace LeanCbcl.Seats

/-- The static forest of seat identities of one thread. `Seat` is the type of seat ids
    (`Root`, `Grant h`, `Moved h`, `Reseated h` in the Rust core); `Grant` is the type
    of grant hashes. -/
structure Forest (Seat Grant : Type) where
  /-- Root seats come from the cast. -/
  rootSeat : Seat → Prop
  /-- Chain parent: the seat a granted seat was issued under. Root seats have none. -/
  parent : Seat → Option Seat
  /-- The seat a `Moved` or `Reseated` seat replaces, if any. -/
  replaces : Seat → Option Seat
  /-- A replacing seat inherits the chain parent of the seat it replaces
      (Terminology "Chain": the replaced seat is swapped for the replacement). -/
  replaces_parent : ∀ Y X, replaces Y = some X → parent Y = parent X
  /-- A root seat has no chain parent. -/
  root_no_parent : ∀ X, rootSeat X → parent X = none

/-- A set of admitted meta acts, as predicates. Admission (REQ-2007–2012, REQ-2040,
    REQ-2045, REQ-2031) is assumed: every act here was `Valid` in its own authority
    past. Two accepts of one transfer by one holder are one act (REQ-2045). -/
structure MetaSet (Seat Grant : Type) where
  /-- `grantIssued g X`: an admitted `facet`, `share` or `appoint` grant `g` issuing seat `X`. -/
  grantIssued : Grant → Seat → Prop
  /-- `transferFrom g X`: an admitted `transfer` grant `g` offering seat `X`. -/
  transferFrom : Grant → Seat → Prop
  /-- `accept g Y`: an admitted accept of transfer `g`, whose `Moved` seat is `Y`. -/
  accept : Grant → Seat → Prop
  /-- An admitted `resign` of seat `X`. -/
  resign : Seat → Prop
  /-- An admitted `revoke` naming the grant of seat `X`. -/
  revoke : Seat → Prop
  /-- `reseat X Y`: an admitted `reseat` naming seat `X`, whose `Reseated` seat is `Y`. -/
  reseat : Seat → Seat → Prop

variable {Seat Grant : Type} (F : Forest Seat Grant)

/-- `S ⊆ S'` pointwise on every family of meta acts. -/
def MetaSet.Sub (S S' : MetaSet Seat Grant) : Prop :=
  (∀ g X, S.grantIssued g X → S'.grantIssued g X) ∧
  (∀ g X, S.transferFrom g X → S'.transferFrom g X) ∧
  (∀ g Y, S.accept g Y → S'.accept g Y) ∧
  (∀ X, S.resign X → S'.resign X) ∧
  (∀ X, S.revoke X → S'.revoke X) ∧
  (∀ X Y, S.reseat X Y → S'.reseat X Y)

section Terminations
variable (S : MetaSet Seat Grant)

/-- An accept termination of `X`: an admitted accept of an admitted transfer from `X`,
    issuing `Y`. -/
def acceptTerm (X Y : Seat) : Prop := ∃ g, S.transferFrom g X ∧ S.accept g Y
/-- A resign or revoke of `X` ("kill"). -/
def killTerm (X : Seat) : Prop := S.resign X ∨ S.revoke X
/-- A reseat naming `X`. -/
def reseatTerm (X : Seat) : Prop := ∃ Y, S.reseat X Y
/-- `X` has some termination in `S` (REQ-2017 step 2). -/
def terminated (X : Seat) : Prop :=
  (∃ Y, acceptTerm S X Y) ∨ killTerm S X ∨ reseatTerm S X

/-- Exactly one reseat names `X`, issuing `Y`. -/
def uniqueReseat (X Y : Seat) : Prop :=
  S.reseat X Y ∧ ∀ Y', S.reseat X Y' → Y' = Y
/-- Exactly one accept terminates `X`, issuing `Y`. -/
def uniqueAccept (X Y : Seat) : Prop :=
  acceptTerm S X Y ∧ ∀ Y', acceptTerm S X Y' → Y' = Y

/-- REQ-2017 step 3 / REQ-2037. A single reseat dominates every other termination.
    Otherwise, with no reseat and no kill, a single accept moves the seat. -/
def successor (X Y : Seat) : Prop :=
  uniqueReseat S X Y ∨
  (¬ reseatTerm S X ∧ ¬ killTerm S X ∧ uniqueAccept S X Y)

/-- REQ-2017 step 1. Issued seats: roots; grants whose parent is issued; and the
    successor of an issued seat. Inductive, so issuance along a replacement chain is
    well founded and a contested seat issues nothing at any depth. -/
inductive issued : Seat → Prop
  | root {X} : F.rootSeat X → issued X
  | grant {g X Z} : S.grantIssued g X → F.parent X = some Z → issued Z → issued X
  | succ {X Y} : issued X → successor S X Y → F.replaces Y = some X → issued Y

/-- REQ-2017 step 4. A seat is removed when it has a termination, or when its chain
    parent is removed (cascade closure). -/
inductive removed : Seat → Prop
  | direct {X} : terminated S X → removed X
  | cascade {X Z} : F.parent X = some Z → removed Z → removed X

/-- REQ-2017 step 5. -/
def live (X : Seat) : Prop := issued F S X ∧ ¬ removed F S X

/-- A terminated seat with no successor is *emptied* when a kill is among its
    terminations, and *contested* otherwise (two or more accepts, or two or more
    reseats, and no kill). -/
def moved (X : Seat) : Prop := ∃ Y, successor S X Y
def emptied (X : Seat) : Prop := terminated S X ∧ ¬ moved S X ∧ killTerm S X
def contested (X : Seat) : Prop := terminated S X ∧ ¬ moved S X ∧ ¬ killTerm S X

end Terminations

/-! ### Theorems -/

section Theorems
variable (S S' : MetaSet Seat Grant)

/-- REQ-2017 step 3: at most one successor. -/
theorem successor_unique {X Y Y' : Seat}
    (h : successor S X Y) (h' : successor S X Y') : Y = Y' := by
  rcases h with hr | ⟨hnr, _, ha⟩
  · rcases h' with hr' | ⟨hnr', _, _⟩
    · exact hr'.2 Y hr.1
    · exact absurd ⟨Y, hr.1⟩ hnr'
  · rcases h' with hr' | ⟨_, _, ha'⟩
    · exact absurd ⟨Y', hr'.1⟩ hnr
    · exact ha'.2 Y ha.1

theorem acceptTerm_mono (hS : S.Sub S') {X Y : Seat} (h : acceptTerm S X Y) :
    acceptTerm S' X Y := by
  obtain ⟨g, ht, ha⟩ := h
  exact ⟨g, hS.2.1 g X ht, hS.2.2.1 g Y ha⟩

theorem killTerm_mono (hS : S.Sub S') {X : Seat} (h : killTerm S X) : killTerm S' X := by
  rcases h with h | h
  · exact Or.inl (hS.2.2.2.1 X h)
  · exact Or.inr (hS.2.2.2.2.1 X h)

theorem reseatTerm_mono (hS : S.Sub S') {X : Seat} (h : reseatTerm S X) : reseatTerm S' X := by
  obtain ⟨Y, h⟩ := h
  exact ⟨Y, hS.2.2.2.2.2 X Y h⟩

theorem terminated_mono (hS : S.Sub S') {X : Seat} (h : terminated S X) : terminated S' X := by
  rcases h with ⟨Y, h⟩ | h | h
  · exact Or.inl ⟨Y, acceptTerm_mono S S' hS h⟩
  · exact Or.inr (Or.inl (killTerm_mono S S' hS h))
  · exact Or.inr (Or.inr (reseatTerm_mono S S' hS h))

/-- REQ-2023 / ADR-2005 (remove-wins): removal is monotone in the set of admitted meta
    acts. A later-seen accept, resign, revoke or reseat never revives a removed seat. -/
theorem removed_mono (hS : S.Sub S') {X : Seat} (h : removed F S X) : removed F S' X := by
  induction h with
  | direct ht => exact removed.direct (terminated_mono S S' hS ht)
  | cascade hp _ ih => exact removed.cascade hp ih

/-- An issued seat's chain parent is issued. -/
theorem issued_parent {X Z : Seat} (h : issued F S X) (hp : F.parent X = some Z) :
    issued F S Z := by
  induction h generalizing Z with
  | root hr => rw [F.root_no_parent _ hr] at hp; cases hp
  | grant _ hp' hz _ => rw [hp'] at hp; cases hp; exact hz
  | succ _ _ hrep ih => exact ih (by rw [← F.replaces_parent _ _ hrep]; exact hp)

/-- REQ-2017 step 5: a live seat's chain parent is live. -/
theorem live_parent {X Z : Seat} (h : live F S X) (hp : F.parent X = some Z) : live F S Z := by
  refine ⟨issued_parent F S h.1 hp, fun hr => h.2 (removed.cascade hp hr)⟩

/-- A seat issued in `S` and live in a superset `S'` is live in `S`. Together with
    `removed_mono` this is the admission-side reading of monotonicity (REQ-2024): a
    verdict computed over a smaller authority past is never contradicted on liveness
    by a larger one, except through issuance, which the larger past may withdraw by a
    contest. -/
theorem live_of_superset (hS : S.Sub S') {X : Seat} (hi : issued F S X) (hl : live F S' X) :
    live F S X :=
  ⟨hi, fun hr => hl.2 (removed_mono F S S' hS hr)⟩

/-- A terminated seat is exactly one of moved, emptied or contested. -/
theorem status_trichotomy {X : Seat} (ht : terminated S X) :
    (moved S X ∧ ¬ emptied S X ∧ ¬ contested S X) ∨
    (emptied S X ∧ ¬ moved S X ∧ ¬ contested S X) ∨
    (contested S X ∧ ¬ moved S X ∧ ¬ emptied S X) := by
  by_cases hm : moved S X
  · exact Or.inl ⟨hm, fun he => he.2.1 hm, fun hc => hc.2.1 hm⟩
  · by_cases hk : killTerm S X
    · exact Or.inr (Or.inl ⟨⟨ht, hm, hk⟩, hm, fun hc => hc.2.2 hk⟩)
    · exact Or.inr (Or.inr ⟨⟨ht, hm, hk⟩, hm, fun he => hk he.2.2⟩)

/-- REQ-2037: a single reseat issues a successor whatever else terminates the seat. -/
theorem reseat_dominates {X Y : Seat} (h : uniqueReseat S X Y) : successor S X Y :=
  Or.inl h

/-- REQ-2037: a resign or revoke blocks every accept-based successor. -/
theorem kill_blocks_accept {X Y : Seat} (hk : killTerm S X) (hnr : ¬ reseatTerm S X) :
    ¬ successor S X Y := by
  intro h
  rcases h with hr | ⟨_, hnk, _⟩
  · exact hnr ⟨Y, hr.1⟩
  · exact hnk hk

/-- REQ-2037: two accepts issuing different seats contest the position. -/
theorem two_accepts_contest {X Y Y' : Seat} (h : acceptTerm S X Y) (h' : acceptTerm S X Y')
    (hne : Y ≠ Y') (hnr : ¬ reseatTerm S X) (hnk : ¬ killTerm S X) : contested S X := by
  refine ⟨Or.inl ⟨Y, h⟩, ?_, hnk⟩
  rintro ⟨Z, hs⟩
  rcases hs with hr | ⟨_, _, ha⟩
  · exact hnr ⟨Z, hr.1⟩
  · exact hne ((ha.2 Y h).trans (ha.2 Y' h').symm)

end Theorems

/-! ### Positions and round membership (REQ-2046, REQ-2047) -/

section Positions
variable {Pos : Type} (S : MetaSet Seat Grant)

/-- Which position each principal seat belongs to. Facet seats are not principal and
    are not mapped. -/
structure Positions (Seat Pos : Type) where
  principalOf : Seat → Option Pos

variable (P : Positions Seat Pos)

/-- The terminal seat of a position: an issued principal seat with no issued successor. -/
def terminalSeat (p : Pos) (X : Seat) : Prop :=
  P.principalOf X = some p ∧ issued F S X ∧ ¬ ∃ Y, successor S X Y ∧ issued F S Y

/-- A position is live when its terminal seat is live. -/
def posLive (p : Pos) : Prop := ∃ X, terminalSeat F S P p X ∧ live F S X
/-- A position is contested when its terminal seat is contested. -/
def posContested (p : Pos) : Prop := ∃ X, terminalSeat F S P p X ∧ contested S X
/-- A position is emptied when its terminal seat is removed and not contested
    (Terminology "emptied position"). Cascade removal counts as emptied. -/
def posEmptied (p : Pos) : Prop :=
  ∃ X, terminalSeat F S P p X ∧ removed F S X ∧ ¬ contested S X

/-- Round membership (REQ-2046): the positions of the counted role present in the
    anchor's authority past and not emptied there. `present p` is "root position or
    created by a grant in `A(anchor)`", supplied by the caller. Contested positions
    stay members. -/
def member (present : Pos → Prop) (p : Pos) : Prop := present p ∧ ¬ posEmptied F S P p

/-- Membership is a function of the anchor's meta-act set: trivially, since every
    ingredient is. Stated so the obligation is visible. -/
theorem member_functional (present : Pos → Prop) (p : Pos) :
    member F S P present p ↔ (present p ∧ ¬ posEmptied F S P p) := Iff.rfl

end Positions

end LeanCbcl.Seats
