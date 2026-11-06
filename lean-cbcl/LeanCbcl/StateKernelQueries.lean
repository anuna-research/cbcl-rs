import LeanCbcl.StateKernelSemantics

/-! Independent query and finite-map semantics for SPEC-036. -/
namespace CBCL.StateKernelQueries
open CBCL.State CBCL.StateKernelSemantics

/-- Recognized physical/logical evidence, supplied independently of evaluation. -/
abbrev Clock := String → Act → Option (Nat × Nat)
/-- An order-preserving image of authenticated signer bytes. -/
abbrev SignerRank := String → Nat

/-- Explicit arbitration policy; legacy address rules do not acquire clocks. -/
inductive Policy where
  | address
  | hlc (field : String)
  deriving DecidableEq

/-- Typed key evidence, independent of search. -/
def Evidence (clock : Clock) (rank : SignerRank) (p : Policy) (a : Act)
    (key : HlcRegister.Key) : Prop :=
  match p with
  | .address => key = ⟨0, 0, 0, a.addr⟩
  | .hlc field => ∃ physical logical, clock field a = some (physical, logical) ∧
      key = ⟨physical, logical, rank a.signer, a.addr⟩

/-- Declarative greatest eligible act, or no eligible candidate. -/
def ChoiceMeaning (clock : Clock) (rank : SignerRank) (p : Policy)
    (P : Act → Prop) (result : Option Act) : Prop :=
  ((¬ ∃ a key, P a ∧ Evidence clock rank p a key) ∧ result = none) ∨
  ∃ a key, P a ∧ Evidence clock rank p a key ∧
    (∀ b other, P b → Evidence clock rank p b other → HlcRegister.LE other key) ∧ result = some a

/-- Concrete decoration from typed clock evidence. -/
def decorate (clock : Clock) (rank : SignerRank) (p : Policy) (a : Act) : Option (HlcRegister.Candidate Act) :=
  match p with
  | .address => some ⟨⟨0, 0, 0, a.addr⟩, a⟩
  | .hlc field => (clock field a).map (fun (physical, logical) =>
      ⟨⟨physical, logical, rank a.signer, a.addr⟩, a⟩)

/-- Eligible candidates preserve original act identities. -/
def candidates (clock : Clock) (rank : SignerRank) (p : Policy) (T : List Act) :=
  T.filterMap (decorate clock rank p)

/-- Choice is a pure maximum reduction over the supplied eligible table. -/
def choose (clock : Clock) (rank : SignerRank) (p : Policy) (T : List Act) : Option Act :=
  (HlcRegister.pick (candidates clock rank p T)).map HlcRegister.Candidate.value

theorem decorate_correct (clock : Clock) (rank : SignerRank) (p : Policy)
    (a : Act) (candidate : HlcRegister.Candidate Act) :
    decorate clock rank p a = some candidate ↔
      candidate.value = a ∧ Evidence clock rank p a candidate.key := by
  cases p with
  | address => cases candidate; simp [decorate, Evidence, HlcRegister.Candidate.mk.injEq, eq_comm, and_comm]
  | hlc field =>
      cases h : clock field a with
      | none => simp [decorate, Evidence, h]
      | some stamp =>
          rcases stamp with ⟨physical, logical⟩
          cases candidate with
          | mk key value =>
              constructor
              · intro eq
                have same : (⟨⟨physical, logical, rank a.signer, a.addr⟩, a⟩ : HlcRegister.Candidate Act) = ⟨key, value⟩ := by simpa [decorate, h] using eq
                rcases HlcRegister.Candidate.mk.inj same with ⟨rfl, rfl⟩
                exact ⟨rfl, physical, logical, h, rfl⟩
              · rintro ⟨same, px, lg, he, keyeq⟩
                change value = a at same
                subst value
                change clock field a = some (px, lg) at he
                simp only [h, Option.some.injEq, Prod.mk.injEq] at he
                rcases he with ⟨rfl, rfl⟩
                change key = ⟨physical, logical, rank a.signer, a.addr⟩ at keyeq
                subst key
                simp [decorate, h]

theorem candidate_member (clock : Clock) (rank : SignerRank) (p : Policy)
    (T : List Act) (candidate : HlcRegister.Candidate Act) :
    candidate ∈ candidates clock rank p T ↔
      candidate.value ∈ T ∧ Evidence clock rank p candidate.value candidate.key := by
  simp only [candidates, List.mem_filterMap, decorate_correct]
  constructor
  · rintro ⟨a, ha, same, evidence⟩; subst a; exact ⟨ha, evidence⟩
  · rintro ⟨ha, evidence⟩; exact ⟨candidate.value, ha, rfl, evidence⟩

/-- Maximum search meets an independent act-level specification. -/
theorem choose_satisfies (clock : Clock) (rank : SignerRank) (p : Policy) (T : List Act) :
    ChoiceMeaning clock rank p (fun a => a ∈ T) (choose clock rank p T) := by
  have good := HlcRegister.pick_satisfies (candidates clock rank p T)
  cases h : HlcRegister.pick (candidates clock rank p T) with
  | none =>
      rw [h] at good
      refine Or.inl ⟨?_, by simp [choose, h]⟩
      rintro ⟨a, key, ha, evidence⟩
      have member := (candidate_member clock rank p T ⟨key, a⟩).mpr ⟨ha, evidence⟩
      rw [good] at member
      exact List.not_mem_nil member
  | some candidate =>
      rw [h] at good
      obtain ⟨mem, evidence⟩ := (candidate_member _ _ _ _ _).mp good.1
      refine Or.inr ⟨candidate.value, candidate.key, mem, evidence, ?_, by simp [choose, h]⟩
      intro b other hb he
      exact good.2 ⟨other, b⟩ ((candidate_member _ _ _ _ _).mpr ⟨hb, he⟩)

theorem evidence_address {clock : Clock} {rank : SignerRank} {p : Policy}
    {a : Act} {key : HlcRegister.Key} (h : Evidence clock rank p a key) : key.address = a.addr := by
  cases p with
  | address => subst key; rfl
  | hlc field => obtain ⟨_, _, _, rfl⟩ := h; rfl

theorem choice_unique {clock : Clock} {rank : SignerRank} {p : Policy} {T : List Act}
    (unique : NodupAddr T) {x y : Option Act}
    (hx : ChoiceMeaning clock rank p (fun a => a ∈ T) x)
    (hy : ChoiceMeaning clock rank p (fun a => a ∈ T) y) : x = y := by
  rcases hx with ⟨empty, rfl⟩ | ⟨a, key, ha, ea, ma, rfl⟩
  · rcases hy with ⟨_, rfl⟩ | ⟨b, other, hb, eb, _, rfl⟩
    · rfl
    · exact False.elim (empty ⟨b, other, hb, eb⟩)
  · rcases hy with ⟨empty, rfl⟩ | ⟨b, other, hb, eb, mb, rfl⟩
    · exact False.elim (empty ⟨a, key, ha, ea⟩)
    · have keys := HlcRegister.le_antisymm (ma b other hb eb) (mb a key ha ea)
      have address := (evidence_address ea).symm.trans ((congrArg HlcRegister.Key.address keys.symm).trans (evidence_address eb))
      exact congrArg some (unique.eq_of_addr ha hb address)

theorem choose_correct {T : List Act} (unique : NodupAddr T)
    (clock : Clock) (rank : SignerRank) (p : Policy) (result : Option Act) :
    ChoiceMeaning clock rank p (fun a => a ∈ T) result ↔ result = choose clock rank p T := by
  constructor
  · intro h; exact choice_unique unique h (choose_satisfies clock rank p T)
  · rintro rfl; exact choose_satisfies clock rank p T

/-- Extensional replacement of source membership. -/
theorem choice_congr {P Q : Act → Prop} (same : ∀ a, P a ↔ Q a)
    (clock : Clock) (rank : SignerRank) (p : Policy) (result : Option Act) :
    ChoiceMeaning clock rank p P result ↔ ChoiceMeaning clock rank p Q result := by
  simp only [ChoiceMeaning, same]

/-- Finite map payloads, including absent selected fields and event provenance. -/
inductive Cell where
  | absent
  | value (v : Val)
  | event (signer : String) (v : Val)
  deriving DecidableEq

/-- Independent field-projection graph, including missing selected data. -/
inductive Projection (field : String) : Bool → Option Act → Cell → Prop where
  | empty {event : Bool} : Projection field event none .absent
  | missing {event : Bool} (a : Act) (h : a.get field = none) : Projection field event (some a) .absent
  | plain (a : Act) (v : Val) (h : a.get field = some v) : Projection field false (some a) (.value v)
  | paired (a : Act) (v : Val) (h : a.get field = some v) : Projection field true (some a) (.event a.signer v)

/-- Concrete data access after selection. -/
def project (field : String) (event : Bool) : Option Act → Cell
  | none => .absent
  | some a => match a.get field with
      | none => .absent
      | some v => if event then .event a.signer v else .value v

theorem project_correct (field : String) (event : Bool) (a : Option Act) :
    Projection field event a (project field event a) := by
  cases a with
  | none => exact .empty
  | some a =>
      cases h : a.get field with
      | none => simpa [project, h] using Projection.missing (event := event) a h
      | some v =>
          cases event with
          | false => simpa [project, h] using Projection.plain a v h
          | true => simpa [project, h] using Projection.paired a v h

/-- A scalar/event reduction is specified by independent choice and projection. -/
def CellMeaning (clock : Clock) (rank : SignerRank) (p : Policy) (P : Act → Prop)
    (field : String) (event : Bool) (cell : Cell) : Prop :=
  ∃ selected, ChoiceMeaning clock rank p P selected ∧ Projection field event selected cell

/-- Grouping is separate from candidate selection and arbitration. -/
inductive Group where
  | signer
  | key (field : String)
  | address
  deriving DecidableEq

/-- Group-key access is a typed input primitive, not a search. -/
def groupKey : Group → Act → Option Val
  | .signer, a => some (.str a.signer)
  | .key k, a => a.get k
  | .address, a => some (.int a.addr)

/-- A finite scalar/event map expression. -/
structure MapPlan where
  /-- Full admitted source; replacement is computed before grouping. -/
  source : Selection
  /-- A signer, application key or content-address grouping. -/
  group : Group
  /-- Explicit arbitration contract. -/
  policy : Policy
  /-- Payload field. -/
  field : String
  /-- Whether values retain the authenticated signer. -/
  event : Bool := false

/-- Finite support plus a total payload lookup; only supported keys are observed. -/
structure FiniteMap where
  /-- Distinct supported keys. -/
  keys : List Val
  /-- Payload for a supported key, possibly absent. -/
  read : Val → Cell

/-- Structural deduplication, independent of key enumeration order. -/
def uniqueKeys : List Val → List Val
  | [] => []
  | x :: xs => if x ∈ uniqueKeys xs then uniqueKeys xs else x :: uniqueKeys xs

theorem uniqueKeys_member (xs : List Val) (x : Val) : x ∈ uniqueKeys xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [uniqueKeys]
  | cons y ys ih => by_cases hy : y ∈ uniqueKeys ys <;> simp [uniqueKeys, hy, ih] <;> grind

theorem uniqueKeys_nodup (xs : List Val) : (uniqueKeys xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons y ys ih => by_cases hy : y ∈ uniqueKeys ys <;> simp [uniqueKeys, hy, ih]

/-- Executable map evaluation over an already admitted act source. -/
def evalMap (clock : Clock) (rank : SignerRank) (A : List Act) (plan : MapPlan) : FiniteMap :=
  let T := select A plan.source
  ⟨uniqueKeys (T.filterMap (groupKey plan.group)), fun key =>
    project plan.field plan.event (choose clock rank plan.policy
      (T.filter (fun a => groupKey plan.group a == some key)))⟩

/-- Independent graph: exact finite support and specified per-group payloads. -/
def MapMeaning (clock : Clock) (rank : SignerRank) (P : Act → Prop)
    (plan : MapPlan) (result : FiniteMap) : Prop :=
  result.keys.Nodup ∧
    (∀ key, key ∈ result.keys ↔ ∃ a, Selected P plan.source a ∧ groupKey plan.group a = some key) ∧
    ∀ key ∈ result.keys, CellMeaning clock rank plan.policy
      (fun a => Selected P plan.source a ∧ groupKey plan.group a = some key)
      plan.field plan.event (result.read key)

/-- Every supported map entry reduces exactly its specified group. -/
theorem map_correct (clock : Clock) (rank : SignerRank) (A : List Act) (plan : MapPlan) :
    MapMeaning clock rank (fun a => a ∈ A) plan (evalMap clock rank A plan) := by
  refine ⟨uniqueKeys_nodup _, ?_, ?_⟩
  · intro key
    simp only [evalMap, uniqueKeys_member, List.mem_filterMap, select_correct]
  · intro key _
    refine ⟨choose clock rank plan.policy ((select A plan.source).filter (fun a => groupKey plan.group a == some key)), ?_, project_correct _ _ _⟩
    apply (choice_congr (P := fun a => a ∈ (select A plan.source).filter (fun a => groupKey plan.group a == some key))
      (Q := fun a => Selected (fun a => a ∈ A) plan.source a ∧ groupKey plan.group a = some key)
      (fun a => by simp [select_correct]) clock rank plan.policy _).mp
    exact choose_satisfies _ _ _ _



/-- Projection completeness includes absence, value and event provenance. -/
theorem projection_complete (field : String) (event : Bool) (a : Option Act) (cell : Cell) :
    Projection field event a cell ↔ cell = project field event a := by
  constructor
  · intro h
    cases h with
    | empty => rfl
    | missing a h => simp [project, h]
    | plain a v h => simp [project, h]
    | paired a v h => simp [project, h]
  · rintro rfl; exact project_correct _ _ _

theorem cell_complete {T : List Act} (unique : NodupAddr T)
    (clock : Clock) (rank : SignerRank) (p : Policy) (field : String) (event : Bool) (cell : Cell) :
    CellMeaning clock rank p (fun a => a ∈ T) field event cell ↔
      cell = project field event (choose clock rank p T) := by
  constructor
  · rintro ⟨selected, choice, projected⟩
    have same := (choose_correct unique clock rank p selected).mp choice
    subst selected
    exact (projection_complete _ _ _ _).mp projected
  · intro same
    subst cell
    exact ⟨choose clock rank p T, choose_satisfies _ _ _ _, project_correct _ _ _⟩

/-- Sources with equivalent membership have equivalent map graph specifications. -/
theorem map_meaning_congr {P Q : Act → Prop} (same : ∀ a, P a ↔ Q a)
    (clock : Clock) (rank : SignerRank) (plan : MapPlan) (result : FiniteMap) :
    MapMeaning clock rank P plan result ↔ MapMeaning clock rank Q plan result := by
  have selected := fun a => selected_congr same plan.source a
  simp only [MapMeaning, CellMeaning, selected, ChoiceMeaning]

/-- Observation equality ignores enumeration order but retains every supported cell. -/
def MapEquivalent (left right : FiniteMap) : Prop :=
  (∀ key, key ∈ left.keys ↔ key ∈ right.keys) ∧
    ∀ key ∈ left.keys, left.read key = right.read key

/-- A map's complete denotation determines its extensional observation. -/
theorem map_complete {A : List Act} (unique : NodupAddr A) (clock : Clock)
    (rank : SignerRank) (plan : MapPlan) (result : FiniteMap) :
    MapMeaning clock rank (fun a => a ∈ A) plan result ↔
      result.keys.Nodup ∧ MapEquivalent result (evalMap clock rank A plan) := by
  have concrete := map_correct clock rank A plan
  constructor
  · rintro ⟨nodup, support, entries⟩
    refine ⟨nodup, fun key => (support key).trans (concrete.2.1 key).symm, ?_⟩
    intro key member
    have entry := entries key member
    have uniqueGroup := (select_unique unique plan.source).filter (fun a => groupKey plan.group a == some key)
    apply (cell_complete uniqueGroup clock rank plan.policy plan.field plan.event (result.read key)).mp
    rcases entry with ⟨chosen, choice, projected⟩
    refine ⟨chosen, ?_, projected⟩
    apply (choice_congr (P := fun a => a ∈ (select A plan.source).filter (fun a => groupKey plan.group a == some key))
      (Q := fun a => Selected (fun a => a ∈ A) plan.source a ∧ groupKey plan.group a = some key)
      (fun a => by simp [select_correct]) clock rank plan.policy chosen).mpr
    exact choice
  · rintro ⟨nodup, support, entries⟩
    refine ⟨nodup, fun key => (support key).trans (concrete.2.1 key), ?_⟩
    intro key member
    rw [entries key member]
    exact concrete.2.2 key ((support key).mp member)

end CBCL.StateKernelQueries
