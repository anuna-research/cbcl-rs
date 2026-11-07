import LeanCbcl.StateLVar

/-! SPEC-038 REQ-3811: immutable context projection from accepted roots.
The decoder is the shared typed interpretation of an immutable root's validated
cast, not a mutable host callback. Wire recognition and signature authentication
remain the existing boundary obligations. Histories are thread-pinned and
identity-consistent at that boundary; defensive mixed-thread / same-address
signer checks in Rust are not modelled by the root projection. Current observation
paths are snapshots; this model covers sealed thread-context projections and
conflict evidence. Eventual dissemination uses a finite contextual witness, not
a minimal blame set. -/
namespace CBCL.StateContext
open State StateLift StateLVar

inductive Read where
  | pending
  | value (data : Val)
  | fault (evidence : Lattice.Set Nat)

def display : Sole → Read
  | .bot => .pending
  | .one _ (some value) => .value value
  | .one address none => .fault {address}
  | .top evidence => .fault evidence

/-- An immutable recognized root contributes its identity and decoded context.
No ordinary application act can modify that contribution. -/
def contribution (decode : Act → Option Val) (a : Act) : Sole :=
  if a.preds.isEmpty then .one a.addr (decode a) else .bot

def carrier (decode : Act → Option Val) (A : List Act) : Sole := lift (contribution decode) A

def read (decode : Act → Option Val) (A : List Act) : Read := display (carrier decode A)

theorem carrier_union (decode : Act → Option Val) (A B : List Act) :
    carrier decode (A ++ B) = carrier decode A ⊔ carrier decode B := lift_append _ A B

theorem read_setEq (decode : Act → Option Val) {A B : List Act} (same : SetEq A B) :
    read decode A = read decode B := by
  unfold read carrier
  rw [lift_setEq _ same]

/-- Two successful context reads agree, or their union is an explicit fault. -/
theorem display_quasi {a b : Sole} {x y : Val}
    (left : display a = .value x) (right : display b = .value y) :
    x = y ∨ ∃ evidence, display (a ⊔ b) = .fault evidence := by
  cases a with
  | bot => simp [display] at left
  | top _ => simp [display] at left
  | one aa value =>
    cases value with
    | none => simp [display] at left
    | some v =>
      have equal : v = x := by simpa [display] using left
      subst v
      cases b with
      | bot => simp [display] at right
      | top _ => simp [display] at right
      | one bb value =>
        cases value with
        | none => simp [display] at right
        | some v =>
          have equal : v = y := by simpa [display] using right
          subst v
          by_cases same : x = y
          · exact Or.inl same
          · refine Or.inr ⟨{aa} ∪ {bb}, ?_⟩
            change display (Sole.join (.one aa (some x)) (.one bb (some y))) = _
            simp [Sole.join, display, same]

theorem read_quasi (decode : Act → Option Val) {A B : List Act} {x y : Val}
    (left : read decode A = .value x) (right : read decode B = .value y) :
    x = y ∨ ∃ evidence, read decode (A ++ B) = .fault evidence := by
  rw [read, carrier_union]
  exact display_quasi left right

/-- A present but unrecognized cast is a fault, not an absent root. -/
theorem invalid_root_faults (decode : Act → Option Val) (a : Act)
    (root : a.preds.isEmpty = true) (invalid : decode a = none) :
    read decode [a] = .fault {a.addr} := by
  simp [read,carrier,contribution,lift_cons,lift_nil,root,invalid,join_bot,display]

/-- A unique recognized root supplies its context value exactly. -/
theorem recognized_root_value (decode : Act → Option Val) (a : Act) (v : Val)
    (root : a.preds.isEmpty = true) (decoded : decode a = some v) :
    read decode [a] = .value v := by
  simp [read,carrier,contribution,lift_cons,lift_nil,root,decoded,join_bot,display]

/-- Evidence of any fault is exactly the contributing root identities. -/
theorem fault_evidence {state : Sole} {evidence : Lattice.Set Nat}
    (fault : display state = .fault evidence) : evidence = Sole.evidence state := by
  cases state with
  | bot => simp [display] at fault
  | top e => simpa [display, Sole.evidence] using fault.symm
  | one address value =>
    cases value with
    | some _ => simp [display] at fault
    | none => simpa [display, Sole.evidence] using fault.symm

theorem fault_join {a b : Sole} {evidence : Lattice.Set Nat}
    (fault : display a = .fault evidence) : ∃ enlarged,
    display (a ⊔ b) = .fault enlarged ∧ ∀ address ∈ evidence, address ∈ enlarged := by
  have original := fault_evidence fault
  cases a with
  | bot => simp [display] at fault
  | top e =>
    cases b with
    | bot => exact ⟨e, rfl, by simp [original, Sole.evidence]⟩
    | one address value =>
      refine ⟨e ∪ {address}, rfl, ?_⟩
      intro n hn
      exact Or.inl (by simpa [original, Sole.evidence] using hn)
    | top other =>
      refine ⟨e ∪ other, rfl, ?_⟩
      intro n hn
      exact Or.inl (by simpa [original, Sole.evidence] using hn)
  | one address value =>
    cases value with
    | some _ => simp [display] at fault
    | none =>
      cases b with
      | bot => exact ⟨{address}, rfl, by simp [original, Sole.evidence]⟩
      | top e =>
        refine ⟨{address} ∪ e, rfl, ?_⟩
        intro n hn
        exact Or.inl (by simpa [original, Sole.evidence] using hn)
      | one other v =>
        change ∃ enlarged, display (Sole.join (.one address none) (.one other v)) = .fault enlarged ∧ _
        by_cases equal : address = other ∧ (none : Option Val) = v
        · obtain ⟨rfl, rfl⟩ := equal
          exact ⟨{address}, by simp [Sole.join,display], by simp [original,Sole.evidence]⟩
        · refine ⟨{address} ∪ {other}, by simp [Sole.join,display,equal], ?_⟩
          intro n hn
          exact Or.inl (by simpa [original,Sole.evidence] using hn)

/-- Growing accepted evidence preserves every context-fault witness. -/
theorem read_fault_persists (decode : Act → Option Val) {A B : List Act}
    (growth : ∀ a ∈ A, a ∈ B) {evidence : Lattice.Set Nat}
    (fault : read decode A = .fault evidence) : ∃ enlarged,
    read decode B = .fault enlarged ∧ ∀ address ∈ evidence, address ∈ enlarged := by
  have absorbs : carrier decode A ⊔ carrier decode B = carrier decode B :=
    lift_join_of_forall _ (fun a ha => join_lift_of_mem _ (growth a ha))
  obtain ⟨e, result, includes⟩ := fault_join (b := carrier decode B) fault
  rw [absorbs] at result
  exact ⟨e,result,includes⟩

open StateKernelDelivery AdmissionStratification

/-- Under actual replica delivery/fairness, every context fault eventually
appears permanently at the other replica with the original witness included. -/
theorem eventual_context_fault {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (decode : Act → Option Val) (atTime : Nat)
    {evidence : Lattice.Set Nat} (fault : read decode (left.run atTime).accepted = .fault evidence) :
    ∃ t, ∀ n, t ≤ n → ∃ enlarged,
      read decode (right.run n).accepted = .fault enlarged ∧
      ∀ address ∈ evidence, address ∈ enlarged := by
  obtain ⟨t, all⟩ := witness_dissemination left right (left.run atTime).accepted atTime (by simp)
  exact ⟨t, fun n hn => read_fault_persists decode (all n hn) fault⟩
end CBCL.StateContext
