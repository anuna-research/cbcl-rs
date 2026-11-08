import LeanCbcl.StateJsonValue
import LeanCbcl.StateLift
import LeanCbcl.StateObservation
import LeanCbcl.StateExecutableFreeze

/-! Canonical fault evidence from finite witness sets. Ordering is explicitly
lexicographic on UTF-8 bytes, not quoted JSON text. The reference uses dedup and
merge sort; correspondence to native radix/count/scatter remains a boundary. -/
set_option autoImplicit false
namespace CBCL.StateFaultRendering
open State StateLift StateObservation Std

/-- Native address comparison keys, including the empty/prefix cases. -/
def bytes (text : String) : List UInt8 := text.toUTF8.data.toList

/-- Two valid strings with the same UTF-8 bytes are the same address. -/
theorem bytes_injective : Function.Injective bytes := by
  intro a b same
  have data := Array.toList_inj.mp same
  have arrays := ByteArray.ext data
  exact String.toByteArray_inj.mp arrays

/-- Native lexicographic byte-order comparison, with prefixes before extensions. -/
def byteLE (a b : String) : Bool := (compare (bytes a) (bytes b)).isLE

/-- Byte comparison is transitive. -/
theorem byte_trans (a b c : String) (ab : byteLE a b = true) (bc : byteLE b c = true) : byteLE a c = true :=
  TransOrd.isLE_trans ab bc

/-- Every pair of address byte strings is comparable. -/
theorem byte_total (a b : String) : (byteLE a b || byteLE b a) = true := by
  have swapped : compare (bytes b) (bytes a) = (compare (bytes a) (bytes b)).swap := OrientedOrd.eq_swap
  unfold byteLE
  rw [swapped]
  cases compare (bytes a) (bytes b) <;> rfl

/-- Antisymmetry identifies addresses rather than only their byte keys. -/
theorem byte_antisymm (a b : String) (ab : byteLE a b = true) (ba : byteLE b a = true) : a = b :=
  bytes_injective ((compare_eq_iff_eq).mp (OrientedCmp.isLE_antisymm ab ba))

/-- A canonical finite list representing exactly the observed address set. -/
def canonical (addresses : List String) : List String := (FinSet.dedup addresses).mergeSort byteLE

/-- Evidence canonicalization never discards or invents an address. -/
theorem canonical_member (addresses : List String) (address : String) :
    address ∈ canonical addresses ↔ address ∈ addresses := by
  simp [canonical,FinSet.mem_dedup]

/-- Canonical evidence has no repeated address. -/
theorem canonical_unique (addresses : List String) : (canonical addresses).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (FinSet.nodup_dedup addresses)

/-- The exact output order is the native UTF-8 byte order. -/
theorem canonical_order (addresses : List String) : (canonical addresses).Pairwise (fun a b => byteLE a b = true) :=
  List.pairwise_mergeSort byte_trans byte_total _

/-- Equal witness sets yield exactly equal canonical lists, irrespective of
original order or repeated delivery. No sortedness premise is supplied. -/
theorem canonical_setEq (A B : List String) (same : ∀ address, address ∈ A ↔ address ∈ B) : canonical A = canonical B := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ => byte_antisymm a b) (canonical_order A) (canonical_order B)
  apply (List.perm_ext_iff_of_nodup (canonical_unique A) (canonical_unique B)).mpr
  intro address
  simpa only [canonical_member] using same address

/-- Recanonicalization changes no bytes or witness ordering. -/
theorem canonical_idempotent (addresses : List String) : canonical (canonical addresses) = canonical addresses :=
  canonical_setEq _ _ (canonical_member addresses)

/-- Canonical finite-set representation descends through the existing quotient;
callers do not choose an ordering-sensitive representative. -/
def fromSet (evidence : FinSet String) : List String :=
  Quotient.lift (s := listSetoid String) canonical (fun A B same => canonical_setEq A B same) evidence

/-- The quotient presentation agrees with its executable finite-list input. -/
theorem fromSet_mk (addresses : List String) : fromSet (FinSet.mk addresses) = canonical addresses := rfl

/-- Public fault layout: sorted evidence, reason and status in fixed key order. -/
def fault (reason : String) (addresses : List String) : StateJsonValue.Value :=
  .map [(.str "evidence",.list ((canonical addresses).map StateJsonValue.Value.str)),
    (.str "reason",.str reason),(.str "status",.str "fault")]

/-- The fault object is determined by the reason and witness set. -/
theorem fault_setEq (reason : String) (A B : List String) (same : ∀ address, address ∈ A ↔ address ∈ B) :
    fault reason A = fault reason B := by rw [fault,fault,canonical_setEq A B same]

/-- Equal reasons and witness sets produce byte-identical complete JSON. -/
theorem fault_bytes (reason : String) (A B : List String) (same : ∀ address, address ∈ A ↔ address ∈ B) :
    StateJsonValue.emit (fault reason A) "" = StateJsonValue.render (fault reason B) := by
  rw [StateJsonValue.empty_buffer,fault_setEq reason A B same]

/-- A finite list realizes semantic evidence precisely by address membership. -/
def Realizes (evidence : Evidence) (witness : List Nat) : Prop := ∀ address, address ∈ witness ↔ evidence address

/-- Different finite realizations of the same semantic evidence have identical
encoded lists under any fixed native address representation. -/
theorem realization_independent (address : Nat → String) (evidence : Evidence) (A B : List Nat)
    (left : Realizes evidence A) (right : Realizes evidence B) : canonical (A.map address) = canonical (B.map address) := by
  apply canonical_setEq
  intro text
  simp only [List.mem_map]
  constructor
  · rintro ⟨id,member,rfl⟩; exact ⟨id,(right id).mpr ((left id).mp member),rfl⟩
  · rintro ⟨id,member,rfl⟩; exact ⟨id,(left id).mpr ((right id).mp member),rfl⟩

/-- With faithful address representation, rendered membership is exactly the
original semantic witness predicate, not merely a one-way support guarantee. -/
theorem realization_member (address : Nat → String) (injective : Function.Injective address)
    (evidence : Evidence) (witness : List Nat) (realized : Realizes evidence witness) (id : Nat) :
    address id ∈ canonical (witness.map address) ↔ evidence id := by
  rw [canonical_member, List.mem_map]
  constructor
  · rintro ⟨other,member,same⟩
    have identity := injective same
    subst other
    exact (realized id).mp member
  · intro member
    exact ⟨id,(realized id).mpr member,rfl⟩

/-- Witness growth is retained after sorting and duplicate removal. -/
theorem canonical_growth (A B : List String) (growth : ∀ address ∈ A, address ∈ B) :
    ∀ address ∈ canonical A, address ∈ canonical B := by
  intro address member
  exact (canonical_member B address).mpr (growth address ((canonical_member A address).mp member))

/-- Semantic fault presentation chooses any finite realization; canonicalization
makes that choice unobservable. Runtime emission uses executable witness lists. -/
noncomputable def semanticFault (reason : String) (address : Nat → String) (evidence : Evidence)
    (finite : ∃ witness, Realizes evidence witness) : StateJsonValue.Value :=
  fault reason ((Classical.choose finite).map address)

/-- Every exact finite witness realization yields the same semantic fault object. -/
theorem realized_fault (reason : String) (address : Nat → String) (evidence : Evidence) (witness : List Nat)
    (realized : Realizes evidence witness) (finite : ∃ witness, Realizes evidence witness) :
    fault reason (witness.map address) = semanticFault reason address evidence finite := by
  unfold semanticFault fault
  rw [realization_independent address evidence witness (Classical.choose finite) realized (Classical.choose_spec finite)]

/-- Existing executable freeze refinement constructs a finite exact realization
of every semantic fault, including all raw and concurrent-freeze witnesses. -/
theorem freeze_fault_enumerated {V : Type} (A : List Act) (ranked : StateExecutableFreeze.Ranked A) (verb : String)
    (contributes : Act → Bool) (policy : Bool) (raw : Option (List Nat)) (evaluate : List Act → V)
    (evidence : Evidence)
    (faulted : StateLVar.freezeRead (fun act => act ∈ A) verb (fun act => contributes act = true) policy
      (raw.map (fun ids => fun id => id ∈ ids)) evaluate A = .fault evidence) :
    ∃ witness, StateExecutableFreeze.read A verb contributes policy raw evaluate = .fault witness ∧ Realizes evidence witness := by
  have refined := StateExecutableFreeze.read_refinement A ranked verb contributes policy raw evaluate
  rw [faulted] at refined
  cases computed : StateExecutableFreeze.read A verb contributes policy raw evaluate with
  | snapshot value => simp [computed,StateExecutableFreeze.Read.semantic] at refined
  | frozen root value excluded => simp [computed,StateExecutableFreeze.Read.semantic] at refined
  | fault witness =>
    refine ⟨witness,rfl,?_⟩
    rw [computed] at refined
    have same : (fun id => id ∈ witness) = evidence := StateLVar.FreezeRead.fault.inj refined
    intro id
    exact Iff.of_eq (congrFun same id)

/-- Complete semantic-freeze fault to canonical public JSON, without a supplied
witness list or caller-provided canonical ordering. Reason agreement and native
address representation remain explicit independent inputs. -/
theorem freeze_fault_serialized {V : Type} (A : List Act) (ranked : StateExecutableFreeze.Ranked A) (verb : String)
    (contributes : Act → Bool) (policy : Bool) (raw : Option (List Nat)) (evaluate : List Act → V)
    (evidence : Evidence) (reason : String) (address : Nat → String)
    (faulted : StateLVar.freezeRead (fun act => act ∈ A) verb (fun act => contributes act = true) policy
      (raw.map (fun ids => fun id => id ∈ ids)) evaluate A = .fault evidence) :
    ∃ witness, StateExecutableFreeze.read A verb contributes policy raw evaluate = .fault witness ∧
      Realizes evidence witness ∧ ∀ finite : ∃ witness, Realizes evidence witness,
        StateJsonValue.emit (fault reason (witness.map address)) "" =
          StateJsonValue.render (semanticFault reason address evidence finite) := by
  obtain ⟨witness,computed,realized⟩ := freeze_fault_enumerated A ranked verb contributes policy raw evaluate evidence faulted
  exact ⟨witness,computed,realized,fun finite => by rw [StateJsonValue.empty_buffer,realized_fault reason address evidence witness realized finite]⟩

end CBCL.StateFaultRendering
