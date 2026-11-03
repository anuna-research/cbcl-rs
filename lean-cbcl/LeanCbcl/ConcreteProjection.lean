/-
  Concrete raw-edge projection following projection.rs::project: Rust copies the
  complete optional causal protocol, filtering only the separate Send/Recv map.
  Lists encode finite maps/sets (the Rust boundary supplies unique keys/members).
  The loop theorem covers even duplicate declarations: last relevant insert wins.

  Agreement follows from concrete clause-table preservation for any interpretation.
  This is not an equivalence of EPP resolved-first and deployed eager verification.
  Route derivation/authentication remain separate; Routes carries computed outputs.
-/
import LeanCbcl.ProtocolProjection

namespace LeanCbcl.ConcreteProjection
open LeanCbcl.EPP LeanCbcl.Projectability LeanCbcl.ProtoProjection

/-- Finite clause syntax corresponding to Rust protocol::NodeRef. -/
inductive NodeRef where
  | single (name : String)
  | any (names : List String)
  | all (names : List String)
  deriving DecidableEq, BEq

/-- All names referenced by a clause. -/
def NodeRef.names : NodeRef → List String
  | .single n => [n]
  | .any ns | .all ns => ns

/-- Usual predicate interpretation of Single/Any/All (not the runtime verifier). -/
def NodeRef.holds (present : String → Prop) : NodeRef → Prop
  | .single n => present n
  | .any ns => ∃ n, n ∈ ns ∧ present n
  | .all ns => ∀ n, n ∈ ns → present n

/-- Every stored step field; successors are preserved too. -/
structure StepDecl where
  /-- Stored performative field, copied independently of the map key. -/
  performative : String
  /-- Ordered predecessor clauses, including empty and repeated clauses. -/
  predecessors : List NodeRef
  /-- Ordered successor clauses. -/
  successors : List NodeRef
  deriving DecidableEq, BEq

/-- Keyed table; keys and the redundant performative field remain distinct. -/
abbrev Protocol := List (String × StepDecl)

/-- Key lookup; Rust BTreeMap encodings have unique keys. -/
def lookupStep (cp : Option Protocol) (name : String) : Option StepDecl :=
  cp.bind fun entries => (entries.find? (fun e => e.1 == name)).map (·.2)

/-- Concrete role annotation. -/
structure Annotation where
  /-- Declared sender role. -/
  sender : String
  /-- Declared recipient set, represented by membership. -/
  recipients : List String
  deriving DecidableEq, BEq

/-- Fields read by the Send/Recv insertion loop. -/
structure Performative where
  /-- Performative declaration name. -/
  name : String
  /-- Optional from/to annotation. -/
  annotation : Option Annotation
  deriving DecidableEq, BEq

/-- Local step kind, with Send taking precedence for self-addressed messages. -/
inductive LocalStep where
  | send | recv
  deriving DecidableEq, BEq

/-- A bystander or an unannotated declaration contributes no insertion. -/
def classify (p : Performative) (role : String) : Option LocalStep :=
  p.annotation.bind fun a =>
    if a.sender == role then some .send
    else if a.recipients.contains role then some .recv else none

/-- Extensional observation of a finite map, independent of tree representation. -/
abbrev StepMap := String → Option LocalStep

/-- One iteration of the Rust insertion loop. -/
def insertStep (role : String) (acc : StepMap) (p : Performative) : StepMap :=
  fun name => if p.name == name then (classify p role).or (acc name) else acc name

/-- Left-to-right finite-map insertion. -/
def runSteps (ps : List Performative) (role : String) (acc : StepMap) : StepMap :=
  ps.foldl (insertStep role) acc

/-- Declarative last-relevant-declaration lookup, including duplicate names. -/
def specifiedStep (ps : List Performative) (role name : String) : Option LocalStep :=
  match ps with
  | [] => none
  | p :: rest => (specifiedStep rest role name).or
      (if p.name == name then classify p role else none)

/-- The insertion loop refines declarative lookup on all inputs. -/
theorem runSteps_refines (ps : List Performative) (role : String) (acc : StepMap)
    (name : String) :
    runSteps ps role acc name = (specifiedStep ps role name).or (acc name) := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
    rw [runSteps, List.foldl_cons]
    change runSteps ps role (insertStep role acc p) name = _
    rw [ih]
    simp only [specifiedStep, insertStep]
    cases h : specifiedStep ps role name <;>
      cases hc : classify p role <;> split <;> simp_all [Option.or]

/-- No phantom steps: a projected key exists exactly when some relevant declaration exists. -/
theorem specifiedStep_isSome (ps : List Performative) (role name : String) :
    (specifiedStep ps role name).isSome = true ↔
      ∃ p, p ∈ ps ∧ p.name = name ∧ (classify p role).isSome = true := by
  induction ps with
  | nil => simp [specifiedStep]
  | cons p ps ih =>
    by_cases h : p.name = name
    · simp [specifiedStep, h, ih, Bool.or_eq_true, or_comm]
    · simp [specifiedStep, h, ih]

/-- An absent name cannot be inserted by projection. -/
theorem specifiedStep_absent (ps : List Performative) (role name : String)
    (h : ∀ p, p ∈ ps → p.name ≠ name) : specifiedStep ps role name = none := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [specifiedStep, h p (by simp), ih (fun q hq => h q (by simp [hq]))]

/-- If all declarations of a key agree, projection returns that classification.
    Unique-name installed dialects satisfy this premise for their one declaration. -/
theorem specifiedStep_of_agreement (ps : List Performative) (role name : String)
    (kind : Option LocalStep) (hex : ∃ p, p ∈ ps ∧ p.name = name)
    (hall : ∀ p, p ∈ ps → p.name = name → classify p role = kind) :
    specifiedStep ps role name = kind := by
  induction ps with
  | nil => simp at hex
  | cons p ps ih =>
    classical
    by_cases ht : ∃ q, q ∈ ps ∧ q.name = name
    · have htail := ih ht (fun q hq hn => hall q (by simp [hq]) hn)
      simp only [specifiedStep, htail]
      by_cases hp : p.name = name
      · simp [hp, hall p (by simp) hp]
      · simp [hp]
    · have hn : ∀ q, q ∈ ps → q.name ≠ name := by
        intro q hq he
        exact ht ⟨q, hq, he⟩
      have hp : p.name = name := by
        obtain ⟨q, hq, he⟩ := hex
        rcases List.mem_cons.mp hq with hq | hq
        · simpa [hq] using he
        · exact False.elim (ht ⟨q, hq, he⟩)
      simp [specifiedStep, specifiedStep_absent ps role name hn, hp, hall p (by simp) hp]

/-- Sender precedence, including self-addressing. -/
theorem classify_sender (name role : String) (recipients : List String) :
    classify ⟨name, some ⟨role, recipients⟩⟩ role = some .send := by
  simp [classify]

/-- Recv requires a distinct sender and recipient membership. -/
theorem classify_recipient (name sender role : String) (recipients : List String)
    (hs : sender ≠ role) (hr : role ∈ recipients) :
    classify ⟨name, some ⟨sender, recipients⟩⟩ role = some .recv := by
  simp [classify, hs, hr]

/-- Already-computed install-time and occupant routes; deriving these is external. -/
structure Routes where
  /-- Whether the dialect uses derive rather than reject mode. -/
  derive : Bool
  /-- Install-time routes keyed by performative name. -/
  roleRoutes : List (String × List String)
  /-- Derived routes keyed by performative, containing occupant keys. -/
  occupantRoutes : List (String × List String)
  /-- Whether project received a cast. -/
  hasCast : Bool
  /-- The endpoint occupant, if supplied. -/
  occupant : Option String

/-- Envelope membership, gated on derive and on cast/occupant availability. -/
def expects (routes : Routes) (role name : String) : Bool :=
  routes.derive &&
    (routes.roleRoutes.any (fun e => e.1 == name && e.2.contains role) ||
     (routes.hasCast && routes.occupant.any (fun occupant =>
       routes.occupantRoutes.any (fun e => e.1 == name && e.2.contains occupant))))

/-- First-declaration lookup, matching Dialect::find_performative exactly. -/
def annotationAt (ps : List Performative) (name : String) : Option Annotation :=
  (ps.find? (fun p => p.name == name)).bind (·.annotation)

/-- Interpret concrete annotations. None is a distinct absence of a role, not an
    empty-string role. The begin thread root retains D's explicit role interpretation. -/
def withAnnotations {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) : ProtoData (Option String) String Msg :=
  { D with
    psender := fun name => if name = "begin" then D.psender name
      else (annotationAt ps name).map (·.sender)
    precip := fun name role => if name = "begin" then D.precip name role
      else match annotationAt ps name, role with
        | some a, some r => r ∈ a.recipients
        | _, _ => False }

/-- The concrete annotation says this role is an endpoint. -/
def annotationKeeps (ps : List Performative) (role name : String) : Bool :=
  (annotationAt ps name).any fun a => a.sender == role || a.recipients.contains role

/-- Non-root type endpoints are exactly those described by a present annotation. -/
theorem annotationKeeps_iff {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) (role name : String) (hb : name ≠ "begin") :
    annotationKeeps ps role name = true ↔ typeEndpoint (withAnnotations D ps) name (some role) := by
  cases ha : annotationAt ps name <;>
    simp [annotationKeeps, withAnnotations, typeEndpoint, hb, ha]

/-- Declarations sharing a name must agree on the role annotation. This is an
    explicit semantic precondition, not an assertion that Rust installation checks it. -/
def AnnotationsConsistent (ps : List Performative) : Prop :=
  ∀ p, p ∈ ps → ∀ q, q ∈ ps → p.name = q.name → p.annotation = q.annotation

/-- Executable check of the consistency premise, permitting harmless identical duplicates. -/
def checkAnnotationsConsistent (ps : List Performative) : Bool :=
  ps.all fun p => ps.all fun q => decide (p.name = q.name → p.annotation = q.annotation)

/-- The executable premise check exactly characterizes annotation consistency. -/
theorem checkAnnotationsConsistent_iff (ps : List Performative) :
    checkAnnotationsConsistent ps = true ↔ AnnotationsConsistent ps := by
  simp only [checkAnnotationsConsistent, AnnotationsConsistent, List.all_eq_true, decide_eq_true_eq]

/-- Under consistent declarations, first lookup and last relevant insertion coincide. -/
theorem specifiedStep_first (ps : List Performative) (role name : String)
    (hc : AnnotationsConsistent ps) :
    specifiedStep ps role name = (ps.find? (fun p => p.name == name)).bind (fun p => classify p role) := by
  cases hf : ps.find? (fun p => p.name == name) with
  | none =>
    apply specifiedStep_absent
    intro p hp
    simpa using (List.find?_eq_none.mp hf) p hp
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hn : p.name = name := by simpa using List.find?_some hf
    apply specifiedStep_of_agreement ps role name (classify p role) ⟨p, hp, hn⟩
    intro q hq hqn
    have ha := hc q hq p hp (hqn.trans hn.symm)
    simp only [classify, ha]

/-- Concrete map membership matches the annotation endpoint mask, for every string role. -/
theorem specifiedStep_matches_annotation (ps : List Performative) (role name : String)
    (hc : AnnotationsConsistent ps) :
    (specifiedStep ps role name).isSome = annotationKeeps ps role name := by
  rw [specifiedStep_first ps role name hc]
  unfold annotationKeeps annotationAt
  cases hf : ps.find? (fun p => p.name == name) with
  | none => rfl
  | some p =>
    cases ha : p.annotation with
    | none => simp [classify, ha]
    | some a =>
      simp only [Option.bind_some, classify, ha, Option.any_some]
      split <;> rename_i h
      · simp_all
      · split <;> simp_all

/-- Concrete projection result with maps observed by key. -/
structure LocalProtocol where
  /-- Send/Recv map lookup. -/
  steps : StepMap
  /-- Expected envelope membership. -/
  expectEnvelopes : String → Bool
  /-- Unmodified dialect causal protocol. -/
  protocol : Option Protocol

/-- Actual raw-edge projection: insert local markers and copy the protocol. -/
def project (ps : List Performative) (cp : Option Protocol) (role : String)
    (routes : Routes) : LocalProtocol :=
  ⟨runSteps ps role (fun _ => none), expects routes role, cp⟩

/-- Observable steps satisfy the declarative projection rule. -/
theorem project_steps (ps : List Performative) (cp : Option Protocol)
    (role : String) (routes : Routes) (name : String) :
    (project ps cp role routes).steps name = specifiedStep ps role name := by
  change runSteps ps role (fun _ => none) name = _
  rw [runSteps_refines]
  cases specifiedStep ps role name <;> rfl

/-- All protocol fields survive, for every role and envelope mode. -/
theorem project_protocol (ps : List Performative) (cp : Option Protocol)
    (role : String) (routes : Routes) : (project ps cp role routes).protocol = cp := rfl

/-- Interpret concrete references and clauses, keeping the supplied message/role data.
    Parametric evaluation avoids silently choosing a deployed citation-route semantics. -/
def interpret {Role Msg : Type} (D : ProtoData Role String Msg) (cp : Option Protocol)
    (eval : Option StepDecl → (String → Prop) → Prop) : ProtoData Role String Msg :=
  { D with
    legalPred := fun t pred => ∃ st, lookupStep cp t = some st ∧
      pred ∈ st.predecessors.flatMap NodeRef.names
    clause := fun t present => eval (lookupStep cp t) present }

/-- Projection derives agreement; clause equality is a conclusion, not a hypothesis. -/
theorem project_agrees {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) (cp : Option Protocol) (role : String) (routes : Routes)
    (eval : Option StepDecl → (String → Prop) → Prop) :
    AgreesOnRole (interpret (withAnnotations D ps) cp eval)
      (interpret (withAnnotations D ps) (project ps cp role routes).protocol eval) (some role) :=
  agreesOnRole_refl _ _

/-- EPP local/global verdict correspondence with concrete raw-table projection. -/
theorem projected_verification_agrees {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) (cp : Option Protocol) (role : String) (routes : Routes)
    (eval : Option StepDecl → (String → Prop) → Prop)
    (hloc : (interpret (withAnnotations D ps) cp eval).causalLocality) {C : Cfg Msg}
    (hcl : (interpret (withAnnotations D ps) cp eval).closedCfgD C) (hsafe : (interpret (withAnnotations D ps) cp eval).pSafeD C)
    {m : Msg} (hm : (interpret (withAnnotations D ps) cp eval).projectD C (some role) m) :
    let Q := interpret (withAnnotations D ps) (project ps cp role routes).protocol eval
    ¬ Q.isUnknownD (Q.projectD C (some role)) m ∧
    (Q.isValidD (Q.projectD C (some role)) m ↔ (interpret (withAnnotations D ps) cp eval).isValidD C m) ∧
    (Q.isViolationD (Q.projectD C (some role)) m ↔ (interpret (withAnnotations D ps) cp eval).isViolationD C m) :=
  local_protocol_verification_agrees (project_agrees D ps cp role routes eval)
    hloc hcl hsafe hm

/-- The paper's raw-edge view erases table entries but leaves retained steps intact.
    This differs from Rust's LocalProtocol.protocol, which retains the whole table. -/
def restrictProtocol (cp : Option Protocol) (keep : String → Bool) : Option Protocol :=
  cp.map (List.filter (fun e => keep e.1))

/-- Erasing other keys cannot change a retained key's complete step declaration. -/
theorem lookup_restrict (cp : Option Protocol) (keep : String → Bool)
    (name : String) (hk : keep name = true) :
    lookupStep (restrictProtocol cp keep) name = lookupStep cp name := by
  cases cp with
  | none => rfl
  | some entries =>
    simp only [lookupStep, restrictProtocol, Option.map_some, Option.bind_some,
      List.find?_filter]
    have hpred : (fun e : String × StepDecl => decide (keep e.1 = true ∧ (e.1 == name) = true)) =
        (fun e => e.1 == name) := by
      funext e
      by_cases h : e.1 = name
      · simp [h, hk]
      · simp [h]
    rw [hpred]

/-- Any key mask retaining endpoint types yields agreement of interpreted protocols. -/
theorem restrict_agrees {Role Msg : Type} (D : ProtoData Role String Msg)
    (cp : Option Protocol) (eval : Option StepDecl → (String → Prop) → Prop)
    (role : Role) (keep : String → Bool)
    (hk : ∀ t, typeEndpoint D t role → keep t = true) :
    AgreesOnRole (interpret D cp eval) (interpret D (restrictProtocol cp keep) eval) role := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => rfl, fun _ _ _ => Iff.rfl, ?_, ?_⟩
  · intro t pred ht
    change (∃ st, lookupStep (restrictProtocol cp keep) t = some st ∧ _) ↔ _
    rw [lookup_restrict cp keep t (hk t ht)]
    rfl
  · intro t present ht
    change eval (lookupStep (restrictProtocol cp keep) t) present ↔ _
    rw [lookup_restrict cp keep t (hk t ht)]
    rfl

/-- The paper's endpoint mask. Decidability is only needed to execute the mask;
    callers may supply it from finite role annotations. -/
def roleMask (sender : String → String) (recipients : String → List String)
    (role name : String) : Bool := sender name == role || (recipients name).contains role

/-- Concrete finite-recipient metadata discharges the key-mask premise. -/
theorem roleMask_keeps (sender : String → String) (recipients : String → List String)
    (role name : String) (h : sender name = role ∨ role ∈ recipients name) :
    roleMask sender recipients role name = true := by
  rcases h with h | h <;> simp [roleMask, h]

/-- Executable paper view over the dialect's concrete annotation table. -/
def roleView (ps : List Performative) (cp : Option Protocol) (role : String) : Option Protocol :=
  restrictProtocol cp (fun t => t == "begin" || annotationKeeps ps role t)

/-- The begin root survives the paper view even though it has no role annotation. -/
theorem roleView_begin (ps : List Performative) (cp : Option Protocol) (role : String) :
    lookupStep (roleView ps cp role) "begin" = lookupStep cp "begin" := by
  apply lookup_restrict
  simp

/-- Concrete bystander erasure also derives agreement at retained endpoint types. -/
theorem roleView_agrees {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) (cp : Option Protocol) (role : String)
    (eval : Option StepDecl → (String → Prop) → Prop) :
    AgreesOnRole (interpret (withAnnotations D ps) cp eval)
      (interpret (withAnnotations D ps) (roleView ps cp role) eval) (some role) := by
  apply restrict_agrees
  intro t ht
  by_cases hb : t = "begin"
  · simp [hb]
  · simp [(annotationKeeps_iff D ps role t hb).mpr ht]

/-- The paper's step-filtered raw-edge view satisfies the EPP transfer theorem. -/
theorem roleView_verification_agrees {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) (cp : Option Protocol) (role : String)
    (eval : Option StepDecl → (String → Prop) → Prop)
    (hloc : (interpret (withAnnotations D ps) cp eval).causalLocality) {C : Cfg Msg}
    (hcl : (interpret (withAnnotations D ps) cp eval).closedCfgD C)
    (hsafe : (interpret (withAnnotations D ps) cp eval).pSafeD C)
    {m : Msg} (hm : (interpret (withAnnotations D ps) cp eval).projectD C (some role) m) :
    let P := interpret (withAnnotations D ps) cp eval
    let Q := interpret (withAnnotations D ps) (roleView ps cp role) eval
    ¬ Q.isUnknownD (Q.projectD C (some role)) m ∧
    (Q.isValidD (Q.projectD C (some role)) m ↔ P.isValidD C m) ∧
    (Q.isViolationD (Q.projectD C (some role)) m ↔ P.isViolationD C m) :=
  local_protocol_verification_agrees (roleView_agrees D ps cp role eval) hloc hcl hsafe hm

/-- A store selected by the actual concrete Send/Recv map, with the shared begin root.
    This models complete payload delivery; derived envelopes need a separate store model. -/
def concreteStore {Msg : Type} (perf : Msg → String) (lp : LocalProtocol)
    (C : Cfg Msg) : Cfg Msg :=
  fun m => C m ∧ (perf m = "begin" ∨ (lp.steps (perf m)).isSome = true)

/-- Conformance identifies message endpoints with declared type endpoints. -/
theorem conformant_endpoint_iff {Role Msg : Type} (D : ProtoData Role String Msg)
    {m : Msg} (hc : D.conformantD m) (role : Role) :
    D.endpointD m role ↔ typeEndpoint D (D.perf m) role := by
  unfold ProtoData.endpointD typeEndpoint
  rw [hc.1]
  exact or_congr Iff.rfl (hc.2 role)

/-- Concrete step-map store selection equals EPP store projection. Annotation
    consistency and shared-root visibility are explicit, checkable/use-site premises. -/
theorem concreteStore_eq_project {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) (cp : Option Protocol) (role : String) (routes : Routes)
    (eval : Option StepDecl → (String → Prop) → Prop) (C : Cfg Msg)
    (hconsistent : AnnotationsConsistent ps)
    (hroot : typeEndpoint (withAnnotations D ps) "begin" (some role))
    (hconf : ∀ m, C m → (interpret (withAnnotations D ps) cp eval).conformantD m) :
    concreteStore D.perf (project ps cp role routes) C =
      (interpret (withAnnotations D ps) cp eval).projectD C (some role) := by
  funext m
  apply propext
  have hstep : ((project ps cp role routes).steps (D.perf m)).isSome =
      annotationKeeps ps role (D.perf m) := by
    rw [project_steps, specifiedStep_matches_annotation ps role (D.perf m) hconsistent]
  constructor
  · intro ⟨hm, hselected⟩
    refine ⟨hm, (conformant_endpoint_iff _ (hconf m hm) (some role)).mpr ?_⟩
    rcases hselected with hb | hs
    · simpa [typeEndpoint, interpret, withAnnotations, hb] using hroot
    · by_cases hb : D.perf m = "begin"
      · simpa [typeEndpoint, interpret, withAnnotations, hb] using hroot
      · exact (annotationKeeps_iff D ps role (D.perf m) hb).mp (hstep ▸ hs)
  · intro ⟨hm, he⟩
    refine ⟨hm, ?_⟩
    by_cases hb : D.perf m = "begin"
    · exact Or.inl hb
    · apply Or.inr
      rw [hstep]
      exact (annotationKeeps_iff D ps role (D.perf m) hb).mpr
        ((conformant_endpoint_iff _ (hconf m hm) (some role)).mp he)

/-- End-to-end concrete projection result: the step map selects the local store,
    the copied concrete clauses determine Q, and Q agrees with global verification.
    Unlike table preservation alone, this theorem depends on correct step selection. -/
theorem concrete_verification_agrees {Msg : Type} (D : ProtoData (Option String) String Msg)
    (ps : List Performative) (cp : Option Protocol) (role : String) (routes : Routes)
    (eval : Option StepDecl → (String → Prop) → Prop)
    (hconsistent : AnnotationsConsistent ps)
    (hroot : typeEndpoint (withAnnotations D ps) "begin" (some role))
    (hloc : (interpret (withAnnotations D ps) cp eval).causalLocality) {C : Cfg Msg}
    (hcl : (interpret (withAnnotations D ps) cp eval).closedCfgD C)
    (hsafe : (interpret (withAnnotations D ps) cp eval).pSafeD C)
    {m : Msg} (hm : concreteStore D.perf (project ps cp role routes) C m) :
    let P := interpret (withAnnotations D ps) cp eval
    let Q := interpret (withAnnotations D ps) (project ps cp role routes).protocol eval
    let L := concreteStore D.perf (project ps cp role routes) C
    ¬ Q.isUnknownD L m ∧ (Q.isValidD L m ↔ P.isValidD C m) ∧
      (Q.isViolationD L m ↔ P.isViolationD C m) := by
  have hconf : ∀ z, C z → (interpret (withAnnotations D ps) cp eval).conformantD z := by
    intro z hz
    exact (good_of_safe_closed ((interpret (withAnnotations D ps) cp eval).toProto hloc)
      hcl hsafe hz).1
  have hstore := concreteStore_eq_project D ps cp role routes eval C hconsistent hroot hconf
  rw [hstore] at hm ⊢
  exact projected_verification_agrees D ps cp role routes eval hloc hcl hsafe hm

/-- Causal locality ensures every actual referenced predecessor type is retained.
    Thus no bystander replacement can be exercised inside a retained clause. -/
theorem retained_predecessor {Role Msg : Type} (D : ProtoData Role String Msg)
    (cp : Option Protocol) (eval : Option StepDecl → (String → Prop) → Prop)
    (hloc : (interpret D cp eval).causalLocality)
    (keep : String → Bool) (role : Role)
    (hk : ∀ t, typeEndpoint D t role → keep t = true)
    {t pred : String} {st : StepDecl} (ht : typeEndpoint D t role)
    (hlookup : lookupStep cp t = some st)
    (hp : pred ∈ st.predecessors.flatMap NodeRef.names) : keep pred = true :=
  hk pred (hloc t pred role ⟨st, hlookup, hp⟩ ht)

/-! A nonempty rooted instance: begin is a thread root, not an annotated performative.
This checks that the agreement theorem can actually be instantiated on a causal run. -/
namespace RootedExample

/-- Two messages: false is the root, true is the annotated step p. -/
def observations : ProtoData (Option String) String Bool where
  perf := fun m => if m then "p" else "begin"
  sender := fun _ => some "r"
  recip := fun _ _ => False
  predRel := fun m p => m = true ∧ p = false
  psender := fun _ => some "r"
  precip := fun _ _ => False
  legalPred := fun _ _ => False
  clause := fun _ _ => False

/-- Only p is a declared performative; begin deliberately has no annotation. -/
def declarations : List Performative := [⟨"p", some ⟨"r", []⟩⟩]

/-- Finite begin-to-p protocol, including both edge directions. -/
def protocol : Option Protocol := some
  [("begin", ⟨"begin", [], [.single "p"]⟩),
   ("p", ⟨"p", [.single "begin"], []⟩)]

/-- A concrete Single/Any/All clause evaluator for this rooted example. -/
def eval (st : Option StepDecl) (present : String → Prop) : Prop :=
  match st with
  | none => True
  | some st => ∀ c, c ∈ st.predecessors → c.holds present

/-- The instantiated EPP model, with clauses and roles from the concrete tables. -/
def model := interpret (withAnnotations observations declarations) protocol eval

/-- The only legal edge is p citing begin. -/
theorem legal_iff (t pred : String) : model.legalPred t pred ↔ t = "p" ∧ pred = "begin" := by
  by_cases hb : t = "begin"
  · simp [model, interpret, lookupStep, protocol, hb, NodeRef.names]
  · by_cases hp : t = "p"
    · simp [model, interpret, lookupStep, protocol, hp, NodeRef.names]
    · simp [model, interpret, lookupStep, protocol, Ne.symm hb, Ne.symm hp, hp]

/-- Ordinary rooted protocols can satisfy the concrete locality premise. -/
theorem causalLocality : model.causalLocality := by
  intro t pred role hp ht
  obtain ⟨rfl, rfl⟩ := (legal_iff t pred).mp hp
  cases role <;>
    simp_all [model, interpret, withAnnotations, annotationAt, observations, declarations]

/-- The full two-message store is closed. -/
theorem closed : model.closedCfgD (fun _ => True) := fun _ _ _ _ => trivial

/-- The full store is safe for the concrete clause interpretation. -/
theorem safe : model.pSafeD (fun _ => True) := by
  intro m _ hv
  apply hv.2
  cases m <;>
    simp [ProtoData.goodD, ProtoData.conformantD, ProtoData.noSpuriousD,
      ProtoData.predTypesPresentD, model, interpret, withAnnotations, annotationAt,
      observations, declarations, protocol, lookupStep, eval, NodeRef.holds, NodeRef.names]
  intro r
  cases r <;> simp

/-- The paper's concrete projection really verifies this non-root message as Valid. -/
theorem projected_valid :
    (interpret (withAnnotations observations declarations)
      (roleView declarations protocol "r") eval).isValidD (fun _ => True) true := by
  have h := verdict_agree (roleView_agrees observations declarations protocol "r" eval)
    (m := true) (by left; rfl) (fun _ => True)
  exact h.2.1.mpr (valid_of_safe_closed (model.toProto causalLocality) closed safe trivial)

/-- Reject mode has no derived envelopes in this example. -/
def routes : Routes := ⟨false, [], [], false, none⟩

/-- A different role is absent from the concrete map and the filtered clause table. -/
theorem bystander_erased :
    (project declarations protocol "bystander" routes).steps "p" = none ∧
    lookupStep (roleView declarations protocol "bystander") "p" = none := by decide

/-- The composed theorem verifies the actual concrete-map-selected store. -/
theorem concrete_valid :
    (interpret (withAnnotations observations declarations)
      (project declarations protocol "r" routes).protocol eval).isValidD
      (concreteStore observations.perf (project declarations protocol "r" routes)
        (fun _ => True)) true := by
  have h := concrete_verification_agrees observations declarations protocol "r" routes eval
    ((checkAnnotationsConsistent_iff declarations).mp (by decide))
    (Or.inl rfl) causalLocality closed safe (m := true)
    (by exact ⟨trivial, Or.inr (by decide)⟩)
  exact h.2.1.mpr (valid_of_safe_closed (model.toProto causalLocality) closed safe trivial)

end RootedExample

end LeanCbcl.ConcreteProjection
