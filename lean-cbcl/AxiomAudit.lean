import LeanCbcl.Lattice.Result
import LeanCbcl.Lattice.Store
import LeanCbcl.Verify
import LeanCbcl.R5
import LeanCbcl.DCFLPreservation
import LeanCbcl.EPPCompletion
import LeanCbcl.ProtocolProjection
import LeanCbcl.Splice
import LeanCbcl.Bridge

/-!
# Axiom audit — NFR-511 / TEST-551 / OBS-512

`#print axioms` for each top-level theorem named in CON-510 through
CON-516 (SPEC-005 §Contracts), plus the SPEC-014 EPP-correspondence
family (`EPP.lean`, `EPPCompletion.lean`, `Projectability.lean`,
`ProtocolProjection.lean`, `Splice.lean`, `Bridge.lean`), whose axiom
claim in `proofs/epp-correspondence/proof.tex` §Notes ("propext,
Classical.choice, Quot.sound only") is enforced here. The companion shell script
`scripts/check-axioms.sh` runs this file via `lake env lean`, parses the
emitted `'<thm>' depends on axioms: [...]` lines, and fails CI if any
axiom outside the allowlist appears.

Allowlist (kept in sync with the shell script and with NFR-511 +
ADR-515 in `specs/SPEC-005-lean-mechanisation.md`):

* `Classical.choice`, `propext`, `Quot.sound` — the standard Lean kernel
  axioms permitted by NFR-511 clause 1.
* `CBCL.ContentHash`, `CBCL.contentHash`, `CBCL.contentHash_injective` —
  the cryptographic-hash carrier and the injectivity assumption justified
  by ADR-515. Located in `LeanCbcl/Lattice/Store.lean`.
* `CBCL.Message.causedBy` — opaque accessor for the `:caused-by` field of
  the abstract `Message` type, also justified by ADR-515. Located in
  `LeanCbcl/Verify.lean`. The Rust implementation pulls the field from a
  parsed S-expression; the Lean model treats it as an abstract accessor
  since `Message` itself is abstract on the verify side.

NFR-511 clause 2 admits *only* the four project axioms above. Any further
project axiom requires an amendment to ADR-515, not merely an allowlist
edit in the script and this header.

Historical note: an earlier draft also declared
`CBCL.ContentHash.instNonempty : Nonempty ContentHash` as a bookkeeping
axiom anticipating `Option ContentHash`-returning helpers. Empirically
none of CON-510..516 transitively depended on it (the `lookup` proofs
go via `Classical.choice` directly, not via `Option.choice`/`Inhabited`
defaults), so the axiom was removed to keep the allowlist minimal. If
the deferred `LookupSpec` mechanisation needs a `Nonempty ContentHash`
instance it should be reintroduced together with a `#print axioms` line
that exercises it.

If a future theorem joins CON-510..516, add a `#print axioms` line for it
below — the shell script discovers theorems from this file's output, so
editing only this file is enough to extend the audit.
-/

-- CON-510 — Three-valued result bisemilattice (Lattice/Result.lean).
#print axioms CBCL.VerificationResult.result_meet_table
#print axioms CBCL.VerificationResult.result_join_table

-- CON-511 — Message store G-Set (Lattice/Store.lean).
#print axioms CBCL.MessageStore.union_assoc
#print axioms CBCL.MessageStore.union_comm
#print axioms CBCL.MessageStore.union_idem
#print axioms CBCL.MessageStore.append_eq_union_singleton
#print axioms CBCL.MessageStore.lookup_monotone

-- CON-512 — `verify` monotonicity (Verify.lean).
#print axioms CBCL.verify_monotone

-- CON-513 — `verify` fan-in lattice-homomorphism (Verify.lean).
#print axioms CBCL.verify_all_is_meet

-- CON-514 — `verify` eventual consistency (Verify.lean).
#print axioms CBCL.verify_eventually_consistent

-- CON-515 — R5 sub-check soundness + completeness (R5.lean).
#print axioms CBCL.check_acyclicity_iff_no_cycle
#print axioms CBCL.check_reachability_iff_all_reachable
#print axioms CBCL.check_performative_definedness_iff_all_defined
#print axioms CBCL.check_step_uniqueness_iff_no_duplicates

-- CON-516 — DCFL preservation (DCFLPreservation.lean).
#print axioms CBCL.DCFLPreservation.dcfl_preserved_under_protocol
#print axioms CBCL.DCFLPreservation.dcfl_preserved_under_shape

-- EPP correspondence, safety + completion levels (EPP.lean, EPPCompletion.lean).
-- `proof.tex` §Notes claims "no sorry; axioms propext, Classical.choice, Quot.sound"
-- for these; this audit enforces that claim in CI (SPEC-014).
#print axioms LeanCbcl.EPP.epp_correspondence
#print axioms LeanCbcl.EPP.soundness_safety
#print axioms LeanCbcl.EPP.completeness_safety
#print axioms LeanCbcl.EPP.reconcile_global
#print axioms LeanCbcl.EPP.valid_stable
#print axioms LeanCbcl.EPP.violation_stable
#print axioms LeanCbcl.EPP.epp_correspondence_complete

-- Theorem 1: projectability ≡ local verifiability (Projectability.lean).
#print axioms LeanCbcl.Projectability.projectability_iff_local_verifiability
#print axioms LeanCbcl.Projectability.causal_locality_necessary

-- Protocol-projection agreement interface (ProtocolProjection.lean).
#print axioms LeanCbcl.ProtoProjection.verdict_agree
#print axioms LeanCbcl.ProtoProjection.local_protocol_verification_agrees

-- Splicing necessity / type-opacity / openings (Splice.lean).
#print axioms LeanCbcl.Splice.type_opacity_indistinguishability
#print axioms LeanCbcl.Splice.resolution_requires_preimage
#print axioms LeanCbcl.Splice.spliced_pred_permanently_unknown
#print axioms LeanCbcl.Splice.weakest_sound_condition
#print axioms LeanCbcl.Splice.openings_suffice
#print axioms LeanCbcl.Splice.openings_suffice_concrete

-- Temporal bridge (Bridge.lean).
#print axioms LeanCbcl.Bridge.bridge_stability
#print axioms LeanCbcl.Bridge.bridge_compatibility
#print axioms LeanCbcl.Bridge.temporal_bridge
