---
id: SPEC-038
title: Optional dialect-thread proof export
version: 0.1.0
status: draft
implementation-status: implementing
last-updated: 2026-11-07
owner: CBCL maintainer
review-status: pending independent review
---

# SPEC-038: Optional dialect-thread proof export

## Orientation

Intent: a holder of a private dialect thread may explicitly export a proof of a
chosen state/result to a receiver who does not receive the discussion. Most
threads never prove. Signed votes may lead to a public outcome; participant
identities may also be public, but disclosure is explicit and bounded.

Metaphor: a sealed meeting record with a separately addressed result certificate.
The certificate states which meeting, rules and closing record it covers; it
cannot establish that nobody has another message.

```text
ordinary thread runtime (no prover dependency or proof work)
       | explicit snapshot/export request
       v
canonical/authenticated covered set -> pinned dialect/program -> optional prover
                                                                   |
                                              statement + proof package
                                                                   v
receiver-owned expectation + trusted profile -----------------> verifier
```

Decisions: [[SPEC-038-optional-thread-proof-export#ADR-3800]] backend-independent
contract with Dory ZK first; [[SPEC-038-optional-thread-proof-export#ADR-3801]]
compose native recognition/authentication/admission/fold rather than inventing a
parallel vote kernel.

Load-bearing: [[SPEC-038-optional-thread-proof-export#REQ-3800]] opt-in isolation;
[[SPEC-038-optional-thread-proof-export#REQ-3801]] precise statement;
[[SPEC-038-optional-thread-proof-export#REQ-3802]] disclosure and completeness;
[[SPEC-038-optional-thread-proof-export#REQ-3803]] native correspondence;
[[SPEC-038-optional-thread-proof-export#REQ-3804]] receiver trust.

Controls:
- No default proof work, dependency, remote transfer or hidden fallback:
  [[SPEC-038-optional-thread-proof-export#REQ-3800]].
- No selected-subset completeness, global freshness, human identity or undisclosed
  state claims: [[SPEC-038-optional-thread-proof-export#REQ-3802]].
- Reject unsupported source/semantics/authentication; no experimental/native alias:
  [[SPEC-038-optional-thread-proof-export#REQ-3803]].
- Reject unknown modes, pins, code, setup and grammars; never learn trust from the
  package: [[SPEC-038-optional-thread-proof-export#REQ-3804]],
  [[SPEC-038-optional-thread-proof-export#CON-3800]].
- Browser release requires executed trace/prove/export/verify and measured memory,
  cancellation and failure outcomes:
  [[SPEC-038-optional-thread-proof-export#NFR-3800]].
- No implemented status without independent acceptance; policy holds are explicit:
  [[SPEC-038-optional-thread-proof-export#REQ-3805]],
  [[SPEC-038-optional-thread-proof-export#Open-policy]].

Open: CBCL maintainer owns profile limits, identity/eligibility authority, closure
policy, public proposal context, disclosure policy, browser support budgets and
pin distribution. These are tasks, not a request to reconsider the approved
backend direction. See [[SPEC-038-optional-thread-proof-export#Open-policy]].

Reading paths: reviewer → [[SPEC-038-optional-thread-proof-export#Evidence-boundary]]
→ decisions → open policy → [[SPEC-038-optional-thread-proof-export#TEST-3805]];
implementer → contracts → core tests → requirements →
[IMPL-038](../plans/IMPL-038-thread-proof-export.spl); stakeholder → intent → disclosure → open policy.

## Scope and failure model

Tier 1: authentication, private witness disclosure and verifier trust are security
boundaries. This document specifies implementation targets, not completed
production functionality. Independent cross-model adversarial review and human
cryptographic/domain review remain acceptance work. A standalone export library
and optional adapters are in scope; live protocol consensus, resource authority,
remote proving and default runtime proving are outside this version.

FM-3800: treating a host's tally as proven permits forged ballots, omitted votes,
or a different proposal/program to inherit an apparently valid certificate.
FM-3801: packaging keys, state hashes, metadata or debug data without an explicit
projection leaks private discussion or makes low-entropy ballots guessable.
FM-3802: accepting a package's own program/setup/expectation substitutes attacker
trust for receiver intent. FM-3803: conflating compilation or fixed-vote experiment
success with general native/browser correctness produces unsupported API claims.

## Evidence boundary

[Native experiment results](../experiments/private-vote-export/RESULTS.md) records real native Dory ZK proofs
for four and eight messages; WASM prover/tracer compilation alone was recorded.
The experimental consumer authenticates its own signed envelope, not native
[[SPEC-015-evidence-widening-v2]] R4 v2 attestations. Its fixed voting source is not a
general arbitrary-dialect implementation. There is no all-16-head or full-kernel
correspondence theorem here, nor a backend comparison winner claim.

The measured native consumer remains source-frozen to preserve image provenance.
Its message/participant/source/input and padded-row caps are experimental profile
choices, not protocol-wide limits. Production integration receives a new program
and profile identity; it does not silently replace that experiment's image.

An actual browser prototype under the same experiment is independent of the
future production API. Its [runtime results](../experiments/private-vote-export/browser/RESULTS.md)
record executed verification, tracing, cancellation and proving outcomes.
The fixed-profile browser proof passed fresh browser and independent native
verification without history after two upstream 32-bit arithmetic fixes. Proving
took 860.6 seconds on the measured desktop, with 3.93 GiB WASM capacity; this
is feasibility evidence for that fixture, not a supported-device policy.
A fixed-profile browser result does not imply production acceptance.

## Delivery status matrix

| Slice | Evidence/status | Does not establish |
|---|---|---|
| Phase 0 native experiment | Real Dory ZK four/eight-message proofs in historical results | Native R4 v2, arbitrary dialects or production API |
| Phase 0 browser prototype | Fixed-profile browser proof/export/fresh-browser/native verification passed; cancellation/resource recovery measured | Production v1 requirements, even if fixed-profile browser proving succeeds |
| Profile/contract | Draft implementation target here | Ratified production manifest or limits |
| Native R4/general dialect | Planned with explicit support matrix | All native heads/full-kernel theorem |
| Optional CLI/WASM API | Planned after contract/integration and applicable browser gates | Default runtime proof dependency |
| Reviewer acceptance | Prototype source review and Orientation exercise recorded; production review/policy dispositions pending | Implemented status today |

## Requirements

### REQ-3800

The ordinary runtime MUST have no proof dependency or proof work on its default
build/execution path. Explicit export selects a snapshot and profile; private
witness preparation, tracing, setup loading, proving and verification occur only
in the optional export component. Turning export off or cancelling it leaves the
ordinary thread operational. Failures MUST be typed failures, with no downgrade
to clear proofs, host-only tallies, another backend, or a remote prover. No private
material is transmitted by this v1 component. Export controls are available per
request; deployments may disable new exports without redeploying or invalidating
previous packages. Unsupported commands/features report unavailable.

Trace: FM-3801, FM-3803; [[SPEC-038-optional-thread-proof-export#TEST-3800]].

### REQ-3801

A proof MUST assert existence of a witness satisfying exactly the relation in
[[SPEC-038-optional-thread-proof-export#CON-3801]] for the public statement in
[[SPEC-038-optional-thread-proof-export#CON-3800]]. The statement binds thread,
public proposal/context, dialect source identity, native semantics/authentication
versions, complete covered-set commitment, closure policy/evidence commitment,
roster, eligibility, actual-voter commitments or disclosures, disclosure mode,
requested projection and outcome, plus profile/program/setup identities. None is
an unauthenticated host annotation. An outcome-only export proves the named
projection; a state export proves the named canonical state projection and MUST
NOT imply that unrevealed state was disclosed or independently available.

Trace: FM-3800; [[SPEC-038-optional-thread-proof-export#TEST-3801]].

### REQ-3802

The exporter MUST explicitly select the public fields and show their values before
export. Public outcome does not imply consent to public discussion, ballots or
voter participation. Identities MAY be public labels plus keys or credentials;
without an independently trusted credential policy they establish only key control,
not a person. In this v1, discussion, ballots, signatures and salt remain witness
material. Private state/ballot hashes MUST NOT be exported unsalted.

Roster is the set of participants/key bindings recognised for this thread;
eligibility is the authorised voting subset under the pinned policy; actual
voters are eligible identities with an effective ballot under native semantics.
These sets MUST NOT be conflated. An eligible abstainer is not an actual voter;
a public roster does not disclose who voted. Each set is either explicitly public
or represented by a domain-separated salted commitment, as the disclosure tag
specifies. Hidden lists and public counts must be proven mutually consistent. Public counts,
small groups and unanimous outcomes can logically reveal participation or choices;
zero knowledge does not conceal information implied by the selected public result.

Closure certifies exactly the canonical covered set and its causal dependencies,
including relevant discussion, replacements and concurrent ballots, not a
prover-chosen ballot subset. V1 requires authenticated unanimous closure by the
roster over this scope. Alternative quorum/deadline policies require a new profile
and maintainer resolution. A missing signer, unresolved ancestor or omitted
record relative to that certified set fails. Closure does not establish global
freshness, absence of undisclosed messages, fairness, private data availability or
permission to act on resources. These limitations accompany successful verification.

Trace: FM-3800, FM-3801; [[SPEC-038-optional-thread-proof-export#TEST-3801]],
[[SPEC-038-optional-thread-proof-export#TEST-3802]].

### REQ-3803

Production v1 MUST authenticate canonical native message bytes, content addresses,
signer/from binding and thread/dialect binding with pinned native R4 v2 rules,
then install the pinned dialect, admit from empty to a complete accepted set and
fold it using pinned native semantics. Host prechecks are useful but MUST NOT
substitute for authentication/semantic constraints inside the proved computation.
Canonicalisation, duplicate/conflict treatment, HLC/replacement order and rejected
input handling MUST match the native APIs; no reserialised alternate representation
may inherit a signature on different bytes. Unsupported constructs fail closed.

General dialect integration MUST accept source through the native recogniser and
installer, bind exact source bytes and installed identity, and expose a versioned
projection supported by that dialect. Each shipped profile declares its supported
constructs/rule heads and tests correspondence. It MUST NOT advertise arbitrary
source support while comparing against the experiment's fixed vote source, or
claim all native heads from vote fixtures. An adapter/restricted profile is allowed
only with a distinct identity, explicit support boundary and rejection tests.

Trace: FM-3800, FM-3803; [[SPEC-038-optional-thread-proof-export#TEST-3803]].

### REQ-3804

The verifier MUST take receiver-owned expectations and a locally trusted profile
registry separately from the untrusted package. It checks the scope and disclosure policy
against those expectations, then cryptographic validity under the pinned ZK mode,
program and setup. Unknown or mismatched grammar, backend/mode, code/source hash,
semantics/authentication version, setup or projection is an error, not discovery
or fallback. Package-supplied preprocessing is untrusted until its digest and
provenance match the independently provisioned profile. Verification does not
require private history. A caller MUST explicitly identify what it expects; a
package cannot populate that expectation for the caller.

Trace: FM-3802; [[SPEC-038-optional-thread-proof-export#TEST-3804]].

### REQ-3805

Implementation proceeds through profile/contract, browser feasibility, native
R4/general dialect integration, optional CLI/WASM adapters, then reviewer acceptance.
Experimental success closes only its own evidence gate. The authoring session
MUST NOT mark this spec implemented. Independent review must disposition findings,
exercise the Orientation comprehension gate, inspect core/mutation and browser
evidence, and record unsupported scope and remaining policy decisions. Production
release for a profile is held until the maintainer resolves its applicable policy
choices and accepts cryptographic trust assumptions; the approved Jolt/Dory
direction needs no new permission.

Trace: FM-3803; [[SPEC-038-optional-thread-proof-export#TEST-3805]].

### NFR-3800

Browser feasibility MUST execute this workload in an actual named browser/device:
witness input → VM trace → ZK prove → export package → fresh receiver verification
without history. Record browser/OS/device, isolation/worker settings, exact
source/image/dependency/setup pins, input size, timings by stage, proof/bundle
sizes, memory measurement method and observed peak or allocation ceiling.
Execute cancellation during trace and prove, worker termination/cleanup, invalid
input, resource exhaustion and subsequent successful use. No successful package
may appear after cancellation. If a stage is not interruptible, worker termination
is the cancellation mechanism and its effects are measured. Browser entropy and
private-buffer/log/cache handling are inspected. Record failure as failure, not
native or Node substitution. A compile/link/Node-verify result cannot pass this
gate. Device support and numeric budgets remain maintainer-owned profile choices;
no unmeasured browser performance guarantee is made.

Trace: FM-3801, FM-3803; [[SPEC-038-optional-thread-proof-export#TEST-3806]].

## Contracts

### CON-3800

Closed v1 transport grammar. `enc` is deterministic CBOR under RFC 8949 core
deterministic encoding, using only definite arrays, unsigned shortest-form
integers, fixed literal text and byte strings. No maps, tags, floats, negative
integers, indefinite lengths or trailing bytes. Tuple position and arity are exact.
`b32` means a byte string of exactly 32 bytes. `bytes` is a definite byte string
bounded by the trusted profile. `u` is an unsigned integer bounded by that profile.
The following algebraic grammar is normative; the quoted tokens are literal text.

```text
Package = ["cbcl-thread-proof", 1, Statement, Proof]
Proof = ["jolt-dory-zk", 1, bytes]
Statement = ["cbcl-thread-statement", 1, ProfileId, ThreadId,
             Proposal, Dialect, Semantics, Authentication,
             Covered, Closure, Participants, Projection, Outcome]
ProfileId = b32
ThreadId = bytes
Proposal = ["public-proposal-v1", bytes, bytes, b32]
Dialect = ["native-source-v1", b32, bytes]
Semantics = ["native-semantics-v1", b32]
Authentication = ["native-r4-v2", b32]
Covered = ["complete-from-empty-v1", b32, u]
Closure = ["unanimous-roster-v1", b32]
Participants = [SetView, SetView, SetView]
SetView = ["public", [Identity*]] | ["private", b32, u]
Identity = [bytes, bytes, bytes]
Projection = ["dialect-projection-v1", bytes, b32]
Outcome = bytes
ExpectedContext = ["cbcl-thread-context", 1, ProfileId, ThreadId, Proposal,
                   Dialect, Semantics, Authentication, Covered, Closure,
                   SetView, SetView, Disclosure, Projection]
Disclosure = ["views-v1", ViewMode, ViewMode, ViewMode]
ViewMode = "public" | "private"
```

Proposal contains canonical public proposal bytes, public context bytes and their
joint domain-separated digest. Dialect contains exact source digest and native
installed dialect identity. Semantics and Authentication contain manifest hashes
for the corresponding rules. Participants positions mean roster, eligibility,
actual voters; Identity means label bytes, canonical signing key bytes, credential
bytes (empty means no credential). Identity lists are sorted by canonical key
bytes, unique, and keys/credentials recognised under the profile's closed schemas.
Projection contains projection identifier and schema digest; Outcome is its
canonical encoding. Duplicate keys or identities, invalid UTF-8 where the nested
schema requires text, or noncanonical embedded values fail recognition. ThreadId,
source, native attestation, identity, outcome and proof bytes are recognised by
the pinned native/profile grammars, never parsed by ad-hoc string extraction.

ExpectedContext carries trusted roster and eligibility views; Disclosure fixes the
allowed visibility of roster, eligibility and actual voters. It does not carry an
expected tally, state/result bytes or actual-voter list. The package supplies those
claims; the proof establishes them. Expected context comes from the receiver or
an independently trusted scope/closure publication, never package auto-fill.

The single shared package recogniser MUST recognise the complete bounded object
before cryptographic operations, setup loading or VM execution. Nested schema
recognition is part of that boundary. Before allocation it enforces local
transport ceilings; before execution it enforces trusted profile ceilings. The
profile/contract task supplies exact numeric limits, canonical vectors and
native/proof schema versions; missing limits or schemas make a profile unusable.
There is no extension/unknown-field bucket. Any extension changes the version.
Future backends use a newly registered closed Proof variant; v1 has no clear mode.

The relation is backend-independent even though the first wire variant names
Dory. A trusted profile manifest binds grammar versions/limits, disclosure modes,
projection schemas, source policy, native authentication/semantics manifests,
compiler/toolchain/dependency/source/image hashes, backend protocol/mode and
parameters, setup/preprocessing digest and provenance, public-IO encoding,
commitment/hash schemes and trust assumptions. ProfileId is its domain-separated
SHA-256 digest over canonical manifest bytes. Receiver registry installation is
out of band, with maintainer-authenticated provenance and an explicit local
allowlist; packages cannot install profiles or fetch/execute code. Manifest
encoding/schema and exact values must be published and pinned by the contract
task before a production profile can be recognised. No placeholder hash passes.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3801]],
[[SPEC-038-optional-thread-proof-export#REQ-3804]],
[[SPEC-038-optional-thread-proof-export#TEST-3804]].

### CON-3801

Let S be Statement. A private witness W contains exact dialect source, canonical
native messages and R4 v2 attestations, identity/eligibility credentials, roster,
ballots, a fresh cryptographic 32-byte secret salt, and closure signatures. The
relation R(S,W) holds iff:

1. All values recognise under the trusted profile grammars. Source digest,
   installed dialect identity, program and native versions equal S and the profile.
2. Public proposal/context bytes hash to S.Proposal's digest. The dialect's
   declared proposal object and each effective ballot are bound to that same
   proposal/thread/context by native authenticated content; matching a host label
   alone is insufficient. A profile without a verifiable proposal binding fails.
3. Every covered record has valid native authentication and bound canonical
   content identity, signer, thread and dialect. Identity credentials and eligible
   subset meet the pinned policy; effective voters are derived, never supplied as
   authoritative host input. Canonical duplicate identities/records are rejected.
4. Admit the exact covered records from empty under the installed native dialect;
   resolve every required dependency within this scope. The accepted set equals
   the covered set. Fold that complete set and compute the declared projection,
   eligibility and effective voters using native semantics.
5. Define Commit(label,x) = SHA256(enc(["cbcl-thread-commit",1,label,
   ProfileId,ThreadId,proposalDigest,sourceDigest,salt,x])). Covered commitment
   commits to the sorted list of canonical record bytes plus authentication bytes
   (ordered by canonical content identity); S includes its exact count. SetView
   commitments use distinct labels and canonical sorted identity lists; Closure's
   commitment binds the closure certificate bytes. Salt is fresh per export and
   stays private. No unsalted private-state digest is substituted.
6. Every roster key signs the domain-separated canonical closure payload binding
   ProfileId, thread, proposal/context digest, source and semantics/authentication
   identities, covered commitment/count, roster and eligibility views, disclosure
   selection and projection. Signature bytes remain private. This freezes exactly
   that certified set, not an unverifiable global cutoff. The closure certificate
   commitment is computed after signatures; the signed payload excludes that
   commitment to avoid circularity. It need not bind proof randomness/setup anew:
   ProfileId already binds program/setup. Any changed view requires new closure.
7. S's public views/counts match W; S.Outcome equals the exact canonical native
   projection result. A public tally includes every effective eligible ballot;
   revisions, ties, concurrent votes and abstentions use the dialect's declared
   semantics. Their meaning is not hardcoded by this transport contract.

Prove(Profile,S,W) returns a package or a typed error. Verify(Registry,
ExpectedContext,Package) first recognises all inputs, resolves only an allowlisted
profile, compares every context field and disclosure mode with the receiver's canonical
ExpectedContext, then verifies the ZK proof's bound public IO including the claimed
outcome and actual voters. Success returns a VerifiedResult containing that statement,
profile identity and the scope/trust limitations; failures return no verified
outcome. Receivers may obtain the expected commitment from an independently
trusted signed closure/publication; it remains an explicit trust dependency,
never an automatic copy from the package. Scope matching is intentionally strict;
an unknown expected context fails closed.
The experiment's full expected Journal fixtures are test oracles, not a production
requirement to trust the outcome before verifying it.

Purity boundary: native recognise/install/authenticate/admit/fold/projection and
statement checking are deterministic computation; entropy, worker scheduling,
files, user disclosure confirmation and trust-registry provisioning are effects
outside it. The proved computation checks the witness relation regardless of host
precheck results. It performs no network/filesystem access.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3801]],
[[SPEC-038-optional-thread-proof-export#REQ-3802]],
[[SPEC-038-optional-thread-proof-export#REQ-3803]].

## Decisions

### ADR-3800

Accepted user direction: pursue Jolt/Dory with ZK as first optional backend. The
statement, expected-context API and scope semantics are independent of it;
program/setup/mode trust remains backend-specific in profiles. Ordinary runtime
stays independent. Native evidence justifies this implementation direction,
not a comparative backend winner or browser feasibility conclusion. No renewed
backend-selection permission is required.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3800]],
[[SPEC-038-optional-thread-proof-export#REQ-3804]].

### ADR-3801

Composition-first: reuse existing native recognisers, R4 verifier, installer,
admission and fold inside the proved consumer; reuse pinned Dory cryptography.
Add only the versioned export relation, recogniser, profile registry and optional
adapters required above. Do not extend the source-frozen experiment in place or
create a second hand-coded vote interpreter. Existing bounded Halo2/cached
checkpoint contracts are not redefined by this export target.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3803]].

## Acceptance

These are target tests, not assertions of executed production evidence. Core is
small fixture-based work; browser measurements and broad correspondence are depth
with named gates, not prerequisites to writing the core. Every core negative must
reach the intended check after otherwise-valid input. Compiler/import failures
are not red-gate or mutation evidence.

### TEST-3800

Core, owner export implementer. Build/dependency inspection shows default core,
CLI and WASM paths have no proof dependency; an ordinary thread executes with no
trace/setup/prove call. Explicit optional export runs; disabled export reports
unavailable. Cancellation/failure leaves ordinary runtime usable. Mutate the
opt-in guard: the default-path spy must fail.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3800]].

### TEST-3801

Core, owner relation implementer. A synthetic private discussion with signed
mixed/revised votes and an eligible abstainer exports the hand-asserted native
outcome and verifies without history. Public proposal and context are visible;
private discussion, votes and salt are absent from package/logs. Public roster
plus private voters does not expose voter labels. Mutating proposal, projection,
outcome, salt commitment or one public field while preserving grammar fails;
coherent output tampering must reach crypto verification and fail there.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3801]],
[[SPEC-038-optional-thread-proof-export#REQ-3802]].

### TEST-3802

Core, owner relation implementer. Exercise ineligible signer, abstainer,
replacement/concurrent ballot, missing closure signer, missing certified message
and unresolved ancestor. A changed subset with old closure fails. Removing native
signature verification and removing closure unanimity are separate source mutants;
otherwise-valid negative witnesses must reach and kill each mutant inside the
proved consumer with host prechecks bypassed. Fresh salt changes commitments but
not outcome. Public roster, eligibility and voters are asserted separately.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3802]],
[[SPEC-038-optional-thread-proof-export#REQ-3803]].

### TEST-3803

Core, owner native integration implementer. Native R4 v2 golden valid input and
wrong-signature/from/thread/canonical-bytes negatives execute inside the guest.
At least a vote dialect and a structurally different supported state dialect
match native admission/fold/projection; unsupported declarations reject. Changing
source, semantics, auth manifest or image changes profile identity and rejects
old expectations. An experimental-envelope fixture fails native-profile input.
Depth, same owner: publish support matrix and correspondence fixtures for every
advertised construct/head before expanding the supported profile. No universal
full-kernel theorem is inferred from these cases.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3803]].

### TEST-3804

Core, owner verifier implementer. Honest package verifies against independently
provisioned registry/expectation without private history. Reject wrong scope,
mode (including clear), program/source/setup/profile pins, duplicate/extra tuple
members, truncation, noncanonical CBOR, trailing bytes, oversized input and
unknown versions. Package-selected expected context/profile cannot auto-trust.
Disable expected-context equality as a mutant: a valid proof for another
scope must make the test fail. Disable setup pin check separately with an
otherwise valid substituted setup path and demonstrate the intended assertion.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3804]],
[[SPEC-038-optional-thread-proof-export#CON-3800]].

### TEST-3805

Core, owner independent reviewer (not producing session), with CBCL maintainer
for policy ratification. Review spec/plan and deliverable from fresh context;
record Orientation-only comprehension, findings/dispositions, source/proof pins,
core baselines, meaningful red gates and killed mutations. Review optional API
fixtures for explicit expectations, no witness-return/log leaks, bounded errors
and enable/disable behaviour. No implemented status or release from compile-only,
fixed-vote, unfinished browser or unsupported-native evidence. Human crypto/domain
review accepts applicable profile assumptions and policy resolutions. No such
review is claimed by this authoring session.

Trace: [[SPEC-038-optional-thread-proof-export#REQ-3805]],
[[SPEC-038-optional-thread-proof-export#REQ-3800]].

### TEST-3806

Depth, owner browser feasibility implementer. Execute the full NFR browser
pipeline with an exported artifact reverified by a fresh receiver. Publish actual
memory/cancel/resource-failure results and support recommendation tied to exact
pins. Native/Node fallback and compilation-only evidence fail the gate. A failing
browser result is useful recorded evidence but cannot complete browser feasibility
for the optional WASM prover API. Budget/support ratification is a separate
maintainer task and may restrict devices or defer that API explicitly.

Trace: [[SPEC-038-optional-thread-proof-export#NFR-3800]].

## Open-policy

Named accountable owner: **CBCL maintainer** for every row. Implementers propose
values; independent reviewer checks their presence and consistency. These choices
block applicable production profiles, not documentation or the authorised backend
work. No fabricated personal owner is assigned.

| Choice | Required resolution/evidence | Gate |
|---|---|---|
| Public proposal/context | Canonical schema and native binding to proposal object/ballots, with changed-context rejection vector | profile/contract before native integration |
| Identity and eligibility | Label/key-only versus credential authority, rotation/revocation epoch, eligible-subset source and required public identities | profile/contract; no human-identity claim before ratification |
| Closure | Ratify unanimous-roster v1, membership epoch, handling equivocation/missing signer; any quorum/deadline needs distinct profile | profile release |
| Disclosure | Allowed roster/eligibility/voter views and outcome projections, publication confirmation and metadata retention | profile release |
| Limits and browser support | Concrete input/proof/setup/trace ceilings, supported browsers/devices, latency/memory budgets and cancel expectations from actual measurements | optional WASM prover API |
| Trust provisioning | Maintainer-authenticated manifest distribution/update/revocation policy, setup origin and upstream ZK review assumptions | receiver/profile release |
| General dialect surface | Supported construct/head matrix and projection registration; unsupported rejection policy | native integration acceptance |

## Amendment Channels

Amendable by: CBCL maintainer through a recorded spec revision or explicit user
direction reflected in this document. This session records the already-approved
Jolt/Dory direction. Independent reviewers propose corrections; their findings do
not manufacture completion evidence. Experimental logs and package metadata are
evidence, not authority to change the contract.

Hard stops: [[SPEC-038-optional-thread-proof-export#REQ-3800]] opt-in/no fallback;
[[SPEC-038-optional-thread-proof-export#REQ-3802]] explicit disclosure/closure;
[[SPEC-038-optional-thread-proof-export#REQ-3803]] native scope honesty;
[[SPEC-038-optional-thread-proof-export#REQ-3804]] fail-closed trust;
[[SPEC-038-optional-thread-proof-export#REQ-3805]] independent acceptance;
[[SPEC-038-optional-thread-proof-export#NFR-3800]] measured browser gate. Any change
to these obligations requires a new explicit spec revision before implementation.

## Validation record

The implementation plan is imported into Elephant theory `spec-038`; its gates
remain evidence-dependent. Browser runtime measurements and independent source
review are recorded with the prototype results. An independent Orientation-only
comprehension exercise correctly predicted opt-in isolation, rejection of missing
required closure, learning an unknown outcome from trusted context, and rejection
of experimental/native relabelling. It does not constitute production acceptance.

Numeric production policy values and the closed manifest/nested schemas remain
profile-task deliverables. Native R4/general-dialect integration and production
API acceptance remain pending. Unresolved values fail closed rather than becoming
defaults.
