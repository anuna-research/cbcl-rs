---
id: SPEC-035
title: Cached certificates for state checkpoints
version: 0.5.0
status: implemented
last-updated: 2026-11-07
---

# Cached certificates for state checkpoints

| Field | Value |
|---|---|
| ID | SPEC-035 |
| Title | Cached certificates for state checkpoints |
| Owner | CBCL state-kernel maintainer |
| Scope | Object state bootstrap, verified continuation and checkpoint publication |
| Review tier | Tier 1; local design review, with independent security and human domain review required before production enablement |
| Status | Profile v2 all-head implementation and typed Lean continuation locally verified; native-port/refinement boundaries remain explicit; production enablement remains opt-in |

## Orientation

**Intent.** Opening an object should fetch its current state and recent changes,
rather than download and fold its entire message history. A
[[SPEC-035-cached-state-checkpoints#Checkpoint certificate|checkpoint certificate]]
is a reusable bundle of native signed `endorse` acts in the built-in
[[SPEC-035-cached-state-checkpoints#CON-3504|checkpoint companion dialect]].
It binds one accepted causal cut, its state summary and its verification context.
Any member can propose a cut;
each endorser independently checks that exact cut before signing. A client can
open the cached certificate without contacting those endorsers again or replaying
the companion thread. The same dialect serves different target object dialects;
their profiles define the claims' state semantics. Native acceptance authenticates
an endorsement's assertion, not its truth. The local profile verifier authorizes
honest endorsement signing.

Profile v2 covers all native state-kernel rule heads, including projected events,
ordered derived fields, progress with verified protocol position, and resource
facts that preserve the native authority checks. Its exact inventory and obligations
are in [[SPEC-035-cached-state-checkpoints#REQ-3516]] through
[[SPEC-035-cached-state-checkpoints#REQ-3521]]. The seven-rule v1 proof remains
valid for its pinned historical model; it does not establish v2 correctness.
A projected event retains identity, signer and selected value rather than its full
message. Event output and retained projections can grow together: checkpointing
promises no constant-space bound for a growing output. Domains and global `All`
queries are separate language features, not extra rule heads, and can remain gated
where they are unnecessary to this all-head profile.

```text
target: authenticate/admit messages -> maintain summaries and coverage
companion dialect: propose -> profile-authorized endorse -> publish location
                                                      |
                                         immutable cached certificate
                                                      |
client: pinned target + companion -> fetch/verify bundle -> admit target tail
                                                      -> preserve local floor
                                                      -> atomically install
```

An [[SPEC-035-cached-state-checkpoints#Accepted cut|accepted cut]] is downward
closed under the object's causal predecessor relation. Its frontier names its
maximal messages. Its coverage commitment authenticates membership and absence;
it does not itself prove that the summary was computed correctly. Eligible native
identities cryptographically bind message content and causal edges. Correctness
relies on the pinned endorsement policy and at most its configured fault bound.
The default experimental policy is three distinct signatures from four members,
with at most one faulty member. An ahead member can endorse an older cut it can
reconstruct from its own independently derived anchor and admitted delta. Importing
another certificate alone never establishes endorsement eligibility. A lagging
member cannot endorse an unknown branch.

Different cuts can both have valid certificates, including incomparable cuts.
This protocol does not elect a winning history, freeze editing, or require a
member to sign only one checkpoint. A returning client has a
[[SPEC-035-cached-state-checkpoints#Local floor|local floor]]: a durable commitment
and frontier for its previously accepted history. It installs a candidate only
after proving that the candidate **plus its admitted tail** contains that history.
If a local edit is missing, supply it in the tail or refuse installation; never
silently discard it. Signed evidence already held locally survives replacement.

If the latest cache entry is missing, try a bounded sequence of older entries and
verified catchup tails. Missing dependencies produce explicit fetch requests.
Failed candidates leave the installed state and floor unchanged. Installation also
fences concurrent changes to evidence, pending submissions and retry records.
A fresh client
without a floor can accept an old valid cut; neither signatures nor advertised
timestamps establish global freshness.

The reference implementation pins an immutable validated context, keeps evidence
in a persistent archive, and atomically commits one local generation. Foreground
preparation and pending old views share immutable snapshots rather than copying
live state. Bounded
validation runs outside the foreground thread. If an OS commit exceeds its budget,
the caller receives an uncertain outcome while the writer stays fenced until
completion or recovery. This is read compaction: it does not authorize deleting
covered messages or promise constant archive space.

**Decisions:** [[SPEC-035-cached-state-checkpoints#ADR-3500]] selects reusable
endorsements; [[SPEC-035-cached-state-checkpoints#ADR-3501]] separates certificates
from availability; [[SPEC-035-cached-state-checkpoints#ADR-3502]] restricts initial
kernel support; [[SPEC-035-cached-state-checkpoints#ADR-3503]] specifies incremental
publication and its measurement boundary;
[[SPEC-035-cached-state-checkpoints#ADR-3504]] chooses the reusable native dialect.

**Controls:** [[SPEC-035-cached-state-checkpoints#REQ-3500]] pinned context;
[[SPEC-035-cached-state-checkpoints#REQ-3501]] independent derivation;
[[SPEC-035-cached-state-checkpoints#REQ-3502]] quorum verification;
[[SPEC-035-cached-state-checkpoints#REQ-3503]] continuation laws;
[[SPEC-035-cached-state-checkpoints#REQ-3504]] ordinary admission;
[[SPEC-035-cached-state-checkpoints#REQ-3505]] local-history fence;
[[SPEC-035-cached-state-checkpoints#REQ-3506]] evidence retention;
[[SPEC-035-cached-state-checkpoints#REQ-3507]] bounded fallback;
[[SPEC-035-cached-state-checkpoints#REQ-3508]] atomic recovery;
[[SPEC-035-cached-state-checkpoints#REQ-3509]] nonexclusive cuts;
[[SPEC-035-cached-state-checkpoints#REQ-3510]] unsupported-profile refusal;
[[SPEC-035-cached-state-checkpoints#REQ-3511]] immutable publication;
[[SPEC-035-cached-state-checkpoints#REQ-3512]] explicit freshness status;
[[SPEC-035-cached-state-checkpoints#REQ-3513]] staged enablement;
[[SPEC-035-cached-state-checkpoints#REQ-3514]] companion scope and portable certificates;
[[SPEC-035-cached-state-checkpoints#REQ-3515]] checked compact-summary continuation proof;
[[SPEC-035-cached-state-checkpoints#REQ-3516]] through
[[SPEC-035-cached-state-checkpoints#REQ-3521]] all-head v2 continuation and proof gates.

**Open:** the kernel maintainer preserves the typed continuation proofs and
independent parity boundary under [[SPEC-035-cached-state-checkpoints#TEST-3525]].
Production endorsement-policy selection and security review belong to the protocol
owner; platform latency ratification belongs to the performance maintainer.
Native extraction/classification and universal Rust refinement are separate proof
boundaries. See [[SPEC-035-cached-state-checkpoints#Open work]].

### IMPL-029 all-head continuation plan

`plans/IMPL-029-all-head-checkpoint-continuation.spl` extends the existing
`spec-035-cached-checkpoints` Elephant theory with v2-specific task identities.
Runtime inventory/projection, native position and resource-port tasks can begin
independently. Closed codecs and ordered composition depend on the adapters; the
all-head typed proof requires their declared semantics; the parity bridge requires
runtime and proof results. Independent audit requires all gates, including the
preserved bounded persistence lifecycle. No v1 completion fact implies v2 completion.

## Amendment Channels

The user's request authorizes this specification, local implementation and acceptance verification.
Protocol maintainers can amend a draft through a reviewed repository change.
Production enablement requires independent security review and human domain
approval. No runtime flag, provider advertisement or checkpoint payload can waive
context binding, native authentication, causal admission, local-history coverage,
or retention of existing evidence. Changes to those obligations require an
explicit versioned specification amendment. This document changes neither the
existing admission authority nor the resource protocols.

## Problem and users

**FM-3500 — history on the opening path.** Reconstructing an object's frontier
state requires fetching and folding potentially thousands of old messages even
when the visible drawing is small. The desired remedy is amortized background
checkpoint publication and a short foreground tail, not simply a smaller hash.

**FM-3501 — unauthenticated or stale substitution.** A small snapshot can omit
effects, lie about accepted history, or replace a client's known branch with an
older state. A membership accumulator alone cannot establish the fold's result.

**FM-3502 — relocated work and unavailable evidence.** Fresh attestations during
each opening, full replay during every publication, a missing newest blob, or
missing dependency evidence can put the historical cost back on the critical path.

**FM-3503 — lost protocol obligations.** Installing visible state while dropping
causal metadata, local pending work or signed equivocation evidence can change
later admission or accountability despite an identical rendered drawing.

The opening client wants usable state without replaying the covered past. A
returning editor additionally needs its local edits and pending submissions kept.
An endorsing member wants to reuse its ordinary admission work and continue editing
while a frozen cut is certified. A cache provider is an untrusted byte supplier;
it can help availability but has no admission or freshness authority.

Happy paths are: fresh open from a recent certificate; returning open with a local
branch included in the tail; fallback to an older certificate; and background
publication while a lagging member remains offline. These are library workflows;
no new end-user screen or presentation contract is introduced.

## Semantic model

### Accepted cut

Let `C` be an independently pinned immutable context, `H` an authenticated,
accepted, duplicate-free set of object messages, and `F(H)` its canonical maximal
causal frontier. `H` contains the object root and the causal predecessors of each
member. Set membership is by the existing native message identity, using the
address scheme pinned in `C`; display aliases cannot substitute for identities.

Checkpoint eligibility requires native identities to cryptographically bind every
field read by authentication, causal admission and state folding, including signer,
object/role context, payload and predecessors. Valid signatures alone do not provide
this binding if an identity can name multiple signed contents. Profiles without
that native binding are unsupported in this version; no same-identity content or
edge substitution is permitted. Detached signature encodings can differ without
changing the uniquely bound message content; retain supplied signed evidence.

The context binds object root, complete installed dialect/role projection, cast
bindings, native authentication/address versions, checkpoint profile, state-summary
version, coverage scheme, endorsement-policy digest, checkpoint dialect code identity
and pinned companion root. Target and companion roots are distinct. Create the
companion root/cast before its opener binds the target context, avoiding a circular
identity dependency. The target installation independently authorizes that binding;
a provider cannot choose a new companion and roster. Admission remains
[[SPEC-019-state-rules#Receipt|the state rules' receipt contract]] and the existing verification lattice in
[[SPEC-003-verification-lattice]]. Resource protocols such as
[[SPEC-022-sealed-budget-checkpoints]] retain their separate authority.

### Checkpoint certificate

`M = (version, target_root, context_hash, companion_root, policy_hash, profile_hash,
coverage_root, summary_hash, frontier)` is the manifest. Native signed endorsement
acts bind its canonical identity and explicit target/context/policy/profile fields.
A certificate contains `M`, summary bytes, bounded companion bootstrap evidence,
and the original signed endorsement acts. `coverage_root = Cover(H)` commits the
accepted native identities, including the root and non-state-bearing accepted
messages. Frontier and summary are computed from exactly that same `H`. Companion
coordination acts never enter `H` or advance the target floor.

The initial coverage profile is a persistent sparse binary Merkle **set**, keyed
by domain-separated hashes of native addresses, with authenticated presence and
absence proofs. Its commitment is not a proof of acceptedness independent of the
certificate's trust assumptions. Other accumulators need a separately versioned
profile satisfying the same proof and update contracts; RSA setup or witness
assumptions are not introduced by this specification.

The historical v1 summary profile supports native `Initial`, `Values`, `ValuesPerKey`,
`ObservedSet`, `LwwRegister`, `LwwPerSigner` and `LwwMap`. Profile v2 extends this
to the entire inventory in [[SPEC-035-cached-state-checkpoints#REQ-3516]]. Both use the current
typed-HLC kernel semantics in [[SPEC-035-register-semantics]], including the
`multi-value-register` and `multi-value-map` aliases. Hash-arbitrated registers
retired by that specification are not reintroduced. It retains operation identities,
live contributions, replacement
scope and unresolved suppression information required by continuation. Rendered
values alone are insufficient. Signatures are normalized out of the semantic
summary while original signed bytes remain in the separate evidence archive;
alternative valid signatures for the same content cannot split summary identities.
Native recipient set/singleton/empty representations and performative aliases use
one canonical representative of their typed identity; payload and causal order
remain unchanged because they are identity-bearing.
The profile identity commits the exact canonical state-clause schema and summary
format version. Unknown profile claims can be attested generically but cannot be
installed by this adapter. For every supported admissible continuation `D`:

```text
render(Summary(H)) = fold(H)
render(advance(Summary(H), H, D)) = fold(H union D)
advance(..., duplicate) preserves rendered state and coverage
```

The `H` argument denotes authenticated coverage queries, not a requirement for a
client to possess `H`'s bodies. Order and batching of admissible deliveries do not
change the final result. Replacement references can be unresolved; later delivery
MUST not resurrect a suppressed contribution. Laws apply to each supported rule
and their composition, using the unchanged core fold as the executable oracle.

### Formal continuation model

The [[SPEC-035-cached-state-checkpoints#REQ-3515|formal continuation proof]] uses
`CBCL.State.Act`, the existing typed native state-kernel act, and the supported
`CBCL.StateKernelClause.Rule` meanings. It establishes extensional observation
equality against the unchanged kernel selections, reductions and clause semantics.
Generic identity/order lemmas require a checked instantiation to those types;
a detached address-only model does not discharge this requirement.

`H` and `D` are finite, already-admitted act histories. Their union deduplicates
by native identity. Equal identities have equal immutable semantic act content;
conflicting identities are outside this accepted-history precondition. Typed clock
and signer/address-order inputs follow the existing kernel's declared boundary.
Full-fold parity is over the accepted store after native identity normalization,
not an append-only list of every raw signed delivery attempt. Native-equivalent
recipient forms such as a singleton set and a single recipient, performative aliases
and signature variants MUST produce one canonical semantic projection and one
summary identity. Independent members admitting different valid aliases of the same
identity MUST derive identical summary commitments; the original signed bytes of
each attempt remain separately retained as evidence.

The raw native resource observer may diagnose two differently spelled duplicate
attempts as conflicting when handed both unnormalized bodies. That diagnostic is
outside the accepted-store continuation law: acceptance deduplicates by native
identity before native folding. Tests MUST distinguish this raw-input diagnostic
from an accepted-history regression, without suppressing faults on genuinely
inconsistent identities or weakening the native authority verifier.
Coverage queries mean exact membership in the pre-step accepted identity set.
These are explicit semantic preconditions, not an assumption that `advance` works.

A scoped row invariant relates the retained live contributions and pending
replacements to independently specified selection from `H`. Uncovered replacement
references remain scoped suppression obligations. Arrival of an identity resolves
its pending references in every row, including arrival of a non-state act, without
suppressing unrelated keys or signers. Covered replay changes neither state effects
nor coverage. Composition shares one identity set across all declared fields.

The computational summary contains the sufficient retained state, not a hidden copy
of all admitted bodies. `H` occurs only as a ghost argument of an invariant or theorem.
It MUST NOT be a runtime summary field or a captured history used by rendering or
refolding. Compact `Initial` stores sufficient uniqueness/ambiguity witnesses. Plain
`LwwRegister` stores the recognized maximum under the existing order. Winner-only
storage is not assumed sufficient for replacement-sensitive keyed/per-signer rules:
removing a winner can expose a previously losing live contribution.

The historical v1 composition is `Initial`, `Values`, `ValuesPerKey`, `ObservedSet`,
`LwwRegister`, `LwwPerSigner` and `LwwMap`. The v2 composition MUST cover every
head in [[SPEC-035-cached-state-checkpoints#REQ-3516]], including ordered derived
fields and the explicit native position/resource boundaries below. Unsupported
separate language features still reject under [[SPEC-035-cached-state-checkpoints#REQ-3510]]. The proof covers duplicate delivery,
scoped replacements, late referenced acts, cross-scope references, non-state
identity arrival, pending pruning, and composed fields with a shared coverage set.

Lean acceptance proves the typed semantic theorem. Rust extraction/correspondence,
canonical serialization/normalization, native identity bindings, admission,
signatures, coverage cryptography and host durability remain explicit external
boundaries. Independent parity vectors and counterexamples connect the implemented
summary transitions to the model; passing them does not turn the Lean theorem into
a proof that the Rust binary is correct. These boundary checks are required by
[[SPEC-035-cached-state-checkpoints#TEST-3519]] and tracked in
[[SPEC-035-cached-state-checkpoints#IMPL-028 continuation proof plan|IMPL-028 continuation proof plan]].

### IMPL-028 continuation proof plan

The executable plan is `plans/IMPL-028-checkpoint-continuation-proof.spl`, extending
the existing `spec-035-cached-checkpoints` theory. The row and compact-rule proof
maintainers can work independently. Composition depends on both proofs; the bridge
depends on composition; independent audit depends on composition and bridge evidence.
Existing runtime acceptance facts cannot complete these new proof tasks.

### Local floor

A floor is `(context_hash, coverage_root, frontier, local_generation)`, durably
bound to an installed client state. It represents **all locally accepted history**,
including accepted edits not yet uploaded or checkpointed. Pending or rejected
messages are not asserted accepted; their outbox, retry and diagnostic records are
retained separately. A verified certificate establishes a fresh client's initial
floor; each successful local admission advances it.

For old history `L`, proposed base `H` and admitted tail `D`, installation requires
`L subseteq H union D`. The operational check is a positive coverage proof under
the **final** candidate root for every old floor head. This suffices only because
the old frontier is complete, both histories are downward closed, causal edges are
immutable and the same context/root is pinned. These are proof obligations, not
properties inferred from an arbitrary provider's frontier. The old coverage root
binds the stored floor record; scalar sequence numbers and counts do not replace
the frontier check. Losing the durable floor loses rollback protection.

## Decisions

### ADR-3500: Certify computation once and reuse the certificate

Use native signed CBCL endorsement acts over independently derived cuts. Under a pinned static
policy `(roster, f, q)`, require `n >= 3f + 1` and `q = n - f` with distinct keys.
The initial conformance policy is `n=4, f=1, q=3`; other configured static policies
need the same tests before enablement. Safety of an individual result depends on
`q > f` and honest derivation, not on unique-cut agreement. The stronger default
quorum leaves an available honest quorum when the fault assumption holds.

This removes the need for interactive votes during opening. It spends background
member CPU and assumes bounded faulty membership rather than proving the fold in
zero knowledge. A cut can be correctly certified while omitting unrelated, unseen
messages. No globally complete history claim follows.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3501]],
[[SPEC-035-cached-state-checkpoints#REQ-3502]],
[[SPEC-035-cached-state-checkpoints#REQ-3509]].

### ADR-3501: Separate authenticity, discovery and availability

Manifests are semantic statements; certificates bundle native signed endorsements; blob identities
address exact serialized certificates. Different valid signature bundles can have
different blob identities for the same manifest. Native `publish` acts and untrusted advertisements list
candidate blob identities and tail offers. They cannot change pinned trust, raise
resource limits, or establish freshness. Publish immutable blobs before advertising
them, retain older reachable blobs, and try bounded fallback. Do not require an
all-member barrier or online signers to open an already certified cut.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3507]],
[[SPEC-035-cached-state-checkpoints#REQ-3511]],
[[SPEC-035-cached-state-checkpoints#REQ-3512]].

### ADR-3502: Put semantic adapters in the state kernel and I/O in the host

Reuse native message recognition, authentication, causal decisions and state-rule
semantics. Add rule-specific pure summary/update adapters and an authenticated
lookup interface at the existing kernel boundary. Add certificate checks alongside
those pure interfaces. Hosts own persistence, network fetch, deadlines, background
publication and scheduling. The research JSON format and drawing-specific code are
not production interfaces.

The shared `cbcl-checkpoint` crate composes `cbcl-core` and `cbcl-parser` rather
than introducing a dependency from the core back to the parser. Pure modules remain
available without `std`; filesystem, worker scheduling and durability are host
modules. Independently installed contexts are immutable constructor-validated
handles. Their native code identities are pinned once; ordinary admission does
not rehash or reinstall the complete dialect on every message.

Full original signed dependency messages plus coverage proofs are the initial
opening format. A provider MUST NOT invent a compact ancestor record or claim a
field is signed merely because an address is covered. Field-only openings need an
explicit native cryptographic binding and a new reviewed profile. This avoids
making the probe's experimental signature format a silent core wire change.

Support starts with the state rules above and causal clauses whose complete query
footprint is expressible through the ordinary finite lookup interface. Global
fan-in completeness and resource authority are not inferred from a drawing summary
or checkpoint quorum. Profile v2 requires explicit sufficient-state adapters for
every head, projected event output, verified position and native resource facts
under [[SPEC-035-cached-state-checkpoints#REQ-3516]]. Unsupported separate language
features use full ordinary replay. Generalization is per-profile conformance, never blanket dispatch.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3503]],
[[SPEC-035-cached-state-checkpoints#REQ-3504]],
[[SPEC-035-cached-state-checkpoints#REQ-3510]].

### ADR-3503: Incremental publication is part of the performance contract

Maintain persistent coverage nodes and rule summaries as ordinary admission accepts
new messages. Freeze immutable roots for an offer; later editing updates new roots.
Verify a proposal by comparing the independently maintained exact cut, or by
reconstructing that cut from a retained anchor and authenticated delta. Every
signing-eligible anchor has durable provenance back to pinned genesis and locally
performed native admission/summary derivation. Imported certified checkpoints are
opening-eligible but not signing-eligible until independent reconstruction checks
them. Propagating an imported root through a delta does not change that provenance.
A root copied from the proposer is not independent evidence. A member lacking a suitable
anchor can reconstruct in the background or decline; opening never waits for it.

Start with configurable publication after 32 newly accepted messages or 1,000 ms
since the first unpublished message, whichever occurs first; one in-flight job per
object, coalescing arrivals. These are provisional scheduler defaults, not safety
or availability bounds. Retry pending publication without blocking normal edits.
Catchup cost is governed by actual published-cut lag, not by a timer promise.
Trace: [[SPEC-035-cached-state-checkpoints#NFR-3500]],
[[SPEC-035-cached-state-checkpoints#NFR-3501]].

### ADR-3504: Use one general-purpose checkpoint companion dialect

Provide a bundled, versioned CBCL dialect with native `open`, `propose`, `endorse`
and `publish` acts. Its installed content identity, native signatures, role cast,
message shapes and causal protocol use the existing language mechanisms. Built-in
means shipped as a standard dialect definition, not exempt from installation or
authentication. Pin its exact code identity; a human-readable alias is not authority.

The same coordination dialect serves multiple target dialects and summary profiles.
It establishes who attested to which manifest and whether the pinned policy is
satisfied. Profile support is required for deriving, endorsing or installing state;
generic certificate verification can report a valid attestation bundle without
understanding that profile's fold. It MUST NOT report an unsupported snapshot usable.

Use a distinct companion thread bound to one target and immutable policy. The
companion's own coordination history is excluded from the target coverage and fold.
There is no recursive requirement to checkpoint the companion before opening the
target. Endorsements follow the fixed companion opener, with the manifest reference
as a signed data field; proposal history is not their causal prerequisite. A client
checks the bundled bootstrap and endorsements without replaying that history.

Native receipt of an endorsement is not a semantic derivation check. An honest
signing path requires a profile-issued endorsement capability; generic `intend`
or message construction alone cannot obtain the managed member's signature on it.
Faulty members can still sign false assertions within the declared fault model.
No arbitrary R7 data predicate or new global consensus gate is introduced.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3501]],
[[SPEC-035-cached-state-checkpoints#REQ-3502]],
[[SPEC-035-cached-state-checkpoints#REQ-3514]],
[[SPEC-035-cached-state-checkpoints#CON-3504]].

## Requirements

Every requirement's named failure is its intent trace. Contract and test links are
the implementation reading path; observation links define post-release evidence.

### REQ-3500: Independently pinned context

The verifier MUST derive context from trusted object installation and compare its
digest before accepting a manifest, signature, tail or local floor. Provider-supplied
rosters or profile identifiers MUST NOT override that context. A same-address root
under a changed dialect, cast, roster or summary version is a different context.
Failure: FM-3501. Trace: [[SPEC-035-cached-state-checkpoints#CON-3500]],
[[SPEC-035-cached-state-checkpoints#TEST-3500]], [[SPEC-035-cached-state-checkpoints#OBS-3500]].

### REQ-3501: Endorse exactly the independently established cut

An honest endorser MUST establish acceptance, downward closure, exact frontier,
coverage and summary for the requested cut before signing an endorsement of its
manifest identity. Unavailable
or unaccepted ancestors prevent endorsement. Importing a certificate without
independent reconstruction MUST NOT unlock endorsement, including for descendants
of that imported cut. Accepted messages outside that cut do
not prevent endorsing it. Invalid derivations MUST expose no signing request.
The resulting capability MUST bind the exact canonical native `endorse` message,
context and authorized signer. The managed signer MUST refuse an endorsement
constructed without that capability or changed after authorization.
Failure: FM-3501. Trace: [[SPEC-035-cached-state-checkpoints#CON-3501]],
[[SPEC-035-cached-state-checkpoints#TEST-3501]], [[SPEC-035-cached-state-checkpoints#OBS-3501]].

### REQ-3502: Verify the complete certificate

Opening MUST verify the pinned threshold of distinct native endorsement signers,
companion bootstrap and causal/role scope, canonical manifest, summary hash and
structural summary invariants before use. Neither valid
blob addressing nor a coverage proof substitutes for these checks. Opening an
available certificate MUST require no fresh signatures.
Certificate validity is derived by the verifier from the bundle; acceptance of a
`publish` act or a native `count` fold MUST NOT declare certification.
Failure: FM-3501, FM-3502. Trace: [[SPEC-035-cached-state-checkpoints#CON-3500]],
[[SPEC-035-cached-state-checkpoints#TEST-3502]], [[SPEC-035-cached-state-checkpoints#OBS-3500]].

### REQ-3503: Preserve state under continuation

Each enabled summary adapter MUST satisfy the render, continuation and duplicate
laws in the semantic model for every supported rule composition. Summary validation
MUST reject duplicate identities, conflicting identity payloads, impossible scope
references and malformed values. Covered duplicates MUST NOT refold a contribution.
Failure: FM-3500, FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3502]],
[[SPEC-035-cached-state-checkpoints#TEST-3503]], [[SPEC-035-cached-state-checkpoints#OBS-3500]].

### REQ-3504: Preserve ordinary message admission

Every tail message, including covered replays, MUST undergo native authentication,
identity/context checks and the applicable existing admission/evidence rules.
Covered accepted predecessor facts MAY be supplied through verified openings; an
opening MUST bind the original message's identity, authenticated fields and
membership to the root at which it is used. Missing data returns explicit
dependencies; wrong data retains the ordinary invalid verdict. Snapshot contents
MUST NOT supply an arbitrary precomputed admission verdict.
Failure: FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3502]],
[[SPEC-035-cached-state-checkpoints#TEST-3504]], [[SPEC-035-cached-state-checkpoints#OBS-3500]].

### REQ-3505: Preserve the local accepted history

A returning client MUST verify every old floor head in the final candidate root
after successful tail admission and before installation. Failure MUST leave the
old state and floor installed. A valid older certificate can be used when its tail
reaches the floor; a higher advertised revision cannot bypass this check.
Failure: FM-3501. Trace: [[SPEC-035-cached-state-checkpoints#CON-3503]],
[[SPEC-035-cached-state-checkpoints#TEST-3505]], [[SPEC-035-cached-state-checkpoints#OBS-3502]].

### REQ-3506: Preserve signed evidence and local pending work

Replacement MUST retain every original signed message/evidence record already held
locally, including covered and superseded messages and evidence from covered replay
attempts. Pending outbox/retry records retain their identities and status unless
ordinary admission independently changes them. Checkpoint installation MUST NOT
introduce a new garbage-collection, fork-exclusion or resource-release authority.
Failure: FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3503]],
[[SPEC-035-cached-state-checkpoints#TEST-3506]], [[SPEC-035-cached-state-checkpoints#OBS-3502]].

### REQ-3507: Bound candidate work and fallback

The loader MUST recognize bounded inputs before cryptographic or admission work,
charge cumulative bytes/work across candidates, and try eligible fallback entries
within the same operation budget. Missing, corrupt, blocked or oversized entries
MUST NOT prevent trying a later entry when budget remains. Exhaustion returns an
explicit failure with prior state unchanged; it MUST NOT silently raise limits or
initiate unbounded full replay.
Failure: FM-3502. Trace: [[SPEC-035-cached-state-checkpoints#CON-3500]],
[[SPEC-035-cached-state-checkpoints#TEST-3507]], [[SPEC-035-cached-state-checkpoints#OBS-3500]].

### REQ-3508: Commit a replacement atomically and recover the floor

The host MUST persist the verified summary, roots, frontier, evidence references,
pending records and updated floor as one generation change before exposing it as
installed. Installation MUST compare the captured local generation; a concurrent
local edit forces restaging or retry. The compared generation MUST also cover every
evidence, outbox, retry and retained-diagnostic mutation, even when the accepted
frontier is unchanged. Crash recovery yields either the old complete
generation or the new complete generation, never a new state with an old/missing
floor. Failed candidate staging MUST emit no edits, votes or accepted-state changes.
Failure: FM-3501, FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3503]],
[[SPEC-035-cached-state-checkpoints#TEST-3508]], [[SPEC-035-cached-state-checkpoints#OBS-3502]].

### REQ-3509: Permit distinct valid cuts without consensus

Members MAY endorse multiple correctly derived cuts, including incomparable cuts.
The protocol MUST NOT infer a unique successor, deletion right or fork rejection
from certificate quorum intersection. Opening and subsequent merging still satisfy
the local floor and ordinary admission requirements. A lagging member's absence
MUST NOT block certification when the configured threshold is available.
Failure: FM-3502, FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3501]],
[[SPEC-035-cached-state-checkpoints#TEST-3509]], [[SPEC-035-cached-state-checkpoints#OBS-3501]].

### REQ-3510: Refuse unsupported semantic profiles

Enablement MUST check the complete installed dialect, all state rules and all
causal lookup/completeness obligations against an explicit capability profile.
An unsupported component MUST disable checkpoint bootstrap for that object and
report ordinary replay as the available path; partial state MUST NOT be presented
as the complete kernel state. Resource certificates and permanent obligations
MUST NOT be synthesized from a checkpoint's rendered value.
Failure: FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3502]],
[[SPEC-035-cached-state-checkpoints#TEST-3510]], [[SPEC-035-cached-state-checkpoints#OBS-3500]].

### REQ-3511: Publish immutable retrievable bytes

A publisher MUST durably store the complete content-addressed certificate before
advertising its blob identity. Existing bytes at that identity MUST match exactly.
The client MUST verify the requested blob identity on received bytes before decode.
Publication or advertisement failure MUST leave existing certificates reachable
and ordinary editing available. Publication MUST NOT delete accepted history.
Failure: FM-3502, FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3501]],
[[SPEC-035-cached-state-checkpoints#TEST-3511]], [[SPEC-035-cached-state-checkpoints#OBS-3501]].

### REQ-3512: Report the strength of the installed result

Opening MUST return the installed manifest/cut, resulting frontier, local-floor
check result, residual missing dependencies and fallback reasons. A valid cached
cut MUST NOT be labelled globally latest, finalized or history-complete. Freshness
relative to a caller-supplied target is reported only after that target's coverage
is verified; provider clocks and revision numbers remain hints.
Failure: FM-3501. Trace: [[SPEC-035-cached-state-checkpoints#CON-3503]],
[[SPEC-035-cached-state-checkpoints#TEST-3512]], [[SPEC-035-cached-state-checkpoints#OBS-3500]].

### REQ-3513: Stage enablement and preserve the disable path

Hosts MUST expose runtime modes `off`, `shadow`, and `enabled`, with `off` the
initial default and per-object profile gating. Shadow mode verifies and compares
with ordinary replay but installs nothing. Disabling stops new checkpoint installs
and publications without deleting evidence or rolling installed history backward.
Continuing by ordinary replay requires the retained signed archive to be available;
otherwise report missing archive and preserve the current verified state. Hosts
MUST notify integrators before enabling refusal/resource-limit behavior.
Failure: FM-3502, FM-3503. Trace: [[SPEC-035-cached-state-checkpoints#CON-3503]],
[[SPEC-035-cached-state-checkpoints#TEST-3513]], [[SPEC-035-cached-state-checkpoints#OBS-3502]].

### REQ-3514: Reusable companion dialect and portable certificates

Checkpoint coordination MUST use the built-in companion dialect defined in
[[SPEC-035-cached-state-checkpoints#CON-3504]]. Every act MUST bind the pinned target,
context, policy, profile and companion scope. The dialect MUST remain reusable
across target dialects; it MUST NOT encode drawing-specific summary rules.
Certificates MUST carry the original native signed endorsements and the bounded
bootstrap needed to verify them without companion-history replay. Proposals and
publication hints MUST NOT acquire endorsement or installation authority.
Failure: FM-3500, FM-3501, FM-3502; user-requested reuse of CBCL dialect mechanisms.
Trace: [[SPEC-035-cached-state-checkpoints#CON-3504]],
[[SPEC-035-cached-state-checkpoints#TEST-3517]], [[SPEC-035-cached-state-checkpoints#OBS-3501]].

### REQ-3515: Prove compact-summary continuation against the native kernel

The kernel maintainer MUST supply a Lean-kernel-checked proof of the render and
continuation laws in [[SPEC-035-cached-state-checkpoints#Checkpoint certificate]],
using the model boundary in
[[SPEC-035-cached-state-checkpoints#Formal continuation model]]. The proof MUST
cover the entire supported rule composition and identity deduplication, scoped
replacement suppression, delayed arrival, and pending-reference pruning. Row and
compact-rule proofs MUST instantiate the existing typed native acts and kernel
meanings; replacing the reference fold with the summary's own evaluator does not
establish correspondence.

The proof MUST derive and preserve a sufficient-state invariant before concluding
`render(advance(summary(H), tail)) = fold(H union tail)`. It MUST NOT store or refold
a whole-history cache inside the computational summary, assume an
`advance-is-correct` premise, or hide the desired equality in the definition of
`render`, `advance` or its invariant. New proof modules MUST contain no `sorry`,
`admit` or `axiom` declarations. The transitive theorem dependencies MUST be audited
for `sorryAx`, project-specific axioms and equivalent unchecked assumptions;
Lean's standard foundational dependencies are reported explicitly.

The release claim MUST distinguish the proved typed model from the unproved Rust,
serialization, admission and cryptographic boundaries. Independent parity vectors
and hostile counterexamples MUST exercise that boundary. Existing runtime acceptance
and a successful Lean build alone MUST NOT mark this requirement complete.
Failure: FM-3500, FM-3503; user-requested formal evidence for the continuation law.
Trace: [[SPEC-035-cached-state-checkpoints#CON-3502]],
[[SPEC-035-cached-state-checkpoints#REQ-3503]],
[[SPEC-035-cached-state-checkpoints#TEST-3519]],
[[SPEC-035-cached-state-checkpoints#IMPL-028 continuation proof plan|IMPL-028 continuation proof plan]].

### REQ-3516: Cover the complete native head inventory

Profile v2 MUST support `Initial`, `Exists`, `Count`, `Progress`, `Events`,
`SetUnion`, `Values`, `ValuesPerKey`, `ObservedSet`, `Counter`, `Histogram`, `Sum`,
`LwwRegister`, `LwwPerSigner`, `LwwMap` and `BoundedCounter` with unchanged native
semantics. Aliases normalize to these heads, not additional inventory entries.
The runtime enabled whitelist, typed Lean inventory and native head mapping MUST
be checked for exact correspondence. No head can be omitted by retaining the v1
whitelist. Domains and global `All` are separate features and MAY remain gated
when not required to implement these heads; the profile MUST declare such gates.
All previous bounded opening, persistence, floor, evidence, independent endorsement,
ordinary admission and failure-atomicity requirements remain binding end to end.
Failure: FM-3500, FM-3503; incomplete head coverage defeats the approved generalization.
Validates through [[SPEC-035-cached-state-checkpoints#TEST-3520]].

### REQ-3517: Retain projections and evaluate ordered derived fields

`Events` MUST retain projected records `{id, signer, selectedValue}` sufficient
for native event observations; full native message bodies MUST NOT be retained
as its summary representation or fetched to render the checkpoint. Selected values
MUST preserve native typing and identity normalization. Storage MAY grow with event
output; no constant-space promise applies to growing projections or live output.
`Histogram` and `Sum` MUST resolve earlier fields in native clause order and preserve
native source compatibility and errors, including composed projected/map sources.
The adapter MUST NOT silently reorder fields or accept forward references rejected
by the native clause. Existing suppression, duplicate identity and pending-pruning
laws apply to all affected projections and compositions.
Failure: FM-3500, FM-3503; whole-body retention hides replay cost and wrong ordering changes results.
Validates through [[SPEC-035-cached-state-checkpoints#TEST-3521]].

### REQ-3518: Resume progress and native verified protocol position

`Progress` MUST retain the native sufficient maximum and resume the protocol
position used by ordinary causal verification, including R5 checks on tail acts.
A snapshot MUST NOT treat every covered parent as being at an arbitrary permitted
position. Position facts MUST be bound to the accepted context/cut and validated
through the existing native verifier. Duplicate delivery and concurrent branches
MUST preserve the native progress/position result or native rejection. Missing
position evidence produces the existing explicit dependency/refusal outcome,
without installing partially advanced state.
The full-history oracle MUST use the same native identity indexes as ordinary
verification: protocol stores use `sha256:<hex>` native IDs, while state coverage
and replacements use the corresponding `sha256-<hex>` wire alias. Equality of the
digest does not permit a store lookup to silently miss the other spelling. Alias
conversion is an index operation, never a rewrite of original signed bytes. A
progress comparison against a broken all-zero oracle does not satisfy parity.
Failure: FM-3500, FM-3503; a correct rendered maximum alone cannot authorize the next act.
Validates through [[SPEC-035-cached-state-checkpoints#TEST-3522]].

### REQ-3519: Resume materialized resource facts without granting authority

Resource continuation MUST preserve native verifier results, fact tags, authority
and fault behavior for legacy core folding and Collective/Quorum modes. A checkpoint
quorum attests state; it MUST NOT itself grant resource rights, manufacture agreement
or replace native agreement signatures. Resource classification remains an explicit
native-port boundary. Materialized projected resource facts MUST factor through the
reference verifier: the typed proof MUST establish that independently specified
verified facts suffice for native folding and tail continuation, with the boundary
and its preconditions stated. Assuming the desired advance-correct equality, or
calling unverified classifications valid because a certificate carries them, does
not establish that factorization. Unavailable facts or failed native authority/tag
checks MUST preserve the ordinary fault/refusal result and leave installed state intact.
The ordinary resource oracle and projected fact observer MUST both normalize
native colon/dash aliases at the state-index boundary for opener predecessors,
`prev` and every `deps` entry. They MUST retain opener role/cast authority, language,
thread and authenticated sender information used by the native verifier. Missing
facts and present-but-invalid authority are distinct outcomes; state quorum cannot
turn either into a ready resource. Native alias corrections are checked in both
ordinary replay and resumed paths, not patched into expected values in the test.
Failure: FM-3503; cached state must not become a resource-authority bypass.
Validates through [[SPEC-035-cached-state-checkpoints#TEST-3523]].

### REQ-3520: Recognize and bind closed Profile v2 records

Profile v2 MUST bind its canonical ordered clause, projection semantics, native
protocol/resource assumptions and summary format in its profile/schema identity.
The normative codec artifact is [WIRE.md](../crates/cbcl-checkpoint/WIRE.md), read
with [[SPEC-035-cached-state-checkpoints#Profile v2 wire grammar]]; its field order,
variant tags, nested records and bounds are part of this requirement.
Its codecs MUST completely recognize a documented versioned closed grammar before
semantic use, reject unknown variants, duplicates, malformed lengths, noncanonical
ordering and trailing bytes, and roundtrip recognized records canonically. No v1
bytes or profile identity may silently acquire v2 meanings. Generic attestations of
unknown profiles remain distinct from installable summaries. Host budgets MUST bound
v2 recognition, authenticated dependencies and durable writes; output-size growth
MUST be accounted for explicitly rather than hidden in an unbounded foreground clone.
Failure: FM-3500, FM-3502, FM-3503; unbound projections or codecs change attested semantics.
Validates through [[SPEC-035-cached-state-checkpoints#TEST-3524]].

### REQ-3521: Prove and independently bridge the full typed v2 continuation law

The all-head typed Lean composition MUST prove semantic
`render(advance(summary(H), tail)) = fold(H union tail)` against existing native
`CBCL.State.Act` and kernel meanings, including ordered derived clauses, duplicate
identities, replacement scopes, pending pruning, projected events, progress/position
and materialized resource-fact factorization. The proof MUST derive sufficient-state
invariants, not store a whole-history cache or assume advance correctness. The
no-placeholder and transitive assumption audit of
[[SPEC-035-cached-state-checkpoints#REQ-3515]] remains binding.
Independent Rust/native/Lean parity vectors and counterexamples MUST bind the exact
v2 runtime, model, adapters and inventories. Rust extraction, serialization, native
classification/verification, admission, signatures and host durability remain
explicit external boundaries unless separately proved. Native-port assumptions MUST
be visible rather than absorbed into an assumed continuation law. Historical v1
proofs and benchmarks remain valid only for their pinned scope and sources; they
MUST NOT be presented as v2 acceptance. Implementation and formal-verification status
remain in progress until the new gates and independent review pass.
Failure: FM-3500, FM-3503; partial or circular proofs cannot establish all-head correctness.
Validates through [[SPEC-035-cached-state-checkpoints#TEST-3525]].

## Contracts

### CON-3500: Recognition, identities and budgets

Coordination uses the native CBCL grammar in
[[SPEC-035-cached-state-checkpoints#CON-3504]]. Snapshot, certificate and proof blobs
use a closed, versioned binary record grammar, embedding native signed-message
bytes unchanged. The following schema defines field order;
`u32` and `u64` are unsigned big endian, `h32` exactly 32 bytes, `bytes` a `u32`
length and that many octets, `vec<T>` a `u32` length followed by that many `T`.
All lengths are checked against local limits before allocation, arithmetic is
checked, and complete recognition forbids trailing bytes, alternate tags and
duplicate/colliding identities. Sets and keyed maps use strictly ascending canonical
encoded key order. Unknown versions reject; there is no permissive normalization.

```text
NativeId    = bytes                         # recognized by pinned native address codec
Context     = bytes                         # canonical installed-context descriptor
Manifest    = u32 NativeId h32 NativeId h32 h32 h32 h32 vec<NativeId>
               # version, target, context, companion, policy, profile, coverage, summary, frontier
Bootstrap   = bytes bytes                  # native companion root/cast and signed opener
Endorsement = bytes                        # complete original native signed endorse act
Certificate = Manifest bytes Bootstrap vec<Endorsement>
               # manifest, canonical profile summary, fixed bootstrap, endorsements
Proof       = u32 vec<h32>                  # presence tag 0/1, exactly 256 siblings
Opening     = bytes Proof                   # original native signed message, membership
TailStep    = bytes vec<Opening> Proof vec<ReplacementProof>
                                             # message, admission lookups, own pre-root
                                             # presence/absence, replacement queries
Offer       = h32 vec<TailStep> vec<FloorProof>
ReplacementProof = NativeId Proof           # scoped replacement-query identity
FloorProof  = NativeId Proof                 # exactly one per captured old floor head
Advertisement = u32 h32 vec<h32>             # optional untrusted transport hint, not a vote
```

`TailStep` proof queries follow the deterministic profile-declared footprint order;
no missing or unused query is accepted. Every proof is checked against the precise
pre-step root, except `FloorProof`, checked against the final candidate root.
The coverage profile uses depth 256 with leaf/branch/empty domains and explicit
height; key derivation, empty hashes and left/right bit order MUST have fixed
cross-language vectors before enablement. Summary bytes use a profile-declared
closed grammar and MUST re-encode identically. The historical v1 profile encodes ordered
live-contribution and unresolved-suppression maps with canonical native scalar values.
Its exact record is `u32(version=1) h32(schema) vec<Row>`; each `Row` is
`vec<Live> vec<Pending>`, with `Live = bytes(wire-id) bytes(signer)
bytes(normalized-native-message)` and `Pending = bytes(scope) bytes(target-id)`.
Live rows sort by wire identity and pending rows by encoded scope/target pair.
Decoded explicit identities must match the normalized native messages.
Opaque bytes do not waive grammar recognition by the selected native/profile codec.
Profile v2 MUST have distinct version/schema bindings and a fully specified closed
record for each enabled row, projected event, position and resource-fact variant
under [[SPEC-035-cached-state-checkpoints#REQ-3520]]. The v1 row record above is
not an implicit grammar for v2 or permission to reinterpret old bytes.

### Profile v2 wire grammar

This appendix fixes the current binary layout implemented by `Summary::encode`
and recognized by `Summary::decode_for` in `crates/cbcl-checkpoint/src/summary.rs`.
It uses the big-endian primitives above. `string` is `bytes` containing valid UTF-8;
`sexpr` is `bytes` containing exactly one canonical typed native S-expression.
`i128` is 16-byte signed two's-complement big endian. An option has exactly the
listed tags, not an implicit nullable JSON value.

```text
SummaryV2 = u32(2) h32(schema) GlobalResume vec<RowV2>
GlobalResume = u32(0) | u32(1) bytes(ProgressResumeV1)
OptValue = u32(0) | u32(1) sexpr
Contribution = string(wire-id) string(signer) OptValue(key) OptValue(value) OptValue(clock)
Event = string(wire-id) string(signer) sexpr(selected-value)
Pending = bytes(scope) string(target-wire-id)
```

The schema is `Hash("cbcl/checkpoint/summary-schema/v2", canonical-signable-dialect)`
with the ordered state clause and pinned causal protocol installed into the base
dialect. The profile hash is this schema hash; the summary commitment uses
`Hash("cbcl/checkpoint/summary/v2", encode(SummaryV2))`. Signature evidence is stored
separately. `Contribution.clock`, when present, is a native string atom containing
a recognized HLC; other value shapes reject. Native symbols/keywords in selected
state values follow the existing canonical semantic normalization; decoders reject
alternative noncanonical representatives. Rule-specific footprints constrain which
key/value/signer/clock fields may be populated.

| Row tag | Payload after the `u32` tag | Matching native rule |
|---|---|---|
| 0 | `vec<Contribution>` with at most two witnesses | Initial |
| 1 | `vec<Contribution> vec<Pending>` | Values, ValuesPerKey, ObservedSet, LwwPerSigner, LwwMap |
| 2 | `vec<Contribution>` with zero or one winner | LwwRegister |
| 3 | `u32(0)` or `u32(1)` | Exists |
| 4 | `u64` | Count |
| 5 | `i128` | Counter |
| 6 | `vec<sexpr>` | SetUnion |
| 7 | `vec<Event>` | Events |
| 8 | empty payload | Histogram, Sum; reference earlier rendered fields |
| 9 | `bytes(ProgressResumeV1)` | Progress |
| 10 | `bytes(ResourceResumeV1)` | BoundedCounter |

The number and tags of rows MUST match the independently pinned ordered clause.
Contributions and events sort strictly by wire identity; set values sort strictly
by canonical encoded value. Pending entries sort strictly by the concatenated
`bytes(scope) string(target)` encoding. Empty scope is the unkeyed scope; nonempty
scopes are recognized canonical values, with signer scope a string. Duplicate
entries, a pending target already present in the same live row, or invalid native
wire identities reject. The current profile permits at most 1,024 rows, at most
65,536 entries per unbounded row component, at most 256 KiB per selected native
value/scope and 16 MiB total summary bytes. These are refusal bounds, not promises
that growing event output stays within them. Initial and winner bounds above are
stricter. Derived rows carry no cached full-body source or duplicated output.

```text
ProgressResumeV1 = u32(1) h32(protocol-code) string(verb) PositionTable
PositionTable = u32(0)
              | u32(1) string(native-root) string(thread) vec<PositionRecord>
PositionRecord = string(native-id) string(wire-verb) Cause
Cause = u32(0) | u32(1) | u32(2) string(parent-id)
      | u32(3) vec<string(parent-id)>
ResourceResumeV1 = u32(1) RuleBinding vec<sexpr(ResourceFact)> vec<string(known-id)>
RuleBinding = byte(0) | byte(1) h32(rule-options)
```

Position causes distinguish absent, `begin`, single and multiple predecessors.
A multiple list is nonempty, strictly ordered and limited to 256 parents. Position
records sort strictly by native ID, at most 65,536 records; root/ID strings are at
most 256 bytes and thread/verb strings at most 4,096 bytes. Protocol code is
`Hash("cbcl/checkpoint/progress-resume/schema-v1", UTF8(dialect_hash(base-with-protocol)))`.
Ranks are never serialized; recognition recomputes the existing native relation
under the pinned protocol/context and requires the root record. These headers do
not encode or authenticate a cast; the independently authenticated target root and
enclosing certificate provide that binding. Without a protocol, native Progress is zero;
with repeat-position queries, global resume metadata is retained even if no Progress
field is declared. The presence requirements are checked against that installed profile.

A resource fact is a canonical native list of exactly these ten elements:

```text
ResourceFact = (address verb signer identity-hex (predecessors...)
                optional-language optional-thread optional-from optional-bindings
                ((field-name selected-value)...))
```

The first four elements and predecessor entries are string atoms. The identity
commitment is a string of 64 lowercase hex digits. Each optional element is an
empty list or singleton list; language/thread singleton values are string atoms,
while bindings, when present, is itself a list. Selected field pairs have arity two
and unique string names in canonical map order. Only the configuration's fields
for that fact's verb and native `prev`/`deps` are allowed. Facts also retain the
native opener's role bindings and wrapper context needed for resource authority;
a fact is not an original Message or a signature archive.

Resource facts sort by address; known IDs sort strictly and designate only referenced
identities whose facts are absent. The optional rule binding pins the canonical
native CounterRule options with the domain
`cbcl/checkpoint/resource-rule/v1`; an unbound record contains no facts or
known IDs. The resource subrecord permits at most 65,536 facts and known IDs each,
256 KiB per fact and 16 MiB overall, with fact address at most 128 bytes, signer/verb
at most 2,048 bytes, at most 64 predecessors and 1,024 selected fields. Recognition
reruns the native fact observer; no serialized cached ready/fault verdict is trusted.
Canonical roundtrip, full consumption and the enclosing schema binding apply to
both nested subrecords. A structurally recognized resume record alone grants no
admission, position, resource or endorsement authority.

For domain string `d` and payload `p`, define `Hash(d,p) = SHA256(bytes(d)||bytes(p))`.
Manifest identity is `Hash("cbcl/checkpoint/manifest/v1", encode(Manifest))`.
Native signatures authenticate complete canonical `endorse` acts in the pinned
checkpoint dialect, including manifest identity and scope fields. There is no
separate detached manifest-vote signature format. Context, summary and blob hashes use respectively
`cbcl/checkpoint/context/v1`, `cbcl/checkpoint/summary/v2`, and
`cbcl/checkpoint/blob/v1`. Coverage hashing has its own versioned domains.
Signature verification uses the pinned native algorithm and strict canonical
signature parser. Endorsement bundles sort by the authenticated signer's pinned
roster index, contain no repeated signer, and reject inconsistent scope or manifest
fields. Claimed actor fields do not determine signer identity.
The profile summary version is part of `Context`; bytes from the research JSON
probe are deliberately incompatible with this wire profile.

Initial local limits are provisional engineering defaults: 8 candidates per open,
16 MiB per certificate, 4 MiB per serialized offer excluding certificate,
2,048 tail steps per candidate, 4,096 frontier heads, 256 KiB per native message,
and 256 dependency/replacement queries per step. Cumulative limits are 32 MiB
received, 4,096 admitted/attempted tail steps and 65,536 proof paths per open.
Every duplicate, rejected candidate and failed proof consumes budget. Limits cannot
be raised by input. A host schedules at most 5,000 ms per open operation by default,
with cancelable fetches and cooperative bounded verification batches; exhaustion
returns `BudgetExceeded`. Platform conformance MUST verify cancellation rather than
calling a byte cap a time bound. Header lengths exceeding limits reject before
signature/proof work. Limits are not assertions that every valid object fits.

Preconditions: independently installed context and immutable local limits.
Postconditions: a fully recognized typed value, or a bounded explicit error with
no installed-state changes. Trace: [[SPEC-035-cached-state-checkpoints#REQ-3500]],
[[SPEC-035-cached-state-checkpoints#REQ-3502]], [[SPEC-035-cached-state-checkpoints#REQ-3507]].

### CON-3501: Proposal, endorsement and publication

`prepare_cut(frontier)` returns an immutable independently validated cut handle or
`MissingDependencies`, `UnsupportedProfile`, `InvalidCut`, or `BudgetExceeded`.
Cut handles record signing eligibility and derivation provenance; recovery verifies
that provenance before permitting signatures. `authorize_endorse(handle, manifest,
native_act, signer)` compares all manifest and scope fields, signer role and canonical
act bytes, then returns an opaque endorsement capability only on equality. The
managed host signer consumes that capability and signs those exact native bytes
with its configured roster key. Generic authoring cannot bypass authorization;
no parser or provider gets access to the key. Collectors verify the native signed
acts through the certificate verifier before bundling them.

No message count, timestamp or proposer assertion establishes inclusion. Frozen
cut handles can share persistent structure while current admission advances.
Publish idempotently by exact blob hash. Discovery ranks candidates as hints only;
choosing a candidate is not a global consensus step. Availability assumes a
reachable provider retaining the certificate **and** required signed openings,
update proofs and tail. Quorum signatures alone guarantee none of those services.

Preconditions: fully recognized native messages and pinned policy.
Postconditions: an independently derived manifest with native signed endorsements
and immutable bytes, or
an explicit decline without changing admission state. Host cache adapters MUST
have a bounded read contract: no symlink/path escape or blocking special-file
open; regular-file reads still require a deadline/cancellation mechanism. Durable
publication includes directory/metadata persistence required by the chosen store,
not only a file write followed by an unacknowledged rename.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3501]],
[[SPEC-035-cached-state-checkpoints#REQ-3509]], [[SPEC-035-cached-state-checkpoints#REQ-3511]].

### CON-3502: Pure summary and authenticated admission adapter

`validate_summary`, `render`, `advance`, `verify_coverage` and `admit_with_openings`
are pure deterministic functions. Inputs are typed immutable structures plus the
pinned context; outputs are new roots, summary deltas, exact dependency queries,
ordinary verdicts or errors. They have no storage, networking or signing effects.

For uncovered messages, authenticate first, evaluate the existing shape/causal
rules using fully authenticated dependency openings, and only then insert the
accepted identity and apply its summary delta. For covered replays, authenticate
and preserve supplied evidence, but do not reapply the state effect. A wrong
opening dominates a merely missing one according to ordinary verifier semantics.
Proofs cannot be reused under a different root as the tail advances. Root/object
metadata comes from pinned installation or an authenticated opening, never an
unverified snapshot field. Each enabled dialect has a total admission-footprint
adapter; absence of a completeness witness for any required query is unsupported
or pending, never success by omission.

Preconditions: recognized certificate/steps and a supported installed profile.
Postconditions: ordinary-core-equivalent verdict/state for the same accepted set,
or an error without committing the candidate. Composed rules share one deduplicated
identity set; one message can affect multiple rule summaries but is covered once.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3503]],
[[SPEC-035-cached-state-checkpoints#REQ-3504]], [[SPEC-035-cached-state-checkpoints#REQ-3510]].

### CON-3503: Open, stage and commit

`open(context, candidates, captured_floor, generation, limits)` returns
`PreparedInstall`, `NeedDependencies`, `NoUsableCandidate`, `UnsupportedProfile`,
`BudgetExceeded`, or `Cancelled`, with candidate-specific bounded reasons.
`PreparedInstall` owns a verified summary, final root/frontier, captured generation,
floor proofs, evidence additions and status. It is not externally installed state.

Candidate order is: bounded fetch and hash verification; full recognition;
context/summary/quorum verification; tail admission in deterministic dependency
order; final floor proofs; merge old retained evidence and pending records; then
prepare one new generation. Installation uses a durable generation compare-and-swap.
The generation covers accepted state, evidence additions and pending/outbox/retry
mutations. If any advanced, re-stage from current records or return
`ConcurrentLocalUpdate`; a state-only compare-and-swap is insufficient.
No caller observes an intermediate candidate. Recovery validates the durable
generation record before serving it. Full-replay recovery is an explicit separate
operation, not an implicit fallback that defeats the opening budget.

Only successful new admission changes coverage/frontier. Each accepted new message
removes its direct parents from the frontier and adds its identity. Covered
duplicates do not advance the frontier. Tail dependency requests identify exact
missing native identities and root/version requirements without claiming freshness.
Result status is `CertifiedCut` with optional `LocalFloorPreserved` and
`RequestedTargetCovered`; there is no `GloballyLatest` result constructor.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3505]],
[[SPEC-035-cached-state-checkpoints#REQ-3506]], [[SPEC-035-cached-state-checkpoints#REQ-3508]],
[[SPEC-035-cached-state-checkpoints#REQ-3512]], [[SPEC-035-cached-state-checkpoints#REQ-3513]].

### CON-3504: Built-in checkpoint dialect

The native dialect is a content-addressed standard definition bundled with the
trusted library release and installed under existing CBCL dialect/shape/role rules.
Separately distributed signed definitions retain ordinary R4 verification; an
unsigned bundled definition MUST NOT be described as author-signature verified.
The pinned native code identity and authenticated companion cast bind the shipped
definition, not its human author label. It declares an
initializer role and a repeated member role. The initializer opens the companion;
every policy member can propose, endorse or publish. Initialization authority does
not confer a new power to replace the independently pinned target policy. The cast
member keys MUST equal the policy roster, with unique canonical key identities.

The following is a closed payload grammar over the existing native S-expression
AST, not a replacement grammar for native signed/thread/role wrappers. Fields occur
exactly once in the displayed order; unknown fields reject. `id` is the pinned
native address grammar, `hash` a lowercase 64-hex string, and `version` integer 1.
`locations` is a list of at most 8 UTF-8 strings, each at most 2,048 bytes. Locations
are hints handled under host fetch policy; receiving one never initiates a fetch.

```text
scope = :target id :context hash :policy hash :profile hash
open    = (open recipients scope :version version)
propose = (propose recipients scope :manifest hash :descriptor hash)
endorse = (endorse recipients scope :manifest hash)
publish = (publish recipients scope :manifest hash :certificate hash
                   :locations locations)
```

Native thread, sender, language, role, signature and `:caused-by` metadata wrap these
payloads using the existing canonical codecs. The root wrapper names the pinned
checkpoint dialect and authenticates its cast. The signed opener binds the scope
and version to independently installed target policy. Root then opener is the
fixed bootstrap. Every later act has **only the opener** as its immediate causal
predecessor. Target frontier addresses and manifest references are signed data,
not companion causal parents. Recipients resolve through the companion cast.
Validate native shapes, roles, fixed causal relation and scope equality on receipt.

`propose` references a canonical manifest descriptor blob; the descriptor contains
exactly `Manifest` from [[SPEC-035-cached-state-checkpoints#CON-3500]], without
requiring a snapshot download to recognize the proposal. A proposer can advertise
an incorrect descriptor; receiving its proposal makes no semantic claim true.
Endorsers retrieve and verify the descriptor, independently derive its target cut,
then obtain the capability in [[SPEC-035-cached-state-checkpoints#CON-3501]]. Native
receipt of `endorse` remains structural/authentic; the signature attests the named
claim under the fault assumption. R7 fold values do not gate native admission.

`publish` advertises an exact certificate blob and optional locations. Any member
can bundle endorsements; none has exclusive collector authority. The verifier
derives `Certified(manifest, policy)` only after checking the pinned threshold of
distinct authenticated members endorsing that manifest in that same companion.
One signer counts once regardless of retries, message identities or transport copies.
No `certify` performative or simple message count can assert that result.

`verify_certificate(context, bytes)` checks the included root/cast identity against
the pinned companion, authenticates/admit-checks its opener, and verifies each
endorsement using that fixed bootstrap. It checks the signed language, thread,
role, recipients, sender identity, sole causal predecessor and exact scope/manifest
binding. Proposal and publication messages are unnecessary for this verification.
It MUST NOT fetch or replay the companion's accumulated history. Missing bootstrap,
wrong opener, cross-thread signature reuse and claimed signers reject. The returned
generic result is `VerifiedAttestations(manifest, signers)`. Producing
`VerifiedSummary` and `PreparedInstall` additionally requires the supported profile,
summary checks, target tail and local-floor obligations in the other contracts.

For example, the same checkpoint dialect can attest a drawing manifest under a
register/set profile and a checklist manifest under another installed profile.
Distinct roots and context/policy/profile hashes keep the assertions separate.
There is no target-specific `drawing-checkpoint` coordination dialect.

Preconditions: independently pinned target/companion binding, installed dialect code,
static policy and bounded native recognition. Postconditions: recognized signed
coordination facts or a portable verified attestation bundle; neither native receipt
nor certificate publication silently installs state. Error categories include
`ForeignCompanion`, `ForeignScope`, `InvalidBootstrap`, `InvalidEndorsement`,
`InsufficientEndorsements`, `MissingDescriptor` and the existing resource errors.
Trace: [[SPEC-035-cached-state-checkpoints#REQ-3500]],
[[SPEC-035-cached-state-checkpoints#REQ-3501]], [[SPEC-035-cached-state-checkpoints#REQ-3502]],
[[SPEC-035-cached-state-checkpoints#REQ-3514]], [[SPEC-035-cached-state-checkpoints#TEST-3517]].

### CON-3505: Immutable evidence roots and bounded host ownership

The durable host uses an immutable content-addressed AVL evidence index keyed by
native identity and original signed-wire digest. Values reference original signed
message blobs. Cloning a view shares its root; warm retention inserts only the
candidate's newly supplied records into the previous root. Persistence writes new
values and copied index paths, then atomically replaces the generation record.
Already durable index roots use metadata-only lookups. Reading every retained body
to preserve it is prohibited on the opening path. Cold archive recovery is a
separate, explicitly bounded operation.

The local index grammar uses the binary primitives in
[[SPEC-035-cached-state-checkpoints#CON-3500]]:

```text
link = byte(0) | byte(1) h32
EvidenceNode = literal("cbcl/checkpoint/evidence-node/v1")
               bytes(native-identity) h32(wire-digest) h32(message-blob)
               link(left) link(right) u32(height) u32(size) u64(recovery-bytes)
```

Recognition checks exact framing, node addressing, strict key order, AVL height and
balance, size/recovery accounting and each original message's authenticated identity.
The local profile bounds individual nodes at 1,024 bytes, native messages at
256 KiB, the tree at 1,000,000 records and total recovery bytes at 256 MiB.
Persistence MUST refuse an index that its recovery profile cannot recognize;
capacity exhaustion MUST NOT erase evidence.

A generation is a closed canonical JSON object with fields `version=1`,
`generation:uint64`, `context:h32`, `coverage:h32`, `summary:byte-array`,
`frontier:array<native-identity>`, `evidence_root:null|h32`,
`outbox:map<string,byte-array>` and `retry:map<string,uint64>`. Hashes use arrays of
exactly 32 unsigned octets. A frame is its domain-separated generation digest
followed by the exact UTF-8 JSON bytes. Unknown/duplicate fields, noncanonical
encoding, invalid profile data, oversized frames and torn digests reject before
serving state. One OS-fenced writer owns each directory. Temporary generations are
unacknowledged data; old temporary names cannot prevent a recovered writer advancing.

`DurableClient::prepare` and `prepare_bounded` capture that instance's actual
generation and complete floor. A private store-instance binding prevents attaching
a stale or foreign client's floor to a current generation. Installation checks both
that binding and the captured generation/floor. The client is exposed read-only;
accepted edits, evidence, outbox and retry changes use generation-fenced durable APIs.

Interactive validation runs in bounded owned workers. Timeout discards only the
uninstalled result; late validation cannot install state. An owned commit worker
retains the exclusive durable writer while an OS write is outstanding. Its initial
wait shares the prepared operation's deadline. The result is completed, explicitly
uncertain with a retained handle, or recovery-required; timeout MUST NOT claim an
in-flight commit was undone. Any ambiguous persistence error stops further writes
through that instance until recovery. Test fault points cover write, sync, rename
and directory sync, not only a successful append.

Trace: [[SPEC-035-cached-state-checkpoints#REQ-3506]],
[[SPEC-035-cached-state-checkpoints#REQ-3507]], [[SPEC-035-cached-state-checkpoints#REQ-3508]],
[[SPEC-035-cached-state-checkpoints#NFR-3500]], [[SPEC-035-cached-state-checkpoints#NFR-3502]],
[[SPEC-035-cached-state-checkpoints#TEST-3518]].

## Performance and observability

### NFR-3500: Opening work follows state and tail, not the covered prefix

The enabled checkpoint path MUST perform zero covered-prefix message replay
and zero accumulated companion-history replay.
Its work is bounded by certificate/summary size, signatures, frontier/floor size,
tail size and authenticated query proofs; live state and concurrency are explicit
size parameters. It MUST NOT claim history-independent total space.

Depth acceptance uses controlled histories of 600, 6,000 and 60,000 accepted messages with
fixed live output, frontier and two-message tail, identical policy and warm local
cache and one fixed installed dialect across those history sizes. State-bearing
edit count and protocol declaration size are reported separately; a finite
nonrepeat chain of distinct acts is a valid covered-message workload. Covered-prefix
scans and replay remain zero. Bounded old-parent openings explicitly named by
new tail steps are measured separately and remain permitted. On the same recorded reference host,
median open CPU at the largest history is at most twice that at the smallest;
byte totals report certificate, tail, openings and floor separately. This is a
provisional engineering target to ratify on native and browser hosts, not a result
established by the existing 600-edit probe. End-to-end timing includes all decode,
verification, admission, floor checks and durable installation; fetch time and
render time are additionally reported separately, never silently excluded.
Trace: FM-3500; [[SPEC-035-cached-state-checkpoints#TEST-3514]],
[[SPEC-035-cached-state-checkpoints#OBS-3500]].

### NFR-3501: Publication amortizes ordinary admission work

Steady-state accepting and publishing a delta MUST NOT rescan all covered messages
or clone the complete retained archive. Persistent summary/index updates share
unchanged structure; proposal freeze is independent of historical body count.
Initial reconstruction and an old-cut request without an anchor are separately
labelled background work. The same fixed-output benchmark MUST record message
visits per delta and prove that appending 32 acts to a maintained current cut performs
no scan or replay of old messages. Finite lookups of explicitly named dependencies
are permitted and counted separately. Report admission cost, summary maintenance, cut
freeze, independent endorsement, upload and durable publication separately.
Trace: FM-3502; [[SPEC-035-cached-state-checkpoints#TEST-3515]],
[[SPEC-035-cached-state-checkpoints#OBS-3501]].

### NFR-3502: Bound unsuccessful opening and preserve responsiveness

Each host MUST enforce the local operation budgets in
[[SPEC-035-cached-state-checkpoints#CON-3500]], including failed fetches and
verification attempts. The 5,000 ms default is provisional: the host conformance
test injects a stalled provider and requires cancellation plus a terminal response
by that deadline plus one documented scheduler quantum. Existing editing/state
access remains usable during staging. Publication cadence and catchup delay are
reported as distributions; no bounded global freshness/liveness claim is made in
an asynchronous network with unavailable quorums or archives.
Interactive native hosts use the bounded validation and owned-commit runtime in
[[SPEC-035-cached-state-checkpoints#CON-3505]], sharing the original operation
deadline across phases. Slow cryptography is bounded by worker isolation as well
as per-message work limits. A potentially completed OS commit cannot be cancelled
as though it never happened: deadline expiry returns an explicit uncertain outcome
and retains the writer fence until completion or recovery. The preceding verified
view remains available; the new generation is not acknowledged installed early.
Trace: FM-3502; [[SPEC-035-cached-state-checkpoints#TEST-3516]],
[[SPEC-035-cached-state-checkpoints#OBS-3500]].

### OBS-3500: Opening diagnostics

Emit operation/candidate outcome, reason code, context/profile version, certificate
signatures checked, bytes by category, dependency queries, proof paths, tail steps,
covered-prefix body reads, budget consumed and decode/verify/admit/floor/commit/fetch
durations. Use opaque local correlation IDs; do not log message contents or signing
material. These signals cover every opening requirement linked above.

### OBS-3501: Publication diagnostics

Emit target and companion scope digests, recognized coordination act kind,
distinct endorsement count and profile-authorization/certificate outcomes.
Emit accepted-to-published cut lag, pending age, maintained-index work, body visits,
proposal/endorsement CPU, available endorsements, decline reasons, storage outcomes
and last successfully advertised blob. Separate lack of agreement on an exact cut
from lack of provider availability. Signatures prove neither recency nor retrievability.

### OBS-3502: Installation and recovery diagnostics

Emit captured/committed generation, floor-head count, missing floor-head count,
retained-evidence/outbox counts before and after, compare-and-swap conflicts, durable
commit outcome, recovery outcome and runtime mode. Monitor event ordering using
finite-trace assertions: always `InstallCommitted(g)` implies a preceding successful
`FloorChecked(g)` and `DurableGeneration(g)`; always `CandidateFailed(g)` implies
no installation of that candidate. These event predicates are fields of this
observable; deadline assertions use elapsed milliseconds from
[[SPEC-035-cached-state-checkpoints#OBS-3500]]. A host test monitor evaluates them;
no distributed termination proof is implied.

## Acceptance tests

These are specified obligations, not assertions that the research tests already
implement them. Core tests need only native fixtures and an injected store/clock;
depth tests require fuzzing, platform adapters or the scaling rig. The kernel
maintainer owns core implementation; the performance/platform maintainer owns depth
evidence. Each row includes intended behavior, hostile input and a forbidden result.

### TEST-3500

Core. Pinned context accepts; change dialect/cast/roster/profile under the same root and reject before installation; provider roster cannot lower threshold. Reject a profile whose identities do not commit full content. Signed same-identity/different-parent and different-payload substitutions cannot pass identity checks.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3500]].

### TEST-3501

Core. Ahead member signs exact older cut; unknown or rejected ancestor declines; copied proposer root, wrong summary and redundant frontier expose no signing request. Importing a valid certificate alone cannot unlock signing it or its descendants, including after restart; independent reconstruction restores eligibility.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3501]].

### TEST-3502

Core. Three-of-four cached native endorsements open with all signers offline;
two distinct endorsers, duplicate signer, forged native signature, changed summary
and well-addressed forgery reject; signature bypass mutation fails.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3502]].

### TEST-3503

Core. Register/values/set composition matches full fold for every prefix, duplicates, permutations, late replacements and concurrent branches; malformed/conflicting identities reject; delete suppression or duplicate guard mutation fails.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3503]].

### TEST-3504

Core. Continue using signed covered predecessors; missing dependency is pending; validly signed wrong-position message, forged field, wrong-root/absent opening and omitted required query cannot become accepted; native causal guard bypass fails.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3504]].

### TEST-3505

Core. Old base plus tail reaches local floor; old base alone or one missing concurrent branch refuses; huge advertised revision cannot remove a local accepted edit; absent-proof guard mutation fails.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3505]].

### TEST-3506

Core. Covered replay preserves supplied original bytes; warm rebase preserves superseded signed bodies without resupply, pending outbox and later equivocation detection; successful install cannot reduce retained evidence; retention deletion mutation fails.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3506]].

### TEST-3507

Core. Missing/corrupt latest blob falls back; single-step byte overflow and independent step-count overflow reject before expensive work; repeated failed candidates exhaust cumulative budget; FIFO/symlink/stalled provider cannot monopolize opening.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3507]].

### TEST-3508

Core. Fault injection at generation write/commit/recovery returns old or new complete state with matching floor; local edit during staging causes compare-and-swap retry. Independently inject evidence receipt, outbox enqueue and retry-status changes without a new accepted edit; all conflict or survive transactional restaging. Failed candidate changes no installed state, evidence or outbox.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3508]].

### TEST-3509

Core. Certify two incomparable cuts with overlapping honest endorsers; merge their tail normally; offline fourth member does not block three signatures; neither certificate rejects the other fork or releases resource rights.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3509]].

### TEST-3510

Core. A compatible installed profile enables; a clause requiring an unsupported
separate feature, such as an unavailable global-fan-in witness, disables whole
bootstrap. Unknown profiles cannot expose partial state or mint resource evidence.
Counts, progress and resource heads are required by v2 and tested by
[[SPEC-035-cached-state-checkpoints#TEST-3520]] through
[[SPEC-035-cached-state-checkpoints#TEST-3525]].

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3510]].

### TEST-3511

Core. Stored blob retrieves by exact identity; substitute another valid certificate under its hash, fail durable store, or fail advertisement; no false publication acknowledgement, old cache remains and editing continues.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3511]].

### TEST-3512

Core. Fresh client reports certified cut; target-covered status needs actual proof; stale but valid cut cannot claim global latest; missing target/forged timestamp cannot promote status.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3512]].

### TEST-3513

Core. Off uses ordinary path; shadow compares without installation; enabled obeys profile gates; disable preserves installed floor/evidence; unavailable replay archive reports missing data rather than resetting state.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3513]].

### TEST-3514

Depth. Fixed-output/width 600/6,000/60,000 histories measure full open phases, bytes and body-read counters; archive-iteration mutant fails even if latency is noisy; broad concurrency/output-growth cases report actual growth separately.

Validates: [[SPEC-035-cached-state-checkpoints#NFR-3500]].

### TEST-3515

Depth. Maintained current cut publishes 32 new acts without scanning or replaying
the old prefix. Explicit causal dependency lookups are counted separately. Compare
independently maintained member roots with the full replay oracle outside timing;
forced whole-prefix recomputation fails the work counter.

Validates: [[SPEC-035-cached-state-checkpoints#NFR-3501]].

### TEST-3516

Depth. Cancel stalled fetch and expensive invalid candidates within deadline plus declared quantum; fuzz all closed grammars for truncation/length/duplicate/trailing input; no allocation from unchecked declared length, state mutation or UI starvation.

Validates: [[SPEC-035-cached-state-checkpoints#NFR-3502]].

### TEST-3517

Core. Use the same checkpoint dialect code for two distinct target dialects/profile
bindings. Native proposal receipt with a wrong summary does not certify it. A
managed signer refuses a manually constructed endorsement without a matching
profile capability and refuses changed bytes after authorization. Duplicate
endorsements from one signer count once. Cross-target, cross-companion, changed
policy/profile, wrong-role, wrong-language and wrong-opener endorsements reject.
Any member can publish a valid bundle; an accepted `publish` containing an invalid
bundle cannot certify or install state. Verify a valid certificate with only its
bootstrap and signed endorsements, absent proposal/publication messages and absent
companion history. Increasing companion history must not cause history reads.
Unknown-profile attestation verification can succeed while installation returns
`UnsupportedProfile`. Guard mutations for scope, distinct signers and authorization
must each be detected independently.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3514]],
[[SPEC-035-cached-state-checkpoints#REQ-3501]], [[SPEC-035-cached-state-checkpoints#REQ-3502]],
[[SPEC-035-cached-state-checkpoints#NFR-3500]].

### TEST-3518

Core. Attempt foreign-store preparation with equal generation and frontier but
different retained evidence; reject installation without losing evidence. Exercise
write/sync/rename/directory-sync failures, old temporary files, exclusive writer
recovery, and evidence/outbox/retry changes without accepted edits. Verify that warm
installation writes only new evidence/index paths and never rereads the retained
prefix's bodies. Slow providers and cryptographic callbacks return within the
foreground budget; stalled commits return uncertainty while retaining the writer
fence, then expose their actual durable result. Shadow comparison uses independent
native admission and cannot install a mismatching or unexamined candidate.

Validates: [[SPEC-035-cached-state-checkpoints#CON-3505]],
[[SPEC-035-cached-state-checkpoints#REQ-3506]], [[SPEC-035-cached-state-checkpoints#REQ-3508]],
[[SPEC-035-cached-state-checkpoints#REQ-3513]], [[SPEC-035-cached-state-checkpoints#NFR-3502]].

### TEST-3519

Core formal gate. Kernel maintainer: build `LeanCbcl/CheckpointSummary.lean` and
`LeanCbcl/CheckpointCompact.lean` with the repository's pinned Lean toolchain;
record exact theorem names, source bindings, commands, exit codes and transitive
axiom reports. Check the compact row invariant and native-kernel instantiation,
compact uniqueness/ambiguity and recognized-clock maximum lemmas, then the complete
supported-clause render/advance theorem. The theorem quantifies over coherent
already-admitted histories and tails without assuming its own correctness.

Independent reviewer: inspect the computational summary fields and theorem
hypotheses. Reject whole-history storage/refolding, a redefined reference fold,
`advance-is-correct` premises, placeholders, custom axioms, unsupported-rule omission,
or proof terms containing `sorryAx`. Any standard Lean foundational dependencies
must be visible in the recorded audit. Until this review and all bridge checks pass,
status remains formal verification in progress.

Bridge owner: derive parity vectors independently from the unchanged native kernel,
not from the summary under test. Compare Rust summary transitions and rendering
with the typed model for each supported rule and composed clauses. Include duplicate
identities with normalized signature variants, scoped/cross-scope replacements,
late suppressed delivery, non-state arrival pruning pending references, and removal
of an LWW winner revealing a live loser. Counterexamples must catch disabling
suppression, duplicate protection or pending pruning. Record extraction/encoding,
admission and cryptographic assumptions separately; do not claim that these tests
or the Lean theorem formally verify the Rust implementation.

Validates: [[SPEC-035-cached-state-checkpoints#REQ-3515]],
[[SPEC-035-cached-state-checkpoints#REQ-3503]],
[[SPEC-035-cached-state-checkpoints#REQ-3510]],
[[SPEC-035-cached-state-checkpoints#CON-3502]].

### TEST-3520

Core. Runtime/kernel conformance owner: exercise every head enumerated in
[[SPEC-035-cached-state-checkpoints#REQ-3516]], both alone and in valid finite
compositions. Check exact Rust enabled-head/typed Lean/native head correspondence;
a deliberate omitted or extra enabled head must fail the checker. Distinguish
separately gated domains/global `All` from head support. Run previous bounded
open/persistence, fork floor, signed-evidence and hostile-cache regressions with v2;
unknown separate features must refuse whole bootstrap, never expose partial state.
Validates: [[SPEC-035-cached-state-checkpoints#REQ-3516]].

### TEST-3521

Core. Projection/derived-field owner: compare native ordinary folds with v2 resumes
for events carrying large irrelevant payloads but identical selected projections;
assert summary records contain only identity, signer and selected value, not bodies.
Measure encoded projection growth against growing event output, without claiming
constant space. Check Histogram/Sum with earlier valid sources, invalid source kinds,
forward references, clause-order changes, duplicates and scoped/late replacements.
Mutations dropping projected signer/value, using full bodies, or reordering fields
must be caught by the relevant independent assertion or parity vector.
Validates: [[SPEC-035-cached-state-checkpoints#REQ-3517]].

### TEST-3522

Core. Native admission owner: resume progress and verified positions from a
checkpoint, then admit valid and invalid R5 tails through the ordinary verifier.
Include repeated protocol positions, forks, stale maxima, duplicate acts and absent
position facts. Compare rendered progress and verdicts with full native replay;
mutating the position witness or bypassing R5 must change a targeted test result.
Failures must preserve the prior durable generation and request missing facts explicitly.
Exercise native-colon protocol IDs alongside state-wire coverage aliases; nonzero
progress and valid/invalid next-position verdicts must agree with the actual native
full-history store. A dash-indexed baseline that misses colon predecessors must fail.
Validates: [[SPEC-035-cached-state-checkpoints#REQ-3518]].

### TEST-3523

Core. Resource native-port owner: compare materialized projected facts and resumed
fold/verdicts with the actual native verifier in legacy core, Collective and Quorum
modes. Include valid authorities, missing agreements, bad authority, wrong fact tags,
faults and duplicates. A valid state certificate with invalid resource authority
must fail exactly the native resource boundary. The typed factorization proof and
parity vectors must distinguish verified facts from unverified input classification;
mutating a tag/authority check must be observed independently of checkpoint quorum.
Exercise both address spellings for opener ancestry, `prev` and `deps`, including
late known dependencies and role casts. Native full-fold and projected observers
must produce the same ready/pending/fault classification without expected-value repair.
Validates: [[SPEC-035-cached-state-checkpoints#REQ-3519]].

### TEST-3524

Core. Codec/host owner: bind [[SPEC-035-cached-state-checkpoints#Profile v2 wire grammar]]
and publish canonical vectors
for each row/projection/position/resource variant. Generated canonical seeds covering
all row tags are executable vectors; the release evidence MUST distinguish these
from any separately saved cross-language byte-vector artifact. Exercise truncation, hostile
lengths, unknown variants, duplicate and unordered entries, trailing data, schema
mismatch and v1/v2 cross-decoding. Recognized values must roundtrip exactly; malformed
input must fail before state use. Retain byte/step/time budgets, immutable snapshot
preparation and bounded durable delta writes under growing projections. A budget or
version-binding bypass must be caught by its own targeted negative case.
Validates: [[SPEC-035-cached-state-checkpoints#REQ-3520]].

### TEST-3525

Core formal gate. Kernel proof owner: run the pinned trust-zero Lean checker over
the all-head theorem and ordered-clause/position/resource-factorization lemmas;
record exact declarations, source hashes and transitive foundational dependencies.
Bind reference histories to accepted native identity normalization; include
independent members admitting singleton-recipient and other canonical aliases in
different orders and require equal v2 roots while retaining each original wire body.
Independent reviewer: reject missing heads, custom axioms, placeholders, whole-body
history caches, circular render/reference definitions, assumed advance correctness
and unreported native-port assumptions. Bridge owner: derive independent native
vectors for every head and composition, projections, progress/R5 tails, all resource
modes/faults, duplicates, pending pruning and winner removal. Semantic proof mutations
must reject in actual theorem proofs; runtime mutations must fail executed targeted
tests, not merely fail compilation. Bind model/runtime/inventory/adapter sources and
state the extraction/codec/admission/crypto boundary. Historical v1 evidence is kept
separately. No implementation-complete claim until all v2 gates pass independent review.
Validates: [[SPEC-035-cached-state-checkpoints#REQ-3521]],
[[SPEC-035-cached-state-checkpoints#REQ-3515]].

## Purity Boundary Map

Native dialect: coordination shapes, roles, fixed causal protocol and signed claims.
Pure core: context/manifest hashing, native endorsement/bootstrap verification,
profile endorsement authorization, coverage checks/updates, summary
validation/render/advance, admission queries and floor verification.
Effectful shell: native key custody, archive/cache retrieval, deadlines, scheduler,
durable generation commits, advertisements and metrics export. Dependencies point
from shell to core. Public typed contracts above carry recognized input and prepared
output; network or filesystem callbacks do not execute inside pure validation.

## Evidence and delivery boundary

The performance goal is to avoid replaying covered message bodies while preserving
the state kernel's semantics. Research prototypes informed the design; they are
not production components or normative acceptance evidence. Reproducible native
fold/admission tests and the typed continuation proof govern acceptance.

Delivery order is the bundled native checkpoint dialect, binding/bootstrap and
endorsement-capability vectors; native profile vectors and summary laws; incremental
member publication; durable client staging/floor/evidence; host discovery/fallback;
then shadow-mode scaling/platform evidence. The executable [IMPL-027 plan](../plans/IMPL-027-cached-checkpoints.spl)
traces the implementation tasks to core and depth tests.
User authorization covers local implementation and verification. Completing this
specification does not activate checkpointing in existing applications. Native
admission and resource authority remain unchanged; consumers opt in explicitly.

## Implementation and validation

### Profile v2 local acceptance

Profile v2 implements every native head in
[[SPEC-035-cached-state-checkpoints#REQ-3516]], with projected semantic rows,
ordered derived-field rendering, verified protocol metadata and native resource
facts. The local all-head workspace, codec/host regressions, guard mutations,
trust-zero proof checks and independent parity/review gates passed for the
recorded source trees. Recorded results, reproduction commands and limitations are in the
[acceptance guide](../proofs/cached-checkpoints/README.md). Detailed machine reports
and logs are generated locally rather than committed.
The pre-cleanup workspace run passed 1,739 tests with 36 ignored and no failures;
that count includes the subsequently removed research-only prototype. After
artifact/prototype cleanup, the workspace passed 1,692 tests with the same 36
ignored. Strict workspace Clippy, formatting and the proof checker passed again;
the original no-std WASM result applies to the unchanged runtime sources. The current
mutation runs killed all 17 compiled guard mutants and all eight summary mutants.
The all-head bridge compared 7,392 rendered observations across 231 cuts, all native
heads and both execution paths; its three typed semantic controls executed and
diverged as intended. The separately reviewed
[resource-policy sidecar](../scripts/check-checkpoint-resource-ports.py)
compared native fold, decoded/resumed Summary and independent Lean fault ports for
installed legacy Collective/Quorum policies without source drift. This transports
the native legacy fault boundary; it does not establish resource finality or a
universal classifier refinement theorem.

These results preserve the bounded opening/persistence, local floor, immutable
preparation and signed-evidence lifecycle; they do not activate checkpointing in
consumers or grant resource authority.

`CBCL.CheckpointAll.render_advance_checkpoint` derives the render/advance law
from concrete compact updates and sufficient-state invariants.
`render_advance_wellformed_clause` covers every native well-formed domain-free
ordered clause and connects its resolved fields to the existing native
`compileClause` and `evaluateFields`. Position-resumption and resource-fact
projection endpoints retain their explicit native extraction/classifier ports.
No resource finality, signature verification, Rust extraction/serialization or
host durability claim is inferred from the typed Lean theorem. Domain filtering
and global `All` remain separately gated features.

The current [v2 wire vectors](../test-vectors/checkpoints/v2-wire-vectors.json)
contain canonical records and nested offsets spanning the all-head profile and
all typed row variants. The independent all-head Rust/Lean bridge and counterexamples
are recorded separately from historical v1 vectors. Recognition proves closed
structure and canonical bytes, not snapshot truth or native authority.

The projection-size fixture uses 2,000 event records: original native signed bodies
occupy 10,296,890 bytes and the projected summary 184,942 bytes, a 55.68× ratio.
This compares that fixture's representation sizes; it measures neither full native
admission nor end-to-end opening latency. Event output and selected facts can grow,
and no constant-space or current all-head latency claim follows from this ratio.

### Earlier profile

The earlier seven-head proof remains a dependency of the all-head composition,
not a separate runtime profile. Its independent Rust/Lean test generates its
corpus at execution time. Intermediate benchmark captures, raw literature
snapshots, prototype code and review transcripts are not part of the deliverable.
Earlier measurements do not establish current all-head latency or platform
acceptance. The [validation guide](../proofs/cached-checkpoints/README.md) records
checked scope and reproduction commands.

## Open work

- Kernel proof maintainer: preserve the all-head v2 proof, native position and
  resource-fact factorization boundary under
  [[SPEC-035-cached-state-checkpoints#TEST-3525]], alongside the historical v1 proof. Universal Rust
  extraction, codec/canonicalization refinement and protocol/cryptographic
  refinement remain separate work; bounded parity does not discharge them.
- Protocol owner: ratify static roster/fault policy for each deployment. Member
  reconfiguration, compromised-key revocation and cross-context migration require
  an explicit transition protocol; silently treating a newer roster as trusted is
  forbidden. The initial version uses an immutable installed policy.
- Dialect maintainer: maintain the standard definition and installation vectors
  from [[SPEC-035-cached-state-checkpoints#CON-3504]], including the exact native
  wrapper encodings, companion binding and managed-signer capability integration.
  Bundling the dialect does not authorize a new R7 admission gate.
- Kernel maintainer: preserve the implemented native-address binding, closed codecs,
  Merkle vectors and continuation/admission equivalence suite. Profile v2 aggregates,
  progress, resource counters and repeat-position resume remain subject to their
  source-bound acceptance gates on every change. Domains and global completeness witnesses remain explicit
  separate-feature gates where unnecessary for all-head support.
- Performance maintainer: ratify publication defaults, per-open limits and reference
  hosts using the depth tests. Measure proof generation and archive/provider storage,
  not only client verification. No constant-storage promise follows from compaction.
- Host maintainer: specify a retained archive/provider availability policy and durable
  generation storage adapters for each additional platform. The native reference
  adapter is implemented; the protocol handles unavailability explicitly; it
  does not guarantee that an arbitrary old cut remains reconstructible forever.
- Security/domain reviewers: review endorsement trust, native signature/identity
  binding, rollback assumptions, side channels and deployment modes before production.
  Same-model design review is useful local feedback, not that release approval.

## Reading paths

- Stakeholder: Orientation → named failures → requirements → performance targets.
- Reviewer: decisions → local-floor argument → contracts → open work.
- Implementer: contracts → acceptance test rows → linked requirement → observables.

## Changelog

- 0.5.0 (2026-11-07): user-authorized all-head Profile v2, projected events,
  ordered derived fields, verified protocol-position resume and materialized native
  resource facts, closed versioned codecs and full typed continuation/parity gates.
  Complete local implementation and typed formal acceptance with independent
  parity/review and current source-bound checks. Preserve v1 proof and benchmark
  results as historical evidence; retain bounded persistence and explicit native-port boundaries.

- 0.4.0 (2026-11-07): implement a non-circular compact-summary continuation proof
  against the existing typed native kernel, full supported-rule composition,
  transitive proof-assumption audit and independent Rust/model boundary vectors.
  Formal verification remains in progress pending the new acceptance gate.
- 0.3.0 (2026-11-07): integrate the current typed-HLC state kernel; specify immutable
  installed contexts, signature-normalized summaries, persistent evidence roots,
  store-bound preparation and bounded validation/commit uncertainty. Distinguish
  covered-message scaling from state-edit count and explicit dependency lookups.
- 0.2.0 (2026-11-07): use one built-in checkpoint companion dialect for native
  proposals, endorsements and publication; retain portable native endorsement
  bundles, profile-authorized signing and history-free certificate verification.
- 0.1.0 (2026-11-06): specify reusable checkpoint certificates, verified continuation,
  durable local-history preservation, bounded fallback and incremental publication.
