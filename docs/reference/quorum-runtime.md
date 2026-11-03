---
title: Quorum runtime API
mode: reference
---

# Quorum runtime API

`cbcl_core::quorum` implements the consensus-free bounded-counter safety protocol
specified by [[SPEC-031-unified-quorum-dag]], with the account-owned lifecycle in
[[SPEC-033-owned-counter-lifecycle]]. Its public types use `alloc`;
optional `serde` supports typed transport and journal serialization. Parsing and
allocation limits belong at the host's wire boundary before constructing these types.

## Context and defaults

`Context::from_instance(&instance, field, instance_validators, &auth)` validates the
selected quorum rule, authenticates genesis, reconstructs its cast, and pins the
canonical dialect, thread, root, opener, resource field and committee. Existing
uncertified history contributes no capacity or balance. The context owns genesis
and dialect data. Certificates from another context cannot be replayed into it.

| Declaration | Resolution |
|---|---|
| No certification clause / `host-gate` | Existing `escrow::issue` host gate |
| `quorum-budget` | Require authenticated instance roster |
| `quorum-budget (validators @v0 @v1 @v2 @v3)` | Pin dialect roster, infer `f=1` |
| Explicit `(faults f)` | Check exact `n=3f+1`; quorum always `2f+1` |

Roster order canonicalizes. Duplicate or malformed members reject. An explicit
instance roster must match an explicit dialect roster. Validators are never inferred
from holders, balances or caller request fields. The single-validator `f=0` profile
is valid mathematically; it tolerates no Byzantine validators.

## Host authentication and persistence

Implement `Authentication` with these independent responsibilities:

- `authenticate_act(act)`: verify the owner's real signature and normal CBCL
  protocol admission, including authenticated sender/wrapper semantics.
- `verify(key, preimage, signature)`: authenticate a vote using the pinned key.

A wrapper named `signed` does not satisfy either responsibility. The core rebuilds
act identity and separately checks context, closed shapes, duplicate parameters,
owner roles, issuer authority, accounts, positive amounts and compiler evidence.

Implement `Journal` per `(context ID, validator key)`. `load` returns the entire
acknowledged log or `None` only for a previously unused identity. `append` atomically
creates that identity when `expected=None`, or appends when the existing event count
matches `Some(sequence)`. A failure must mean no append occurred. The acknowledged
log must survive crashes without truncation, rollback, forks or lost history. Shared
processes using one validator key must use this same storage namespace and atomic CAS.
Do not initialize the same previously used key against an empty replacement store.

`Replica::initialize` creates once and refuses existing logs. `Replica::recover`
replays all typed events through semantic guards and rechecks received signatures;
it never trusts a deserialized balance or counter. Events contain complete acts and
proofs. Recovery has no clock, timeout unlock, or signing-budget reset. Signature
verification and act admission must remain deterministic for the pinned instance.

Every mutation is validated into an owned local update, then its original event
is appended atomically before that update is applied or a signing request exposed.
Storage/CAS failure leaves the previous state untouched and returns no request. Retrying a durable vote returns the same preimage.
Physical durability is a host obligation, not a property of an in-memory test log.

## Transaction and certificate operations

| API | Meaning |
|---|---|
| `intend(instance, owner, verb, fields, nonce)` | Shared CBCL binder, adding epoch, dependencies and nonce before owner signing |
| `register(act, journal, auth)` | Authenticate and retain a candidate; missing dependencies reject for fetch/retry |
| `prepare_operation(id, journal, auth)` | Enforce local epoch, phase and budget/owned slot; persist before returning signing bytes |
| `receive(certificate, journal, auth)` | Verify every distinct member signature and complete local prerequisites |
| `prepare_effects(id, journal, auth)` | Require operation QC and no local cancellation fence |
| `prepare_cancel(owner_request, journal, auth)` | Verify owner request, require no prior local effects vote, persist fence |
| `release(id, journal, auth)` | Require own recorded charge plus cancellation QC; retain all evidence |

The caller externally signs the complete message returned by `intend`, then submits
its authenticated `Act`. Caller-supplied `escrow-prev`, `escrow-deps` and
`escrow-nonce` reject. The nonce is a nonempty string of at most 256 bytes, supplied
as the explicit API argument. Reuse it for retries; choose a different nonce for a
new identical payment. Epoch changes also change transaction identity.

`SigningRequest::preimage()` supplies exact bytes to the external signer;
`attach(signature)` creates an untrusted `Vote`. Assemble a `Certificate` with its
kind, payload ID and member votes. Receipt checks actual signatures, context, kind,
payload and distinct-member quorum; constructing the struct confers no authority.
An operation QC is pending capacity. Effects QC is finality for that operation.
Effects and cancellation QCs cannot coexist under the honesty assumption.
Conflicting genuine certificates return an explicit error; they are never resolved
by choosing a hash or arrival order. Treat that error as a violated assumption.

`Context::cancellation_request(owner, id)` supplies separate owner signing bytes.
Cancellation does not introduce a business `extend` message or bypass normal act
signing. No private key or signing algorithm is embedded in the runtime.

## DAG versions

`(certification quorum-budget ...)` always selects consensus-free multi-parent DAG
adoption. `Context::from_instance` derives the runtime from that declaration. The
host supplies cryptography, transport and durable storage, not a handoff protocol.
There is no handoff option, legacy checkpoint API or old-log migration.

```text
        A --\
       /     \
root          M --> N
       \     /
        B --/
```

| API | Meaning |
|---|---|
| `version_snapshot(account)` | This scope's active/visited/known versions and complete own-origin journals |
| `draft_version(parents, held, refunds, credits)` | Derive scope from parents, union cumulative sets and recompute exact books |
| `Context::version_request(manifest, actor)` | Version authorization bytes for the actual eligible actor (not permanent seal intent) |
| `receive_version(DagVersion, journal, auth)` | Verify actor, parents, rank, inherited sets, exact books and real credit/refund QCs |
| `adopt_version(id, journal, auth)` | Require current scope's active version among parents and its full signature history held |
| `version(id)` | Fetch retained verified metadata for relay |

An account version is authorized by that account's actor. A collective version is
authorized by an eligible operation actor, never by the pool identity. A host gathers
candidate histories, drafts a covering manifest, externally signs its authorization
request and relays the version. Each validator adopts independently. Receipt makes
metadata known without activating it. Concurrent DAG updates need no version quorum.
Owned roots require the separately authorized seal quorum described below.

The target must include every historical signature from its resource scope,
including released and zero-cost IDs. Signatures from other accounts do not become
this account's debit obligations. Parents and held operations must share the target
scope; verified incoming transfer credits can originate in another account.
Changing the actor within a collective pool does not change the scope or budget.
Adoption preserves all machine evidence, including other accounts' histories.

The accounting equation is independently checked for rights and headroom:

```text
allocation = genesis + unique cumulative final credits
                     - unique cumulative held costs
                     + unique cancellation-backed refunds
```

Parent allowances are never added. Over-reserved branches need refunds or adequate
verified credits before they can produce a funded join. Cancellation continues to
require the original transaction actor. Missing history blocks an adopter; there is
no timeout unlock or consensus fallback. These are concurrent DAG constraints;
account completion uses the separate correct-owner lifecycle below.

`VersionManifest::rank` exceeds every parent rank and every held operation's source
rank. Drafting computes the smallest such label; callers can choose a larger rank
before reauthorizing. Siblings can share rank. This is not a global transaction
order. The version ID binds scope, context, parents, rank, sets and allocation.

Versions use the same prepared update, atomic append and guarded recovery as votes.
Recovery recognizes only current typed events; removed legacy event/vote variants
reject during decoding. Cached signing and same-active-version adoption retries
stutter. Old version receipt never resets the active version.

## Queries and limits

`finalized_view` returns known-final IDs, pending operation IDs, rights, optional
headroom, value and an evidence digest. `value()` renders `status: finalized-view`
and `completeness: unknown`. This is a dependency-closed local certificate view;
it is neither a complete latest balance nor guaranteed immediately signable capacity.
The digest commits the context and final operation set, not a quorum-signed balance.
`fold_instance` overlays this selected field on the normal state fold. Generic
stateless parser/WASM/FFI folds remain fail closed for quorum counters.

`operation_act`, `certificate` and `version` return retained evidence for host
fetch/relay protocols. They never synthesize signatures or completeness claims.

`Limits::default()` admits at most 4096 candidates, 1024 DAG versions, 65536 journal events, 1 MiB per operation object, and 8192 bytes per signature.
The typed message traversal also enforces a depth ceiling of 64 before recursive
canonicalization. Cardinalities and known-ID checks bound certificate/report inputs.
The host can choose stricter limits and must bound decoding before allocating inputs.
Hitting a limit refuses new work and retains safety evidence. It does not garbage
collect histories, fences, signatures or visited versions. Limit changes on recovery must
still admit the full existing log.

The executable example is `crates/cbcl-parser/tests/quorum_runtime.rs`. It uses
explicit test-only authentication and in-memory CAS journals. Production signing,
transport, nonforking durable journal providers and complete-history read protocols
remain host integrations. Rust/Lean correspondence is tested and reviewed, not
formally extracted or proved.

## Collective pool API

`CounterRule::ownership` defaults to `Ownership::Account`. Collective rules use
`Ownership::Collective`, `(initial open :available)` and no transfer mapping.
`CounterRule::transfer` is now optional: account rules require `Some(tuple)`, while
collective rules require `None`. Existing tuple JSON is compatible with `Some`;
missing serialized ownership defaults to account.

`Context::ownership()` reports the mode. `Context::pool()` returns the reserved
`COLLECTIVE_POOL` resource scope in collective mode. Genesis rejects a cast key
matching that scope. Actor authorization always uses real authenticated signers
and the pinned cast. `Replica::intend` reconstructs public Instance caches before
using the shared binder.

`root_epoch(actor)` and `active_epoch(actor)` resolve every collective actor to the
same pool epoch. They also accept the explicit resource scope for read access.
The resource scope cannot sign transactions, cancellation requests or versions.

`version_request(manifest, actor)` returns signing bytes for an eligible actual
actor. Incoming versions independently recheck authorization. Cancellation always
requires the original transaction signer; a shared balance cannot replace that
signature. `version_snapshot(actor)` resolves the actor to the same pool scope.

`FinalizedView` exposes its ownership mode. Rust `rights` and optional `headroom`
maps contain one pool entry for collective rules. `value()` renders scalar resources
and `ownership: collective`. Final-set digests and unknown completeness retain their
existing meaning. Collective DAG accounting and journals use the same pool scope
across all actors. See [[SPEC-031-unified-quorum-dag]].

## Proof and execution scope

[[SPEC-029-multi-parent-counter-model]] proves the collective numeric DAG protocol.
`MultiParentRustOracle.lean` proves its API adapter generates valid abstract runs.
The adapter names source-metadata registration, own-charge release and durable
retry stuttering. Shared fixtures synchronize verified metadata/certificates;
separate Rust tests cover delayed local receipt. Tests compare real runtime
admission/projected state and recover journals after every shared command.

Account DAG behavior additionally has transfer, headroom, scope isolation, branch
join, late-certificate and recovery tests. It is not newly claimed as formally
refined to the single-pool Lean model. Historical single-parent Lean modules remain
research artifacts and do not select runtime behavior.

Run from repository root:

```sh
python3 proofs/validator-budget/check_rust_multi_parent.py
cargo test -p cbcl-parser --test quorum_runtime
python3 proofs/validator-budget/check_rust_multi_parent_mutations.py
```

This is tested Rust correspondence, not universal source-code equivalence. The
finite catalogue, machine arithmetic and positive-amount/codec limits reject inputs
outside the supported projection. Cryptography, physical journal durability and
network decoding remain host assumptions. Neither unbounded fresh-ID refinement
nor complete/latest balance reads are proved. Current evidence:
[unified-quorum-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/unified-quorum-evidence.md).

## Local execution cost

The runtime validates each event into a small owned update before atomic append,
then applies that update without repeating fallible protocol checks. Rejection,
failed append/CAS and validated retries leave in-memory state unchanged; signing
requests remain unavailable until persistence succeeds. No full-state clone is
needed to implement rollback.

Per-version charge totals are derived from signed/released journal evidence and
updated once on first sign/release. Adoption never resets them. Recovery rebuilds
the cache through the same validated transitions; serialized totals are not trusted.
Debug builds independently recompute the history sum after each applied update.
Read-only checks borrow stored manifests rather than cloning their held sets.

An ignored local probe measures four serial validators, a memory journal and test
authentication. It includes authoring, registration, operation QCs and effects
finality, but no network, real cryptography, fsync, version merges or adversarial
contention. Run with native speed optimization (the workspace release default is
size optimization):

```sh
CARGO_PROFILE_RELEASE_OPT_LEVEL=3 CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_DEBUG=0 \
  cargo test --release -p cbcl-parser --test quorum_runtime \
  multi_parent::in_memory_throughput_probe -- --ignored --exact --nocapture
```

There is no CI timing threshold. Measurements and validation are recorded in
[quorum-local-cost-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-local-cost-evidence.md) under [[SPEC-032-quorum-local-update-cost]]. They do
not establish production TPS; networking, durable writes, real signatures and
history retention limits remain separate costs.


## Account-owned completion lifecycle

Use `OwnerDriver` for the correct logical owner of an account counter. Initialize
its separate `OwnerJournal` before the first issuance; after restart recover that
same journal and retain/fetch validator metadata and evidence. Existing owners must
recover their issuance log rather than initialize an empty replacement. A signing
key shared by independent writers is outside the progress guarantee.

```text
intend draft -> durable enqueue/reserve -> poll -> Publish(exact act)
                                          |
                              head exceeds concurrent envelope
                                          |
                                  freeze new issuance
                                          |
                            retry finite issued batch to effects
                                          |
                    AuthorizeSeal(exact Owned version manifest)
                                          |
                 owner signs VersionRequest + OwnedSealRequest
                                          |
                     validators persist seal -> seal votes/QC
                                          |
                           adopt -> Publish(full allocation)
                                          |
                   effects QC -> next funded Owned version
```

The existing `(certification quorum-budget ...)` declaration selects this protocol;
there is no new dialect keyword or host protocol switch. The driver chooses the
internal lifecycle phase deterministically. Ordinary account DAG APIs remain
available for concurrent metadata, but raw replica calls alone do not implement
the correct-owner progress policy. Collective pools retain their previous
contention behavior and cannot be converted to owned accounts.

`OwnerDriver::enqueue(draft, replica, owner_journal)` takes an unsigned draft built
by `Replica::intend`. It derives resource costs, reserves known-final funds and
rejects changed nonce reuse or overcommitted queues. `poll` exposes `Publish` (act and retained evidence),
`AuthorizeSeal`, `AuthorizeVersion`, `Adopt` or `Idle`. Every issuance and selected
manifest is journaled first. Host signs/relays the exact returned act or manifest and the accompanying
prerequisites;
retries reuse it. Continue polling and relaying evidence until completion. The
driver never cancels issued work. It completes an owned operation before issuing
the next version's operation. Certificates—not acknowledgements or timeouts—release
queue reservations. No timeout reclaims funds.

`VersionManifest::phase` is hash-bound (`Concurrent`/`Owned`, DAG identity v2).
`draft_version` inherits Owned phase from any Owned parent. An Owned root must be
marked Owned before generating either owner authorization. The owner driver
handles this. Owned metadata cannot be adopted or signed before a verified seal
QC; phase downgrade rejects. A `VersionRequest` signature never authorizes a seal.

| API | Meaning |
|---|---|
| `Context::owned_seal_request(manifest, owner)` | Distinct permanent-seal owner signing domain; requires an Owned account manifest |
| `record_owned_proposal(request, journal, auth)` | Verify drained books, both owner authorizations and retain metadata for relay |
| `prepare_owned_seal(request, journal, auth)` | Require active parent and all historical signatures held; persist the unique account seal before returning a validator signing request |
| `receive(OwnedSeal certificate, journal, auth)` | Verify quorum before enabling full-capacity continuation |
| `owned_root(account)` | Verified certificate-derived root, never a caller-supplied mode flag |
| `version_snapshot(account)` | Includes permanent local seal and verified owned root separately |

Full-capacity owned signing requires a descendant of that root, the active version,
cost within every allocation coordinate, and an unused permanent version slot.
Historical fences/cancellation QCs reject, including those recorded before seal
arrival. Owned operations cannot be canceled or released; another distinct operation
cannot reuse their slot. Incoming and self credits require actual effects QCs and
unique cumulative transaction IDs. Rights and optional headroom use the same rules.

Progress assumes at most f Byzantine validators among 3f+1, a correct coherent
owner, reliable eventual delivery, fair honest service, finite draining and available
configured catalogue/journal capacity. It has no clock-bound guarantee and does
not require Byzantine cooperation. Byzantine owners may stall their own accounts.
The Lean model proves abstract safety and conditional progress; selected shared
traces and real-signature/durable-journal tests validate Rust execution. This is
not a universal source/network/filesystem refinement. See [owned-lifecycle-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/owned-lifecycle-evidence.md) for precise proof and correspondence boundaries.


### Protocol-level progress

For a funded account request outside the fractional envelope, `OwnerDriver` stops
new issuance, drains its finite issued batch, obtains an owner-authorized seal QC
and continues with full-capacity versions. Finishing the issued batch requires no
new spending allowance. The driver retries its exact issued acts and never races
them against cancellation. The identified residual-budget and split-cancellation
traps therefore have an explicit avoidance/completion path for a correct owner.

The intended client contract is eventual receipt and verification of an effects
certificate for each funded FIFO request under the conditions above. This includes
spending the entire remaining balance and the final base unit, without Byzantine
votes. A pending certificate is not a deadline-triggered refund or balance reset.

The composed Lean product proves eventual owner-journaled completion for every
accepted request, deriving history, funding, drain and prerequisite readiness from
initialized transitions. Its explicit environmental assumptions are correct durable
ownership, an available honest quorum, retained proofs, fair necessary-job service
and sufficient finite capacity. These product invariants have not been universally
extracted from every Rust `OwnerDriver` execution. Shared traces,
adversarial tests and durable-journal recovery tests provide implementation evidence;
a universal Rust-driver refinement and implementation-wide deadlock-freedom proof
remain open. This boundary concerns the protocol implementation itself, separately
from outages or loss of keys/storage. Collective contention and conflicting owner
issuance remain outside the account progress contract.


### Retained publication and lagging validators

`OwnerAction::Publish(Publication)` contains the immutable issued `act` and its
transitive counter `evidence`. `AuthorizeSeal { manifest, evidence }` includes old
holds/credits and their prerequisites. Host signs the manifest's two distinct owner
requests, then sends `SealPublication { request, evidence }`. Act signing remains
separate: transport must provide the real authentication envelope for **each**
relayed Act, plus any normal CBCL causal/admission evidence required by the host.
An Act cache or a publisher's assertion is not authentication.

`Replica::prepare_publication` imports evidence through the ordinary guards until
it reaches a fixed point. It catches up along a compatible verified ancestry path,
using ordinary direct-parent adoption and complete historical-signature coverage,
then prepares an operation/effects vote. It searches alternative covering parent
paths rather than relying on hash/arrival order. `prepare_seal_publication` similarly
imports the drained batch's actual certificates and catches up to a compatible
seal parent before voting. A root QC also permits forward traversal of its pre-root
ancestors; the certified-root budget guard still forbids new signatures outside the
owned root. No old allowance is reopened.

Responses distinguish pending work from observed completion:

- `Operation(request)` / `Seal(request)`: local decision was durably recorded before
  exposing signing bytes.
- `Effects { operation, request }`: includes the actual operation QC that enabled
  this effects vote. Relay/verify it at the owner before collecting finality.
- `Finalized { certificate, evidence }`: supplies the retained dependency chain,
  including operation QC before effects QC. The supplied target is authenticated
  even when its certificate was already cached.
- `Pending { items, reasons }`: retain/retry; a fixed point or an empty `items` list
  is not completion. Adoption/signing may still need prerequisites or service.

`receive_evidence` imports response proofs without making local voting decisions.
Its `RelayReport` retains unresolved objects and reasons. Individual accepted
journal events survive a later batch failure. Catch-up is also a sequence of
individually atomic durable adoptions, not a transactional rollback of the batch.

The sender's durable issued record remains pending until the owner verifies the
actual effects certificate and journals completion. Retry current publications
with their prerequisites after reordering, rejection or restart. An early valid
Byzantine-assisted QC does not require every honest validator to have signed the
old operation; later publications let lagging validators catch up without waiting
for Byzantine cooperation. Privately existing/unreceived votes never retire honest
work. Capacity assumptions include retained dependencies, cumulative metadata,
transport envelopes and local service—not only transaction counts.

See [[SPEC-034-owned-progress-closure]] and [owned-deadlock-proof-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/owned-deadlock-proof-evidence.md) for the
initialized finite-product completion theorem, executable fair witness and precise
source-refinement boundary. Earlier component evidence is in [owned-progress-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/owned-progress-evidence.md).
