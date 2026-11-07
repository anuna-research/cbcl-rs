---
mode: explanation
status: experiment-complete
---
# Private vote export findings

## Decision supported by this experiment

Jolt/Dory with zero knowledge is a viable experimental implementation of optional
private result export using the native CBCL kernel. Real proofs authenticated
participants and closure, admitted and folded private messages, and exported the declared public statement; witness privacy relies on the
pinned upstream zero-knowledge protocol. The matched clear/ZK run makes privacy overhead
measurable without changing the guest or witness. It does not establish a winner
against all zkVMs: RISC Zero, SP1 and Nexus were not rerun on this authenticated
vote workload; Akita has no ZK mode in the pinned implementation.

The experiment supports continuing with this backend behind an export interface.
It does not justify making proving part of normal thread processing, selecting
Halo2 as the general backend, or promising practical browser/mobile proving.

## Workload and statement

The governing contract is [[BRIEF]]. Synthetic Alice and Bob open a vote, discuss
privately and cast different yes/no ballots. Four messages plus two unanimous
closure signatures require six strict Ed25519 verifications inside the guest.
The eight-message variant adds private discussion and requires ten signatures.
The exact same current native consumer installs the dialect, admits from empty
and folds; only roster, scope, salted covered-set commitment, counts and tally
are exported. The full ballot map, question, discussion and signatures remain
witness data. No unsalted ballot/state hash is public.

These are experimental signed envelopes, not a demonstration of native R4 v2
attestation verification or human identity credentials. Public labels are bound
to signing keys. Every participant is eligible in this profile; abstention means
no ballot, while revisions/concurrent HLC ordering follow the native kernel.
The dialect is deliberately fixed to this voting profile, not arbitrary caller
source. Unanimous closure establishes the agreed covered set, not global
freshness or the absence of undisclosed messages. Public proposal/context and
key-to-person identity policy remain explicit future design decisions.

## Real proof measurements

Apple M2, 8 GB RAM; four Rayon threads; Jolt
`beebf45d829f5aecc5d330f78879cd914e47541e`, Rust 1.95.0,
upstream CPU `build-fast`, native kernel at `6e3ad4e` (same core semantics as
`d1a093d`). No GPU, mock proofs or upstream cryptographic modifications.
Single observations on a shared workstation, not statistical throughput claims.
Memory is sampled aggregate process-tree RSS every two seconds, not a hard OS
limit or exact peak. GB below is decimal.

| Run | Preprocessing | Proof generation | Proof bytes | Warm verification | Sampled peak |
|---|---:|---:|---:|---:|---:|
| Dory clear, 4 messages | 14.778 s | 89.731 s | 98,112 B | 115.1 ms | 1.79 GB |
| Dory ZK, 4 messages | 9.842 s | 93.292 s | 92,796 B | 184.2 ms | 1.83 GB |
| Dory ZK, 8 messages | 9.796 s | 150.115 s | 93,198 B | 183.7 ms | 2.99 GB |

The four-message clear and ZK runs have the same guest ELF SHA256
`7cc6a3a76581e43c05cf4ad1d96e00b5319627869ee3fc36fb92bc06cb3bb870`, exact signed witness and byte-identical
serialized public IO. ZK proof generation was about
4.0% slower in this pair;
the proof was smaller because its protocol envelope differs. Neither observation
is a general overhead bound. Preprocessing/cache warmth differs; do not infer
cold-start superiority from the setup times. The managed four-message runs each
took about 107 seconds including count, tracing, setup, proving, verification and
other host work. First guest compilation was measured separately at 55.4 seconds;
first host builds and dependency resolution are excluded from proof timings.

Fresh receiver crypto verification was 132.7 ms clear
and 181.5 ms ZK. Including file loading/deserialization,
its internal totals were 470.6 ms and
512.2 ms; outer process wall times were
0.502 s and 0.537 s.
These exclude network transfer. The independent reviewer separately verified the
ZK artifact in a fresh process without a history argument.

The ZK public bundle (proof, public IO and expected statement) is
95,539 bytes with cached trusted preprocessing;
including preprocessing and its trust pin makes it 9,865,426 bytes.
Verifier software and independent acquisition/authentication of expected scope
and pins are excluded. No bandwidth saving against these tiny histories is claimed.
The four/eight-message ZK preprocessing was byte-identical at
9,769,212 bytes; reuse for arbitrary programs/bounds is unmeasured.

## Scaling observations, not unexecuted proofs

| Covered messages | Executed VM rows | Required padded rows | VM execution | Within 2^24 profile |
|---:|---:|---:|---:|---|
| 4 | 8,182,464 | 8,388,608 | 169 ms | yes |
| 8 | 13,376,619 | 16,777,216 | 260 ms | yes |
| 16 | 24,448,095 | 33,554,432 | 455 ms | no |
| 32 | 47,472,753 | 67,108,864 | 860 ms | no |

Every count output matched the fixture expected statement generated by native
compute; the native tests separately assert the intended tallies by hand.
Only four-message clear/ZK and eight-message ZK full proofs were generated.
Sixteen and thirty-two messages exceed the chosen local profile; no full-proof
attempt, proving time or proof size is claimed for them. This is a harness bound,
not a universal limit of Jolt. Thousands-message authenticated proving remains
unmeasured here. The wrapper still retries native admission over growing accepted
sets; the earlier cloning/scaling concern has not been fixed or quantified by
this experiment. Signature, parsing, allocation and fold costs also need profiling.

## WASM result

The pinned Dory/ZK prover library and its verifier dependency closure passed a
locked `wasm32-unknown-unknown` Cargo check. A separate check passed for the tracer
and this no_std vote consumer. The probes select `jolt-platform/random` and
`--cfg getrandom_backend="wasm_js"`; exact commands are in the ignored run ledgers.
This is library compilation evidence, not browser linkage, runtime proving or
browser performance evidence.

The native harness uses files, a build toolchain, processes and a configured 128 MiB host-thread
stack. A browser wrapper must preload the compiled guest/program,
prepare trace/witness data, supply browser entropy, integrate workers as needed,
and measure memory/latency. Native 1.83–2.99 GB peaks make actual device testing
necessary. The upstream pinned WASM CI proves natively and verifies in Node;
it does not validate this browser prover. RAYON_NUM_THREADS does not configure
browser workers. No remote prover received a real private discussion.

## Acceptance and review

The saved native suite passed twelve tests, covering mixed/replacement outcomes,
concurrent HLC, lower-clock explicit replacement, abstention, order independence,
strict authentication/closure, malformed input and unresolved causality.
Eleven direct VM negatives rejected the expected invalid witness with the host
native precheck bypassed, after a successful same-ELF VM control. Both receiver
suites passed fourteen cases: an honest artifact plus thirteen negatives, including
coherent tally/output tampering reaching cryptographic verification, wrong scope,
setup/pin, clear/ZK substitution and nonempty advice. An arbitrary corrupted ZK
proof was rejected during bounded decoding; it is recognition evidence, not a
claimed cryptographic-stage failure. The initially over-strict test expectation
was corrected to allow that exact decoder rejection while preserving the strict
cryptographic requirement for coherent output tampering.

Two targeted source mutants were killed by executed named assertion failures:
removing message signature verification and removing closure unanimity. Passing
named baselines preceded mutation, compiler failures did not count, and the staged
consumer was restored byte-for-byte. Independent fresh-context review inspected
source, artifacts, resource ledgers and rejection/mutation evidence; limitations
include upstream cryptographic audit and production pin distribution. It authored
none of the implementation. The final review record remains an ignored local
artifact, alongside source and artifact hashes.

The measured consumer source remains frozen. Clippy flags two redundant unit
expressions in successful match branches; these are style-only. Removing them
changed the guest image despite identical trace length, so that cleanup was
reverted to preserve exact proof-image provenance. The final lint command permits
only `clippy::unused_unit` while denying other warnings; no cryptographic or
semantic check is relaxed. The experiment lock pins Ed25519-dalek 2.2.0.

Generated logs, binaries, private synthetic witnesses, proofs, preprocessing and
review JSON live in ignored `outputs/private-vote-export/`; no raw logs or large
proof artifacts are tracked. [[README]] describes reproduction; `jolt-lock.patch`
records the resolution delta rather than duplicating an entire vendor lockfile.
The first Cargo attempt hit two same-version CBCL path copies; staging isolated
workspace membership repaired that. The initial fixture incorrectly used intend
for an opener; the native API rejects that by design, and fixture construction
was repaired without changing the kernel. No production code/default changed.

## Next decision

Keep proving optional and the public statement independent of the backend.
Jolt/Dory ZK now has concrete native evidence for a private authenticated result
export. A browser deployment still needs an actual browser proof and memory test;
compilation alone cannot settle that choice. Profile and reduce admission/witness
cost before increasing history sizes. A vote-specific authenticated projection
could reduce work, but must preserve ballot completeness and closure rather than
silently omit relevant history. The CBCL maintainer owns generalising the dialect
interface, identity credentials, public proposal/context, closure quorum/liveness,
private data availability and production cryptographic review.
