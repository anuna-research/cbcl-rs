---
title: State checkpoint
mode: explanation
---

# State checkpoint

A state checkpoint binds an accepted cut of a CBCL thread to its state. The
repository has two opt-in paths with different trust and scaling boundaries.
Both use the current native state kernel, whose 16 heads include immutable
`initial`, conflict-preserving registers/maps and explicit host-HLC `lww-*` rules.
A timestamp orders eligible state writes; it does not authorize protocol steps
or resource spending.

| Path | What the receiver verifies | Bound or trust premise |
|---|---|---|
| [Halo2](../../crates/cbcl-state-proof/README.md) | Exact accepted-set growth and native state in a verifier-compiled finite relation | Role-free dialect; at most eight public candidates; host-authenticated candidates |
| [Member-certified cache](../../crates/cbcl-checkpoint/README.md) | Native endorsement bundle, projected summary, authenticated tail and returning client's local-history floor | Independently deriving endorsers under the pinned fault policy; native admission and resource authority remain separate |

## Bounded Halo2 proof

A Halo2 checkpoint contains accepted-set and native-state commitments. The verifier
runs the native kernel over every subset and monotone pair of a fixed candidate
vocabulary. The circuit constrains Boolean selections, selected table roots,
grow-only membership, the exact batch difference and an admitted transition.
It proves membership in that verifier-derived relation; it does not implement
all native rule heads or signature verification in gates.

The receiver supplies the expected statement. A chain is checked link by link
from a receiver-pinned start, with each link beginning at the preceding result.
Candidate authentication is external: R4 v2 attestations can establish the host
input, while unauthenticated candidates retain a host precondition. The proof
itself does not distinguish those construction paths.

Enumeration grows as 2^n rows and 3^n transitions. A new vocabulary needs a new
profile and keys; flat commitments require the whole vocabulary at compilation.
Native admission/fold changes require a new semantics pin and regenerated golden
vector. The historical `c9093e8` pin is not a current-kernel compatibility promise.
This bounded experiment does not provide constant-cost large-history opening or
recursive proof composition, and it has no production cryptographic approval.

## Optional private result export

Jolt/Dory ZK is the selected first implementation target for an explicit private
thread-result export, separate from the cached continuation paths above. A
recipient can verify a disclosed result and participant-key roster without
receiving the private discussion or individual ballots. The covered set and
closing policy must be explicit; a proof cannot establish global freshness or
that no undisclosed message exists.

[SPEC-038](../../specs/SPEC-038-optional-thread-proof-export.md) defines the target
interface, including receiver-owned expected context rather than a pre-known
tally. Most threads incur no proof work. The [native experiment](../../experiments/private-vote-export/RESULTS.md)
proves a fixed synthetic voting profile with experimental signed envelopes;
it does not establish native R4 v2 or arbitrary-dialect integration. The
[browser results](../../experiments/private-vote-export/browser/RESULTS.md)
record successful worker proving and independent verification after two
upstream arithmetic portability fixes. Browser budgets and production integration remain separate
acceptance work. A disclosed outcome does not imply permission to continue a
thread from that projection alone.

## Member-certified cached continuation

The cached path maintains summaries and identity coverage during ordinary native
admission. Each endorser derives the exact cut independently before signing; a
client verifies the bundle, admits the tail and checks that its previous floor is
still covered before atomic installation. Prior original signed evidence survives.
Missing or corrupt offers can fall back within configured work and byte budgets.

Its Profile v2 covers all 16 heads, including projected events, ordered aggregates,
protocol-position metadata and resource facts. The typed Lean continuation law
connects these sufficient summaries to the native evaluator over accepted identities.
It does not turn the bundle into a Halo2 proof or formally verify Rust extraction,
serialization, cryptographic admission or native resource classification. Growing
event output and retained selected facts can require growing space.

Neither path establishes global freshness, deletes covered history by itself, or
grants resource authority. The cached endorser policy and Halo2 proof relation are
separate mechanisms; one path's acceptance evidence does not certify the other.

Specifications: [bounded Halo2](../../specs/SPEC-035-halo2-state-checkpoints.md),
[member-certified caches](../../specs/SPEC-035-cached-state-checkpoints.md).
Native meanings: [state rules](../../specs/SPEC-019-state-rules.md),
[initial/HLC registers](../../specs/SPEC-035-register-semantics.md),
[typed kernel correctness](../../specs/SPEC-036-state-kernel-correctness.md).
