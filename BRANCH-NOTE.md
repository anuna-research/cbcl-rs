# Jolt/Dory proof export: branch disposition

The proposed disposition is to shelve this branch for now. It demonstrates a
working mechanism, but does not establish a compelling application requirement
or acceptable proving performance. This note records the conclusion for anyone
revisiting the experiment; it does not close a PR or delete the branch.

## Separate from the merged checkpoint work

The checkpoint feature has already landed through a separate recent merge. It
addresses opening an object from a compact checkpoint and processing its tail
without downloading and folding the entire message history.

This branch explores a different capability: optionally exporting a proof of a
result computed from private thread messages. It is not required for the merged
checkpoint feature and should not be presented as its performance solution.

## What the experiment establishes

The fixed voting program verifies message signatures, unanimous endorsements of
the exact covered set, admission and state folding, then exposes the tally and
participant-key roster without exporting the discussion or individual ballots.
It uses experimental signed envelopes, not native R4 authentication or arbitrary
dialect support. The current public output also lacks the proposal text needed
to bind the tally to a particular public question.

Closing endorsements approve the covered input set; the proof additionally
establishes that the program computed the disclosed result from those inputs.
It does not establish real-world identities, global freshness, or the absence of
withheld messages.

For the motivating use case, participants could instead sign the proposal,
rules, scope and result directly. If the recipient accepts those endorsements,
the expensive computation proof has little additional application value. A ZK
proof matters when the recipient specifically needs to verify computation over
hidden inputs without relying on the signers' assertion that the result is
correct. That requirement has not yet been established for this application.

## Measured cost

On the measured Apple M2, the four-message fixture contained an opening, one
discussion message and two votes, plus two closing endorsements: six Ed25519
signature checks and 8,182,464 executed VM rows.

| Measurement | Observed result |
|---|---:|
| Native proof generation, four Rayon threads | 93.3 seconds |
| Browser proof generation, one compute worker | 860.6 seconds / 14.3 minutes |
| Browser sampled aggregate peak RSS | 2.59 GiB |
| Browser final WASM memory capacity | 3.93 GiB |
| Proof size | 92,796 bytes |

The proof passed fresh browser and independent native verification without
history. Verification is comparatively cheap, but does not compensate for this
proving cost at such a small workload. Successful WASM proving is feasibility
evidence, not practical browser performance or a backend comparison winner.

## Preserve and revisit only with a concrete requirement

Preserve the experiment, the two upstream arithmetic portability fixes, and the
[measured results](experiments/private-vote-export/browser/RESULTS.md).
[SPEC-038](specs/SPEC-038-optional-thread-proof-export.md) and its plan remain
unimplemented production proposals; their presence is not a commitment to ship
this feature. The existing checkpoint implementation needs no change from this
conclusion.

Before resuming integration, identify a recipient and a claim that signed result
exports cannot adequately satisfy, specify which inputs and closing policy are
trusted, and set a concrete latency/memory budget. Then profile authentication,
parsing, admission and folding separately. Signature verification is a candidate
cost, not a measured attribution of the full runtime. Any smaller proof scope
must explicitly state how its guarantees differ from full-history execution.
