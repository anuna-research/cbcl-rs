---
mode: explanation
status: static-review
---
# Recursive experiment review record

A fresh-context reviewer `/root/proof_review` inspected the brief, circuit,
helpers, experiment runner and native oracle without editing or heavy proving.
The generating and reviewing sessions used OpenAI Codex with inherited model
configuration. Exact cross-model independence is unverified.

The first review found that predecessor roots and appended operations were
private inputs. A valid proof could therefore certify an unrelated history for
the same object. Resolution: public Context now binds object, kind, both expected
parent roots and operation identity; the receiver checks caller-owned context.
The initial compilation was stopped and recorded before restarting.

The reviewer also found that any proving exception counted as invalid-parent
rejection, and that serialization coverage was overstated. Resolution: generic
errors are inconclusive and fail the run; all positive proofs receive serialized
verification. The observed forged-parent failure was specifically
`prevs_verified` with an unsatisfied constraint.

On re-review, no additional apparent constraint soundness or witness-dependent
layout defect was found. Exact subset checks in both directions preserve the
specified sets, and canonical ordering prevents duplicate records. The reviewer
recommended an explicit capacity-overflow circuit test; it now demonstrates
rejection of a truncated union whose two valid parents contain five records.

This is static review plus executed experiment evidence, not an independent
cryptographic audit or production approval. External messages and head freshness
remain outside the completeness claim.

Targeted arithmetic mutations subsequently removed the append-parent binding
and right-input preservation constraints. Each named negative assertion executed
and failed; sources were restored, then the normal tests passed again.
