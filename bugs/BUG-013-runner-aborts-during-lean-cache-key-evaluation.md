---
id: BUG-013
title: Runner aborts before the Lean cache action starts
severity: S3
priority: P1
status: resolved
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: .forgejo/workflows/lean.yml
---

# BUG-013: Cache-key evaluation aborts before Lean installation

The required proof job for [[SPEC-038-lvar-state-kernel#TEST-3806]] sometimes
fails before the cache action and installer execute. This is distinct from the
earlier elan release-download HTTP 504, addressed by the pinned installer and
API-asset fallback. It prevents the checks required by
[[SPEC-005-lean-mechanisation#NFR-510]] from running.

## Observed boundary

[Run 289, job 0](https://git.anuna.io/anuna-research/cbcl-rs/actions/runs/289/jobs/0)
checked out commit `5e76c52` successfully on runner `hetzner-fsn` v9.1.1, then
invoked the runner's `workflow/hashfiles/index.js`. The next recorded event
skips the cache step because its success condition is false; cleanup follows
and the job fails after seven seconds. The raw log supplies no diagnostic for
the hashing command. The precise runner-internal cause is unverified.

[Run 299, job 0](https://git.anuna.io/anuna-research/cbcl-rs/actions/runs/299/jobs/0)
on the same named runner/version restored its cache and ran the pinned Lean
4.27.0 installer check successfully before entering the proof build. Therefore
this evidence does not establish a universally broken cache action or installer.
Intermediate runs cancelled by newer pushes are also distinct from failures.

## Implementation

Compute the key in an ordinary Node step using only standard-library SHA-256
and file reads. Publishing the digest through the step output removes the
runner's pre-action `hashFiles` evaluation from this path and makes failures
ordinary, visible command failures. Cache restore, installation, build, lint,
oracle and audit remain required. No failure is suppressed.

The calculation retains the existing key algorithm and file order: hash each
of `lean-cbcl/lean-toolchain` and `scripts/ci-install-lean.sh`, concatenate their
binary digests, then hash that concatenation. On the current source this gives
`1378afe6a4b5a1282e28ca2e2c36a734f9cbf551590ae1a218696eb4e14ce6ae`,
matching run 299's restored cache key. Existing caches remain usable.

## Acceptance evidence

`node --test scripts/test-ci-lean-cache-key.mjs` passes its fixed digest vector,
content invalidation and missing-input cases. Missing input fails before any
cache digest is published. The script resolves inputs relative to itself,
independently of the process working directory.

[Run 301, job 0](https://git.anuna.io/anuna-research/cbcl-rs/actions/runs/301/jobs/0)
on commit `619bf67` ran the explicit calculation, passed all cache-key tests,
restored the existing cache and verified Lean 4.27.0. The complete required Lean
job then passed, including its oracle, Batteries linter and axiom-audit gates.
This resolves the repository mitigation; the original runner-internal cause
remains unknown. Later revisions still require their own successful CI result
before the broader SPEC-038 implementation or `lean-ci-green` task is complete.
