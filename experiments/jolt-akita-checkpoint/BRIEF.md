# Jolt/Akita CBCL checkpoint experiment

User: generation time is too long; evaluate Jolt with the lattice-based SNARK.
Hypothesis: Jolt's optimized Akita backend can prove the same existing CBCL
consumer computation faster than the recorded RISC Zero baseline. No claim that
published throughput transfers to CBCL or that a lattice PCS alone establishes
end-to-end post-quantum security of SHA-bound messages/signatures.

Pin Jolt beebf45d829f5aecc5d330f78879cd914e47541e and its locked Akita dependencies.
Use the unmodified native core/parser, same input schema, bounds, hash framing and
public journal as [[experiments/general-kernel-checkpoint/BRIEF]]. Adapt only the
common wrapper's std imports to alloc/core for a no_std guest; compare native and
VM outputs byte-for-byte with existing fixtures and expected commitments.
History is untrusted advice, not public verifier input. Reject panic outcomes.
Authentication, signer/wire binding and expected-set anchoring remain the same
explicit host assumptions. No fresh/full validity/continuation claims.

Tier1 experimental proof boundary: independent fresh-context review (model launch gpt-6-astra; distinct-model diversity unestablished) and human
cryptographic review open. Reuse upstream public optimized prover and verifier,
not SDK Dory-only host helpers. Try CPU first; Metal only through a supported
upstream backend, measured separately. Separate guest build, tracing, setup,
proof, verification and complete transport bytes. Use a real proof and serialized
separate-process receiver with no history; detect tampered expected/output/proof.
Compare identical drawing2-message and register9-message inputs before scaling.
No mock or benchmark-only guest may be called a CBCL proof.

Reproducible overlay: source lives here, staged into a pinned read-only-source
checkout's new example/package directories; only workspace membership and owned
overlay paths are changed. Save patch/locks and repository state. Do not modify
upstream cryptographic checks, catalogs or kernel semantics to force a pass.
Akita schedule provisioning must use legitimate validated geometry/security
parameters. A missing compatible schedule is a recorded setup limitation.

One Cargo worker, one prover process with up to4 Rayon threads, sampled aggregate
4GiB RSS cap, at least1GiB disk reserve,30minutes per managed process and90minutes
wall envelope from this worktree's creation including setup/reviews. No paid
remote service, real drawings, production changes, global profile edits or upstream
messages. At a cap save partial artifacts and precise failure, not inferred
performance. Producer Codex (GPT-6 family; exact version/settings not exposed).
Maintainer next: use actual results to choose a backend or provision a larger
machine, then specify an authenticated general checkpoint protocol.


The operator must trust the program/setup build before pinning trusted.json. The
receiver verifies that independently supplied setup digest before deserializing;
the recorded ELF hash is build provenance, not independently authenticated by the
receiver. Setup bytes are measured as cold transport; warm proof-only key reuse
is explicitly conditional. The current CPU build uses upstream build-fast profile
(opt3, LTO off, overflow checks on); it is not claimed to reproduce the authors'
release/Metal benchmarks. Metal's published result is from draft PR1848, not the
mainline CPU code being exercised.
