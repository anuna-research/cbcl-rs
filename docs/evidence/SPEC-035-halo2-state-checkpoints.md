---
title: SPEC-035 implementation evidence
mode: reference
status: complete
---

# SPEC-035 Halo2 State Checkpoints — evidence record

Governing specification: `specs/SPEC-035-halo2-state-checkpoints.md`.
Generating model for the specification and orchestration: Claude Fable 5.1
(claude-fable-5-1), Claude Code 2.1.318, session 2026-11-04. Implementation
attempts run through Circus with `circus-driver-claude` (one-shot Claude Code);
each attempt's own evidence file is under `docs/evidence/circus/`.

## Specification review (TEST-3510, spec stage)

### Comprehension gate

A fresh-context agent (same model family, no access to the body) read only the
Orientation block of version 0.1.0 and answered: intent restated correctly;
case "unchecked signer label on both sides" predicted correctly (proof
verifies, authorship not guaranteed, REQ-3504 and the metaphor named); case
"chain gap" predicted correctly (REQ-3505, CON-3503); four deciding artefacts
named correctly. Fifteen ambiguities reported. Dispositions in 0.2.0: diagram
caption rewritten to match arrow directions; vocabulary paragraph defines
candidate vocabulary, native, enumeration, recognition, role-declaring dialect
and "admitted pair"; the `unauthenticated` consequence is stated (same profile
identity, proof silent on authorship); the metaphor now states that consequence;
REQ-3509 and REQ-3510 are integration conditions and stay out of Controls by
design; "Spindle Halo2 approach (user reference)" removed from prior art as
unsourced.

### Adversarial review

A fresh-context agent (same model family) reviewed version 0.1.0 against the
prototype code and upstream specs with a mandate to find defects. 26 findings:
3 critical, 9 major, 14 minor. Dispositions, numbered as reported:

| # | Finding | Disposition in 0.2.0 |
|---|---|---|
| 1 | `attested` required `Message::Simple` but candidates are `lang`-wrapped | Accepted. Attestation targets `innermost_simple()`; wrapper bound by REQ-3512 (b). ADR-3504 records it. |
| 2 | canonical key spelling `@ed25519:a` breaks literal `:from` equality | Accepted. Identity compared via `KeyId::parse`; label keeps `:from` text (REQ-3504 c, d). |
| 3 | `unauthenticated` as "only path" unenforceable with public fields | Accepted. Fields private, accessors added, `compile_fail` doctest in TEST-3503 (REQ-3504 a). |
| 4 | `Chain::verify` reads link statements, contradicting hard stop REQ-3502 | Accepted. REQ-3502 split (a)–(d); chain takes receiver start and optional expected end; ADR-3505 explains. |
| 5 | `Signer` carries no key identity; host can pair wrong key | Accepted as a boundary. Recorded as documented precondition in CON-3504, F2 narrowed to prover-side laundering, Open item added. |
| 6 | compile-time rejection contradicted existing test | Accepted. REQ-3512 keeps prototype behaviour: compile succeeds, sets invalid. |
| 7 | REQ-3509 vs REQ-3510 dependency contradiction | Accepted. REQ-3509 (b) names the `cbcl-cli` optional exception. |
| 8 | ABNF stricter/looser than `serde_json` | Accepted. CON-3502 restated as the recogniser's language with explicit whitespace, order, duplicate and integer rules. |
| 9 | thread and dialect binding tested but never required | Accepted. New REQ-3512, F7. |
| 10 | wrong anchor SPEC-019 CON-1908 | Accepted. Links to the SPEC-019 kernel section. |
| 11 | fuel 256 bounds nodes, not bytes | Accepted. REQ-3507 states the node budget and scope. |
| 12 | "absence of row allocation" undecidable; missing cases | Accepted. TEST-3506 uses `Err` plus a 100 ms bound and names new cases. |
| 13 | `Proof` lacks `PartialEq` | Accepted. REQ-3508 (c). |
| 14 | address spelling `sha256-<hex>` vs typed root | Accepted. CON-3500 and CON-3505 fix wire addresses. |
| 15 | limb order unspecified | Accepted. CON-3501 fixes limb 0 = bytes 0..16. |
| 16 | sort order is content address, not (label, canonical) | Accepted. CON-3500 corrected. |
| 17 | `SEMANTICS_VERSION` test is manual | Accepted. `relation_domain(version)` and a named test (REQ-3506 a, TEST-3505). |
| 18 | chain cannot start from trusted non-genesis | Accepted. Start parameter; `Profile::genesis` for the empty start. |
| 19 | `Prover` has no contract | Accepted. CON-3506. |
| 20 | multiple obligations per clause | Accepted. REQ-3502, 3504, 3506–3509 lettered; tests cite letters. |
| 21 | non-portable NFR; transcript overflow unruled | Accepted. NFR-3500 records machine; REQ-3508 (d) prove fails closed. |
| 22 | mutation configuration target "does not exist" | Partly accepted. `mutants.toml` exists at the repository root with an `examine_re` allow-list; REQ-3509 (d) now names it. |
| 23 | identity transition is a positive case; limb test maps to REQ-3500 | Accepted. TEST-3502 reworded and validates both. |
| 24 | whitespace test also covers CON-3500 post-conditions | Accepted as a note; test retained under TEST-3505 for identity invariance. |
| 25 | "notify the maintainer" and "own compiled profile" untestable | Accepted. REQ-3511 records open items in the evidence file; CON-3503 lists the precondition as unverifiable by the library. |
| 26 | `:from` string vs symbol spelling | Accepted. REQ-3512 states both are distinct candidates; golden vector pins the fixture spelling. |

Review tooling note: `usdd-count.sh` matches three-digit artefact ids and
undercounts this repository's four-digit ids; counts are therefore not pasted
here. `usdd-lint.sh` on 0.2.0: see the gate section below.

## Gates

Run on 2026-11-04 on the integration branch content as merged into
`circus/docs-evidence/1` (Apple M2, Mac14,3, macOS 26.5, rustc 1.95.0), with
`RAYON_NUM_THREADS=2`. Per-task gate runs are in `docs/evidence/circus/*.md`.

`make check` (= `cargo fmt --all --check`, `cargo clippy --workspace --all-targets --locked -- -D warnings`,
`cargo check -p cbcl-core -p cbcl-parser --no-default-features --locked`, `cargo test --workspace --locked`),
final lines:

```
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 13.69s   # clippy
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 2.07s    # nostd
    Finished `test` profile [unoptimized + debuginfo] target(s) in 21.19s
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
make check exit=0
```

56 `test result: ok` suites, 1616 passed, 0 failed, no `FAILED` or `panicked` lines.

`RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1`

```
test result: ok. 45 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 37.73s
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.03s
crate test exit=0
```

(The ignored test is the golden-vector writer; the one doc-test is the
`compile_fail` check that `Candidate` cannot be built by struct literal.)

`cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings`

```
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.17s
clippy exit=0
```

`python3 scripts/state-proof-mutations.py`

```
{"mutant": "unbound-after-state", "test": "every_public_limb_is_constrained_without_the_host_precheck", "exit_code": 101, "killed": true, ...}
{"mutant": "unconstrained-admission-transition", "test": "previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks", "exit_code": 101, "killed": true, ...}
runner exit=0
```

`cargo tree -i cbcl-state-proof --workspace --features cbcl-cli/state-proof`

```
cbcl-state-proof v0.1.1 (.../crates/cbcl-state-proof)
└── cbcl-cli v0.1.1 (.../crates/cbcl-cli)
tree exit=0
```

`cargo tree -i cbcl-state-proof --workspace` (no feature)

```
cbcl-state-proof v0.1.1 (.../crates/cbcl-state-proof)
tree-plain exit=0
```

Only `cbcl-state-proof` depends on itself without the feature, and only
`cbcl-cli` with it (REQ-3509 b). The earlier standalone `no_std` regression was
fixed on main and merged into this branch in `fe2a06e`; the current workspace
verification includes `make nostd`. Historical gate output above is retained.

## Mutations

From `docs/evidence/state-proof-mutations/mutations.json`, written by
`python3 scripts/state-proof-mutations.py` on 2026-11-04 (run recorded under
Gates). Each mutant is a one-line edit of `crates/cbcl-state-proof/src/circuit.rs`;
the named test must execute and fail (exit 101), not fail to compile.

| Mutant | Named test | Exit | Result |
|---|---|---|---|
| `unbound-after-state` | `every_public_limb_is_constrained_without_the_host_precheck` | 101 | killed |
| `unconstrained-admission-transition` | `previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks` | 101 | killed |

Command per mutant: `cargo test -p cbcl-state-proof --lib <test> -- --test-threads=1`.
Every named mutant is killed. The attempt-level mutations (one per task, each a
deliberate break of the code that task wrote, run, observed failing and
reverted) are recorded in each attempt's file under `docs/evidence/circus/`.

## NFR-3500 measurement

Run on 2026-11-04 by the docs-evidence attempt (branch `circus/docs-evidence/1`).

Machine:

| Query | Value |
|---|---|
| `sysctl -n machdep.cpu.brand_string` | Apple M2 |
| `sysctl -n hw.model` | Mac14,3 |
| `sw_vers -productVersion` | 26.5 |
| `rustc --version` | rustc 1.95.0 (59807616e 2026-04-14) |

Command: `RAYON_NUM_THREADS=2 cargo run -p cbcl-state-proof --example checkpoint --release`
(exit 0). Full JSON output:

```json
{"candidates":3,"compile_ms":1,"prover_setup_ms":302,"verifier_setup_ms":268,"prove_ms":165,"cached_verify_ms":7,"transcript_bytes":3616,"package_bytes":13659,"state":{"title":"Register","entries":{"@a":"new"},"all":{"sha256-7b448dbd6586709f85aa895600692c988a694ca3a7a9294db7023d291f138b8b":{"by":"@a","value":"new"},"sha256-ed411b6c465b3f6a873b0eca2e4265305c5f516a23b756be1a9d57d85c70cbd8":{"by":"@a","value":"old"}}},"tampered_state_rejected":true,"signature_verification":"external host precondition","eight_candidates":{"fixture":"tags-and-balance","candidates":8,"compile_ms":49,"circuit_k":14,"proved":false}}
```

Against NFR-3500 for the three-candidate signer-supersession fixture:

| Bound | Limit | Measured |
|---|---|---|
| cached-key verification | 1,000 ms | 7 ms |
| transcript | 16,384 bytes | 3,616 bytes |
| JSON package | 100,000 bytes | 13,659 bytes |
| eight-candidate circuit `k` | 14 | 14 |

The eight-candidate profile is compiled from the first eight distinct accepted
messages of `test-vectors/state/tags-and-balance.json`; the lunch-vote fixture
named in TEST-3511 has only five accepted messages, so it cannot fill eight.
Only `k` is reported for it; no keys are built and nothing is proved over it.
`k` for eight candidates sits exactly on the ceiling: the row estimate in
`StateCircuit::k` is `3·2^n·(n+2) + 8n + 64 + |transitions| + 1`, rounded up
to a power of two, and the fixture yields 2^14 rows. The unit test
`eight_candidate_profile_circuit_k_is_at_most_14` pins the bound.

## Independent code review

Two fresh-context reviews of the integration branch at `e3bf0ea` (all
implementation tasks merged), each given only the specification and the
deliverable, with a mandate to find defects and no access to attempt evidence
or transcripts:

- Claude Fable 5.1 (same model family as the generator, fresh context, ran the
  test suites and gates itself): 0 critical, 4 major, 11 minor, 4 notes. No
  soundness break found; public-instance wiring, limb encoding, one-hot
  indicators, transition accumulation, grow-only gate and batch selection
  checked out; recognisers accept exactly CON-3502.
- Codex (`gpt-6.1-sol`, cross-model, static review; its sandbox could not run
  cargo): 0 critical, 1 major, 5 minor, 2 notes.

Dispositions (C = Claude finding, X = Codex finding):

| Finding | Severity | Disposition |
|---|---|---|
| X1 nested `lang` wrappers bypass dialect binding (`dialect_name` reads the outer wrapper, admission the innermost message) | major | Accepted. REQ-3512 (b) amended in 0.2.2 to reject nested wrappers; repaired in `review-repairs` with a negative test. |
| C1 / X4 REQ-3507 (b, c, d, h) implemented but untested; `size_bounds_and_roles_fail_before_enumeration` absent | major | Accepted. Test added in `review-repairs`, including the 100 ms bound and the roles fixture. |
| C2 / X8 crate README front matter said `status: implemented` while the spec is `implementing` | major | Accepted. README status follows the spec; set by the reviewing session with the spec. |
| C3 / X3 mutation runner lacks the TEST-3504 continuity mutation and the final-one constraint mutation | major | Accepted. Runner generalised to several files; both mutants added. |
| C4 Boolean selector, growth gate and validity constants are mutation-invisible because every witness is mask-derived | major | Accepted for the Boolean gate: a `#[cfg(test)]` forge hook presents a non-Boolean bit and a test asserts rejection. Growth and validity gates stay redundant with the transition sum by design (defence in depth); recorded as a known blind spot. |
| C5 / X5 two proofs of one statement not shown to differ; `prove` size check not exercised | minor | Accepted (first half): test added. Second half: only an over-size profile could exercise it; recorded in the README as untestable at the eight-candidate bound. |
| X2 duplicate `:from` scan assumed aligned pairs | minor | Accepted. Sliding scan like `keyword_fields`; negative test added. |
| C7 profile-level `:sender` ≠ label and duplicate `:from` untested | minor | Accepted. Tests added. |
| C8 lunch-vote per-subset parity not tested | minor | Accepted. Parity loop runs over both fixtures. |
| C9 / X9 fuzz crate depends on the proof crate against REQ-3509 (b) | minor | Accepted as a spec tension. REQ-3509 (b) amended in 0.2.2 to name the out-of-workspace fuzz crate. |
| C10 one combined resource-limit error | minor | Accepted. One message per bound. |
| C11 / X6 CLI `read_file` bounded by metadata only | minor | Accepted. Read through a `take(limit + 1)` and reject on length. |
| C12 duplicate addresses silently OR-ed; chain-verify prints byte arrays | minor | Accepted. CON-3505 amended in 0.2.2; repeated addresses reject; checkpoints print as hex. |
| C13 dead code (`check_len` in `verify`, `relation_id` alias) | minor | Partly accepted. Removed `relation_id`; retained `check_len` after independent repair review showed public serde deserialization bypasses constructors. The direct-deserialization regression test pins rejection before backend verification. |
| C14 early-rejection path indistinguishable from backend failure in tests | minor | Accepted. Tests assert the rejection message of the early path. |
| C15 README omits the v1-signature and two-labels limitations; `relation_domain` visibility wording | minor | Accepted. README updated. |
| X7 serde derive accepts positional arrays for structs | note | Accepted. CON-3502 and CON-3505 amended in 0.2.2; recognisers check object shape before typed deserialisation; tests added. |
| C16 `:from @a` with `:sender "@ed25519:a"` passes `attested` but every set is invalid under REQ-3512 (c) | note | Accepted as documentation. README states the trap. |
| C17 without-feature CLI behaviour verified manually only | note | Recorded. Automating it needs a second build; manual record in `docs/evidence/circus/cli-checkpoint.md`. |
| C18 fuzz target covers `from_json` only, not `Verifier::verify` | note | Accepted. A second target `state_proof_verify` fuzzes transcript bytes against a fixed verifier. |
| C19 / X (NFR) 1,000 ms budget only measured by the example | note | The measurement and machine are recorded above; depth item stays with the maintainer. |
| X conformance: REQ-3506 (d) whitespace test does not introduce whitespace | minor | Accepted. Test adds spacing and newlines to candidate text. |

Repairs are scoped to the implicated requirements and carried out by the
`review-repairs` Circus attempt; its evidence is `docs/evidence/circus/review-repairs.md`.
The status change to `implemented` is made by the reviewing session after the
repairs merge, per REQ-3511.

## Open items for the CBCL maintainer

Carried from the specification's Orientation; none closed by this record.

- Incremental constrained kernel over authenticated state paths, removing the
  eight-candidate ceiling (successor specification).
- Recursive proof composition; the o1js experiment is evidence only.
- Human cryptographic review and production authorisation.
- Lean correspondence between the compiled relation and the SPEC-019 model.
- Pairing a `Signer` with the key it embodies is a host obligation the library
  cannot check (CON-3504). Owner: host integrators.
- Current status: the specification and crate README are `implemented` under
  the independent status decision below. Human cryptographic review and
  production authorisation remain open.


## Review repairs verified

The interrupted `review-repairs/1` attempt was recovered by a new Codex session on 2026-11-04. Acceptance evidence, reconstructed red gates, final workspace and feature gates, fuzz-target build, and named mutation results are committed in [[review-repairs]] and its adjacent `review-repairs-logs/` directory. The historical Gates and Mutations sections above describe the earlier implementation baseline; the repair record supersedes them for current acceptance.

A fresh-context review of the repairs identified one regression: deleting `Chain::verify`'s length check allowed public `Deserialize` to bypass the constructor limit. The guard was restored with an executed failing-then-passing regression test for [[SPEC-035-halo2-state-checkpoints#REQ-3505]]. The reviewer reinspected the fix and reported no further correctness findings. Item 11's proposed cleanup was narrowed accordingly. All named mutants are killed by executed tests. The independent reviewer records the status decision below, under [[SPEC-035-halo2-state-checkpoints#REQ-3511]].


## Status decision

On 2026-11-04, the independent Codex reviewing session `/root/status_reviewer`
sets version `0.3.0`
to `implemented` under [[SPEC-035-halo2-state-checkpoints#REQ-3511]] and
[[SPEC-035-halo2-state-checkpoints#TEST-3510]].
This status-reviewing session did not produce code or implement repairs. It
inspected the specification, merged repair diff, prior fresh-context review and
its dispositions, and committed gate evidence at `744e9f1` (repair commit
`51dbe91`). The prior fresh-context reviewer `/root/review_repairs` found
the chain-length regression,
reinspected its correction, and reported no further correctness findings.
The merge introduces no additional deliverable change beyond the reviewed repairs.
No unresolved correctness finding blocks this status decision.

The decision records implementation verification, not production authorisation.
Human cryptographic review, long fuzz campaigns, and the other maintainer-owned
depth items remain open. The earlier gate sections remain historical records;
[[review-repairs]] supplies current repair acceptance evidence.

### Disposition verification

| Finding | Inspected implementation, test, or scoped deferral |
|---|---|
| X1 | `profile::dialect_bound`; `nested_or_wrapped_dialect_forms_invalidate_every_containing_set` rejects nested and signed wrappers. |
| C1 / X4 | `size_bounds_and_roles_fail_before_enumeration` covers individual size limits, timing, and roles rejection. |
| C2 / X8 | README status followed the specification during repairs; this independent decision updates both metadata values. |
| C3 / X3 | Mutation runner includes final transition-total and chain-continuity mutations alongside the original mutations. |
| C4 | Boolean forge seam and gate-specific rejection assertion added. Growth and validity mutation isolation remains a documented defence-in-depth blind spot. |
| C5 / X5 | Two proofs of one statement differ and both verify. Transcript overflow exercise remains deferred at the bounded profile size; runtime rejection remains present. |
| X2 | `from_field` scans past positional parameters; the attested duplicate-field regression exercises the repaired scan. |
| C7 | Profile/circuit invalidity cases cover conflicting `:sender` and duplicate `:from`. |
| C8 | Lunch-vote per-subset native parity uses the shared parity helper. |
| C9 / X9 | Version 0.2.2 explicitly permits the out-of-workspace fuzz dependency. |
| C10 | Compilation reports each resource bound separately. |
| C11 / X6 | CLI reads through `take(limit + 1)` and rejects excess bytes. |
| C12 | CLI rejects repeated addresses and emits hex checkpoints; golden output assertions cover both verification commands. |
| C13 | Alias removed; `Chain::verify` retains its required length check. Direct-deserialization regression rejects before backend verification. |
| C14 | Single-proof and chain tests assert early rejection messages. |
| C15 / C16 | README documents v1 signatures, key-label spelling, and internal `relation_domain` visibility. |
| X7 | Proof, chain, and CLI profile recognisers check object shapes before typed parsing; negative array cases cover those positions. |
| C17 | Without-feature CLI verification remains the recorded manual check in [[cli-checkpoint]]; a second automated build remains deferred. |
| C18 | `state_proof_verify` exercises transcript bytes against a fixed verifier; target compilation is recorded. Long campaigns remain maintainer-owned depth work. |
| C19 / X NFR | Recorded machine and example measurements satisfy the stated budget; ongoing depth ownership remains with the maintainer. |
| X whitespace | Candidate identity test explicitly inserts spaces and newlines. |

### Inspected gate evidence

These results come from committed output, not a fresh execution by this reviewer.
The reviewer checked the relevant assertions, successful suite output, and
mutation records. Unchanged full suites were not repeated for this metadata decision.

| Gate | Inspected result and committed output |
|---|---|
| Workspace | `make check` exits 0; includes the final chain-bound regression: [workspace.log](circus/review-repairs-logs/workspace.log). |
| Proof crate | Tests and compile-fail doctest pass: [crate.log](circus/review-repairs-logs/crate.log). |
| Feature CLI | Checkpoint integration tests pass: [cli.log](circus/review-repairs-logs/cli.log). |
| Lints | Both crate and feature CLI clippy runs pass with warnings denied: [crate-clippy.log](circus/review-repairs-logs/crate-clippy.log), [cli-clippy.log](circus/review-repairs-logs/cli-clippy.log). |
| Fuzz target | Offline verification-target compilation passes: [fuzz.log](circus/review-repairs-logs/fuzz.log). No long campaign is claimed. |
| Named mutations | Every runner entry reports `killed: true`, with assertion failures required: [mutations.log](circus/review-repairs-logs/mutations.log). |
| Reconstructed red gates | Nested wrapper, duplicate-field scan, object shape, bound errors, and CLI recognition execute and fail against baseline: [command/results manifest](circus/review-repairs-logs/results.json), with individual `red-*.log` files beside it. |
| Reviewer regression | Removing the chain bound produces the expected assertion failure; restoring it passes: [chain-red.log](circus/review-repairs-logs/chain-red.log), [chain-green.log](circus/review-repairs-logs/chain-green.log). |
| Vault | Syntax check passes. Existing dead-link backlog is unchanged, as recorded in [[review-repairs]] and [zetl-syntax.log](circus/review-repairs-logs/zetl-syntax.log). |

The earlier standalone `cbcl-core --no-default-features` defect was fixed on
main and merged in `fe2a06e`; the committed final workspace log includes the
successful `make nostd` gate. The maintainer-owned open items remain open.
