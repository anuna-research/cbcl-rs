---
title: SPEC-035 implementation evidence
mode: reference
status: in-progress
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
`cbcl-cli` with it (REQ-3509 b). Known gap carried from the workspace-gates
attempt: `cargo check -p cbcl-core --no-default-features` on its own fails on
`main` and here alike (`blame.rs` lacks `use alloc::vec`); the `make check`
`nostd` target passes because it checks `cbcl-core` together with
`cbcl-parser`. Unchanged by SPEC-035.

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

Pending.

## Open items for the CBCL maintainer

Carried from the specification's Orientation; none closed by this record.

- Incremental constrained kernel over authenticated state paths, removing the
  eight-candidate ceiling (successor specification).
- Recursive proof composition; the o1js experiment is evidence only.
- Human cryptographic review and production authorisation.
- Lean correspondence between the compiled relation and the SPEC-019 model.
- Pairing a `Signer` with the key it embodies is a host obligation the library
  cannot check (CON-3504). Owner: host integrators.
- Status: the specification remains `implementing` (REQ-3511). The crate README
  carries `status: implemented` for the crate's own requirements and says the
  artefact is not independently audited; the specification status is for the
  reviewing session to set.
