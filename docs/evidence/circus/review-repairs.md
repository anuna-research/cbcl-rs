# review-repairs (SPEC-035 v0.2.2; TEST-3502, 3504, 3506, 3507, 3509, 3510)

Branch `circus/review-repairs/1`, worktree `cbcl-rs-review-repairs-1`, 2026-11-04.
Generating model: Claude Fable 5.1; recovered, verified and completed by Codex. Host: macOS (Darwin 25.5.0), aarch64.

Repairs of the accepted findings of the two independent code reviews recorded
in `docs/evidence/SPEC-035-halo2-state-checkpoints.md`. One line per item of
the task, with the covering test.

| # | Item | Status | Covering test |
|---|---|---|---|
| 1 | REQ-3512 (b): only one `lang` wrapper naming the installed dialect directly around a simple message binds (`dialect_bound` in `profile.rs`) | done | `tests::nested_or_wrapped_dialect_forms_invalidate_every_containing_set` |
| 2 | REQ-3504 (c): `from_field` scans like `keyword_fields` | done | `tests::attested_rejects_second_from_after_stray_positional_param` |
| 3 | REQ-3508 (a) / CON-3502: positional arrays rejected by `Proof::from_json` and `Chain::from_json` (JSON `Value` shape check before typed deserialisation) | done | `package_tests::positional_arrays_are_rejected`; round-trip, whitespace and duplicate tests unchanged and passing |
| 4 | REQ-3507 (b, c, d, h) / TEST-3506: size bounds and roles, 100 ms, one message per bound | done | `tests::size_bounds_and_roles_fail_before_enumeration` |
| 5 | REQ-3503 / REQ-3500: `forge_non_boolean_bit` test seam, Boolean gate named in the MockProver failures | done | `tests::non_boolean_selection_bit_is_rejected_by_the_boolean_gate` |
| 6 | REQ-3502 (b) / REQ-3505: early-rejection messages asserted | done | `tests::actual_proof_roundtrip_tampering_and_independent_verifier` ("unexpected checkpoint statement"); `chain_tests::foreign_profile_in_one_link_is_rejected` ("link 1: foreign profile"); `chain_tests::foreign_profile_in_header_is_rejected` ("chain profile differs") |
| 7 | REQ-3501 / TEST-3500: per-subset parity for the lunch-vote fixture | done | `tests::lunch_vote_native_fold_matches_for_every_valid_subset` (shared `assert_native_parity` helper, also used by `native_fold_and_replacement_match_for_every_valid_subset`) |
| 8 | REQ-3512 (c): `:sender` ≠ label and two `:from` fields at profile level | done | `tests::invalid_shape_sender_thread_and_dialect_are_constrained` (modes `sender-field`, `two-from`) |
| 9 | CON-3506 / TEST-3501: two proofs of one statement differ and both verify | done | `tests::actual_proof_roundtrip_tampering_and_independent_verifier` |
| 10 | REQ-3506 (d): whitespace inserted into candidate text | done | `tests::canonical_whitespace_and_unknown_candidates` |
| 11 | Remove `relation_id` alias; retain `check_len` in `Chain::verify` after independent review showed public `Deserialize` bypasses constructors | done with reviewed correction | `directly_deserialized_overlong_chain_is_rejected_before_verification`; clippy |
| 12 | Mutation runner generalised to file paths; mutants `unconstrained-transition-total` (test `tests::transition_total_must_equal_one_without_a_forged_sum`, new) and `chain-continuity-unchecked` (test `chain_tests::gap_between_links_is_rejected`) | done | `python3 scripts/state-proof-mutations.py`: 4 of 4 killed (below) |
| 13 | Fuzz target `state_proof_verify` | done | `cargo check --manifest-path fuzz/Cargo.toml --bin state_proof_verify --offline` |
| 14 | README | done | n/a (prose) |
| 15 | CLI: `read_file` through `take(limit + 1)`, hex checkpoints, repeated address rejected, positional arrays rejected | done | `compile_prove_verify_and_chain_verify_round_trip` (hex output equals golden mask 6), `malformed_profile_and_address_inputs_exit_one` (repeated address, top-level array, candidate array, 1 MiB file at the limit accepted) |

Notes on choices:

- Item 3: the task says to deserialise to `Value` and then `serde_json::from_value`.
  `Value` deserialisation silently keeps the last of two duplicate members, so
  `from_value` would lose the duplicate-member rejection the existing test
  `duplicate_member_is_rejected` requires. The recognisers therefore parse the
  bytes twice: once to `Value` for the object-shape check, then typed
  `from_slice` on the same bytes, which keeps the duplicate, size and
  trailing-input behaviour unchanged. Both parses are bounded by the package
  size checked first.
- Item 5: a non-Boolean bit is also caught downstream (sums and public limbs),
  so an `is_err()` assertion alone would not kill a removed Boolean selector.
  The test asserts the "Boolean selection" gate appears among the
  `MockProver` failures.
- Item 12: for the removed `constrain_constant(last.cell(), Fp::ONE)` the
  existing forged-sum test still fails on the recurrence gate, so it does not
  kill the mutant. The new test removes the pair from `transitions` without
  forging, so the honest total is 0 and only the final-total constant rejects.
- Item 13: `serde_json` is added to `fuzz/Cargo.toml` to read the fixture. It
  was already in `fuzz/Cargo.lock` through `cbcl-state-proof`; no new crate
  enters the graph and `--offline` resolves.
- CON-3505 says `verify` prints the after checkpoint as hex; the CLI output is
  `{"verified": true, "after": {"accepted": hex64, "state": hex64}}`.

## Commands and results

Recovered on 2026-11-04. Full captured output and command records are committed in `docs/evidence/circus/review-repairs-logs/`. All Cargo test runs set `RAYON_NUM_THREADS=2`.

`cargo test -p cbcl-state-proof --locked -- --test-threads=1` (exit 0):

```text
   Doc-tests cbcl_state_proof

running 1 test
test crates/cbcl-state-proof/src/candidate.rs - candidate::Candidate (line 21) - compile fail ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.05s
```

`cargo test -p cbcl-cli --features state-proof --locked` (exit 0):

```text
test protocol_referencing_undefined_performative_fails_r5 ... ok
test protocol_referencing_inherited_core_performative_passes_r5 ... ok
test crosschain_passes_r5_with_protocol ... ok
test protocol_free_dialects_pass_r5_vacuously ... ok

test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.03s
```

`cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings` (exit 0):

```text
   Compiling sha2-asm v0.6.4
    Checking sha2 v0.10.9
    Checking cbcl-core v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-core)
    Checking cbcl-parser v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-parser)
    Checking cbcl-state-proof v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-state-proof)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 1.81s
```

`cargo clippy -p cbcl-cli --all-targets --features state-proof --locked -- -D warnings` (exit 0):

```text
    Checking sha2 v0.10.9
    Checking cbcl-core v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-core)
    Checking cbcl-parser v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-parser)
    Checking cbcl-state-proof v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-state-proof)
    Checking cbcl-cli v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-cli)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 1.97s
```

`cargo check --manifest-path fuzz/Cargo.toml --bin state_proof_verify --offline` (exit 0):

```text
    Checking sha2 v0.10.9
    Checking cbcl-core v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-core)
    Checking cbcl-parser v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-parser)
    Checking cbcl-state-proof v0.1.1 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/crates/cbcl-state-proof)
    Checking cbcl-fuzz v0.0.0 (/Users/anuna-02/Code/cbcl-rs-review-repairs-1/fuzz)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 3.25s
```

`python3 scripts/state-proof-mutations.py` (exit 0):

```text
{"mutant": "unbound-after-state", "file": "circuit.rs", "test": "tests::every_public_limb_is_constrained_without_the_host_precheck", "exit_code": 101, "killed": true, "command": ["cargo", "test", "-p", "cbcl-state-proof", "--lib", "tests::every_public_limb_is_constrained_without_the_host_precheck", "--", "--test-threads=1"]}
{"mutant": "unconstrained-admission-transition", "file": "circuit.rs", "test": "tests::previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks", "exit_code": 101, "killed": true, "command": ["cargo", "test", "-p", "cbcl-state-proof", "--lib", "tests::previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks", "--", "--test-threads=1"]}
{"mutant": "unconstrained-transition-total", "file": "circuit.rs", "test": "tests::transition_total_must_equal_one_without_a_forged_sum", "exit_code": 101, "killed": true, "command": ["cargo", "test", "-p", "cbcl-state-proof", "--lib", "tests::transition_total_must_equal_one_without_a_forged_sum", "--", "--test-threads=1"]}
{"mutant": "chain-continuity-unchecked", "file": "chain.rs", "test": "chain_tests::gap_between_links_is_rejected", "exit_code": 101, "killed": true, "command": ["cargo", "test", "-p", "cbcl-state-proof", "--lib", "chain_tests::gap_between_links_is_rejected", "--", "--test-threads=1"]}
```

`make check` (exit 0):

```text

   Doc-tests cbcl_wasm

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
```

The standalone chain regression passes after restoring the guard (`chain-green.log`). The workspace run includes that regression.

`NO_COLOR=true zetl -d specs check --fail-on error` exits 0. Adding `--dead-links` exits 1 on the unchanged existing vault backlog; the parsed dead-link records equal those from the pre-repair integration branch exactly (`zetl.log`, `zetl-baseline.log`). No SPEC-035 dead link is introduced.

## Red gate

The interrupted attempt left no usable red-gate transcript. This continuation reconstructed the pre-repair production files from `HEAD` while retaining the new tests, executed each failing assertion below, then restored every file in a `finally` block. These are reconstructed regression checks, not a claim of historical test-first ordering.

`cargo test -p cbcl-state-proof --lib nested_or_wrapped_dialect_forms_invalidate_every_containing_set --locked -- --test-threads=1` (exit 101):

```text
test tests::nested_or_wrapped_dialect_forms_invalidate_every_containing_set ... FAILED
thread 'tests::nested_or_wrapped_dialect_forms_invalidate_every_containing_set' (11456444) panicked at crates/cbcl-state-proof/src/tests.rs:740:9:
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 52 filtered out; finished in 0.00s
```

`cargo test -p cbcl-state-proof --lib attested_rejects_second_from_after_stray_positional_param --locked -- --test-threads=1` (exit 101):

```text
test tests::attested_rejects_second_from_after_stray_positional_param ... FAILED
thread 'tests::attested_rejects_second_from_after_stray_positional_param' (11456499) panicked at crates/cbcl-state-proof/src/tests.rs:771:5:
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 52 filtered out; finished in 0.00s
```

`cargo test -p cbcl-state-proof --lib positional_arrays_are_rejected --locked -- --test-threads=1` (exit 101):

```text
test package_tests::positional_arrays_are_rejected ... FAILED
thread 'package_tests::positional_arrays_are_rejected' (11456546) panicked at crates/cbcl-state-proof/src/package_tests.rs:106:5:
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 52 filtered out; finished in 0.00s
```

`cargo test -p cbcl-state-proof --lib size_bounds_and_roles_fail_before_enumeration --locked -- --test-threads=1` (exit 101):

```text
test tests::size_bounds_and_roles_fail_before_enumeration ... FAILED
thread 'tests::size_bounds_and_roles_fail_before_enumeration' (11456590) panicked at crates/cbcl-state-proof/src/tests.rs:803:5:
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 52 filtered out; finished in 0.00s
```

`cargo test -p cbcl-cli --features state-proof --locked --test checkpoint malformed_profile_and_address_inputs_exit_one` (exit 101):

```text
test malformed_profile_and_address_inputs_exit_one ... FAILED
thread 'malformed_profile_and_address_inputs_exit_one' (11457562) panicked at crates/cbcl-cli/tests/checkpoint.rs:234:5:
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 2 filtered out; finished in 6.83s
```

The independent reviewer then found that removing `Chain::verify`'s length guard violated [[SPEC-035-halo2-state-checkpoints#REQ-3505]] through public serde deserialization. The new `directly_deserialized_overlong_chain_is_rejected_before_verification` test failed first with `left: "link 0: invalid proof"`, `right: "chain exceeds link limit"` (exit 101, `chain-red.log`), then passed after restoring the guard (exit 0, `chain-green.log`). The test intentionally uses an invalid transcript so the error establishes that the link bound is enforced before backend verification.

## Mutation

`python3 scripts/state-proof-mutations.py` exits 0. Each named test executed and failed on its assertion with exit 101; compilation errors are excluded by the runner. Sources were restored after each run.

```json
[
  {
    "mutant": "unbound-after-state",
    "file": "circuit.rs",
    "test": "tests::every_public_limb_is_constrained_without_the_host_precheck",
    "exit_code": 101,
    "killed": true,
    "command": [
      "cargo",
      "test",
      "-p",
      "cbcl-state-proof",
      "--lib",
      "tests::every_public_limb_is_constrained_without_the_host_precheck",
      "--",
      "--test-threads=1"
    ]
  },
  {
    "mutant": "unconstrained-admission-transition",
    "file": "circuit.rs",
    "test": "tests::previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks",
    "exit_code": 101,
    "killed": true,
    "command": [
      "cargo",
      "test",
      "-p",
      "cbcl-state-proof",
      "--lib",
      "tests::previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks",
      "--",
      "--test-threads=1"
    ]
  },
  {
    "mutant": "unconstrained-transition-total",
    "file": "circuit.rs",
    "test": "tests::transition_total_must_equal_one_without_a_forged_sum",
    "exit_code": 101,
    "killed": true,
    "command": [
      "cargo",
      "test",
      "-p",
      "cbcl-state-proof",
      "--lib",
      "tests::transition_total_must_equal_one_without_a_forged_sum",
      "--",
      "--test-threads=1"
    ]
  },
  {
    "mutant": "chain-continuity-unchecked",
    "file": "chain.rs",
    "test": "chain_tests::gap_between_links_is_rejected",
    "exit_code": 101,
    "killed": true,
    "command": [
      "cargo",
      "test",
      "-p",
      "cbcl-state-proof",
      "--lib",
      "chain_tests::gap_between_links_is_rejected",
      "--",
      "--test-threads=1"
    ]
  }
]
```

## Spec questions

- CON-3502 says the recogniser "is `serde_json::from_slice` into the Rust
  types" and also that "the recogniser checks object shape before typed
  deserialisation". Read as: the language is what the typed deserialiser
  accepts minus positional arrays in object positions. Implemented as a
  `Value` shape pass followed by the typed `from_slice` (see item 3 note).
- REQ-3512 (b) says a candidate "that carries more than one dialect wrapper
  between the outer `lang` and the simple message" is unbound. A `signed` or
  `envelope` wrapper between the `lang` wrapper and the simple message is not a
  dialect wrapper, but it is also not the "`lang`-wrapped simple message" of
  CON-3500's input grammar. Chosen reading (fail closed): the inner message of
  the single `lang` wrapper must be `Message::Simple`; any other form is
  unbound. The test covers nested `lang` (other and same name) and `signed`.

## Not done

No repair item remains incomplete. Item 11 intentionally retains the required verification bound; the independent reviewer confirmed that correction. Long fuzz campaigns, human cryptographic review, production authorisation, incremental kernels, recursive composition and Lean correspondence remain with the CBCL maintainer as recorded in [[SPEC-035-halo2-state-checkpoints]]. The spec status remains for the independent reviewing session to decide.


## Independent repair review

A fresh-context Codex reviewer received only [[SPEC-035-halo2-state-checkpoints]] and the deliverable, with a mandate to find defects. It identified the removed chain-length guard as a correctness regression against [[SPEC-035-halo2-state-checkpoints#REQ-3505]] / [[SPEC-035-halo2-state-checkpoints#CON-3503]]. This continuation reproduced it, restored the check, and added the regression above. On reinspection the reviewer confirmed the fix and found no additional correctness defect in the inspected repairs. The reviewer ran no tests; executed gate evidence is recorded separately above. It will make the status decision in a separate reviewing session.
