# attested-candidates (SPEC-035 REQ-3504, REQ-3512; TEST-3503)

Branch `circus/attested-candidates/1`, worktree `cbcl-rs-attested-candidates-1`.

Change: new `crates/cbcl-state-proof/src/candidate.rs` holding `Candidate`
with private `text`/`label`, constructors `unauthenticated` and `attested`
(R4 v2 header via `attestation_header_for`, `verify_attestation_v2`, exactly
one `:from` whose `KeyId` equals the header sender, label = `:from` as
written, text = canonical serialisation of the whole message), accessors
`text()`/`label()`, a `compile_fail` doctest on the struct literal, and a
shared `from_field` helper now also used by `profile.rs::sender_matches`
(REQ-3512 c unchanged: mismatching sets are invalid, compile succeeds).
`profile.rs`, `tests.rs`, `chain_tests.rs` and `examples/checkpoint.rs` use
the constructors and accessors; no `Candidate { .. }` literal exists outside
`candidate.rs`. README gains four lines on the two constructors.

## Commands and results

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1
running 31 tests
test result: ok. 30 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 33.29s
   Doc-tests cbcl_state_proof
running 1 test
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.12s

$ cargo fmt --all --check
(no output) exit 0

$ cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings
    Checking cbcl-state-proof v0.1.1 (.../crates/cbcl-state-proof)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.55s
exit 0
```

The one ignored test is the pre-existing `write_golden_vector` regenerator.
The single doctest is the `compile_fail` block on `Candidate`.

## Red gate

Tests `attested_candidates_bind_from_label_and_match_unauthenticated_profile`
and `attested_rejects_forged_altered_and_mismatched_candidates` were written
with `Candidate::attested` stubbed to `Err("not implemented")`:

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked attested -- --test-threads=1
running 2 tests
test tests::attested_candidates_bind_from_label_and_match_unauthenticated_profile ... FAILED
test tests::attested_rejects_forged_altered_and_mismatched_candidates ... FAILED
---- tests::attested_candidates_bind_from_label_and_match_unauthenticated_profile stdout ----
thread ... panicked at crates/cbcl-state-proof/src/tests.rs:586:37:
called `Result::unwrap()` on an `Err` value: "not implemented"
---- tests::attested_rejects_forged_altered_and_mismatched_candidates stdout ----
thread ... panicked at crates/cbcl-state-proof/src/tests.rs:612:5:
assertion failed: Candidate::attested(&message, &signature, &KEY).is_ok()
test result: FAILED. 0 passed; 2 failed; 0 ignored; 0 measured; 29 filtered out
```

After restoring the body both tests passed. Two test-side fixes were needed
on the way (not implementation changes): `:sender` is written as a string
because `@ed25519:b` does not tokenise as one symbol (the reader produced
"keyword :b missing value"), and the positive profile assertion targets the
opener rather than the full set because adding `:sender` changes the content
addresses the fixture's `:caused-by`/`:replaces` references point at.

## Mutation

Broke the `KeyId` equality check in `candidate.rs` by prefixing it with
`false &&`:

```
65:        if false && KeyId::parse(from).map_err(|e| e.to_string())? != header.from {
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked attested_rejects -- --test-threads=1
test tests::attested_rejects_forged_altered_and_mismatched_candidates ... FAILED
thread ... panicked at crates/cbcl-state-proof/src/tests.rs:635:5:
assertion failed: attest(&owner.replace(":from @owner", ":from @impostor"), &KEY).is_err()
```

Reverted; `grep` confirms line 65 reads
`if KeyId::parse(from).map_err(|e| e.to_string())? != header.from {` and the
full suite passes (see above).

## Spec questions

- CON-3504 says `text()` is "the canonical serialisation of the whole message
  as given". `SExpr::from(&Message)` re-emits `:thread` and `:sender` as
  strings whatever the source spelling, so `text()` can differ byte-wise from
  the source while re-parsing to the same message and address. I took the
  serialiser's output as "canonical"; profile identity is unaffected because
  `Profile::compile` canonicalises every candidate the same way (asserted by
  the positive test).
- TEST-3503 "a `:from` naming a different key than `:sender`": I read this as
  rejection by `attested` (REQ-3504 c), while the same mismatch expressed via
  the label stays a profile-level invalid set (REQ-3512 c). Both are tested.

## Not done

Nothing. One scope note: the positive attested profile is asserted admissible
for the opener only, since the fixture's child messages reference the
opener's pre-`:sender` address; identity and address equality with the
unauthenticated profile are asserted over all three candidates.
