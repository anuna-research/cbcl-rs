# chain (SPEC-035 REQ-3505, REQ-3502 c–d, REQ-3508 c; TEST-3504)

Branch `circus/chain/1`, worktree `cbcl-rs-chain-1`, 2026-11-04.
Generating model: Claude Fable 5.1. Host: macOS (Darwin 25.5.0), aarch64.

Changes:
- `crates/cbcl-state-proof/src/chain.rs` (new): `Chain { profile, links }`
  with private fields, `new` (rejects more than 64 links), `profile`, `links`,
  `to_json` / `from_json` (100,000-byte package limit, 64-link limit, per-link
  transcript size check through `Proof::check_size`), and `verify` implementing
  CON-3503: header profile equals the verifier's, each link's profile equals
  it, link 0 before equals `start`, link i before equals link i−1 after, each
  link verified with `verifier.verify(link, &link.statement)`, result is the
  last after or `start` for an empty chain, `expected_end` mismatch rejects.
  `MAX_LINKS = 64` is a public constant.
- `profile.rs`: `Profile::genesis(&self) -> Checkpoint` returning row 0's
  checkpoint (mask 0 is valid for every compiled profile).
- `lib.rs`: `Proof` derives `PartialEq, Eq` (`Statement` and `Checkpoint`
  already did); `Chain` and `MAX_LINKS` re-exported; `chain_tests` included
  under `#[cfg(test)]`.
- `chain_tests.rs` (new): 14 tests, one shared `Prover` behind a `OnceLock`
  producing the three real proofs empty → {opener} → {opener, first write} →
  all three; each transition checked against `profile.statement` first.

## Commands and results

`RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1`

```
     Running unittests src/lib.rs (target/debug/deps/cbcl_state_proof-32493cb2cbf048f7)
test result: ok. 26 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 30.91s
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
test exit=0
```

`cargo fmt --all --check`

```
fmt exit=0
```

`cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings`

```
    Checking cbcl-state-proof v0.1.1 (/Users/anuna-02/Code/cbcl-rs-chain-1/crates/cbcl-state-proof)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 3.58s
clippy exit=0
```

`cargo clippy --workspace --all-targets --locked -- -D warnings` (the `make check` clippy gate)

```
    Checking cbcl-cli v0.1.1 (/Users/anuna-02/Code/cbcl-rs-chain-1/crates/cbcl-cli)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 15.57s
workspace clippy exit=0
```

## Red gate

Tests were written first (`chain_tests.rs` plus the `mod chain_tests;` line in
`lib.rs`) and run before any implementation:

`RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1 chain_tests`

```
   1 error: could not compile `cbcl-state-proof` (lib test) due to 29 previous errors
   2 error[E0369]: binary operation `==` cannot be applied to type `Proof`
   1 error[E0425]: cannot find type `Chain` in this scope
  13 error[E0433]: cannot find type `Chain` in this scope
  13 error[E0599]: no method named `genesis` found for struct `profile::Profile` in the current scope
```

The three missing pieces (`Chain`, `Profile::genesis`, `PartialEq` on `Proof`)
are exactly what the task adds. After implementation the same command passed
14 of 14 chain tests, and the full crate run passed 26 of 26.

## Mutation

Removed the before-equals-previous-after comparison in `Chain::verify`
(the three-line `if statement.before != current { return Err(..) }` block) and
ran the chain tests:

```
test chain_tests::first_link_not_at_start_is_rejected ... FAILED
test chain_tests::gap_between_links_is_rejected ... FAILED
test chain_tests::swapped_links_are_rejected ... FAILED
thread 'chain_tests::gap_between_links_is_rejected' panicked at crates/cbcl-state-proof/src/chain_tests.rs:152:5
test result: FAILED. 11 passed; 3 failed; 0 ignored; 0 measured; 12 filtered out; finished in 16.37s
```

The named gap test fails as TEST-3504 requires. Reverted by restoring the
saved copy of `chain.rs`; `git diff --stat -- crates/cbcl-state-proof/src/chain.rs`
against the pre-mutation file showed no difference, and the final gate runs
above were made on the reverted code.

## Spec questions

- The 100,000-byte package limit applies to chains as written (CON-3502,
  REQ-3508 b). A two-link chain of real proofs for the three-candidate fixture
  fits (asserted in `json_round_trip_and_recogniser_limits`), but 64 real links
  cannot: transcripts serialise as JSON integer arrays, so a 64-link chain of
  real proofs is several hundred kilobytes. The 64-link limit is therefore
  only reachable with tiny transcripts under the current package format. I
  implemented both limits exactly as specified (fail closed); the 64-link
  tests use 32-byte placeholder transcripts so the link limit, not the byte
  limit, is what rejects.
- CON-3503 lists `links.len() <= 64` as a `Chain::verify` pre-condition.
  `new` and `from_json` already enforce it, so `verify` re-checks it
  defensively; it cannot fail there through the public API.

## Not done

Nothing left out. The crate README was not updated because the task did not
ask for it; a later task documenting the chain API should add a sentence on
`Chain` and `Profile::genesis`.
