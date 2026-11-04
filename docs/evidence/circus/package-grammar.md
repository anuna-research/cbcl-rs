# package-grammar — SPEC-035 REQ-3508, TEST-3507

Branch `circus/package-grammar/1`, worktree `cbcl-rs-package-grammar-1`,
2026-11-04.

## What changed

- `crates/cbcl-state-proof/src/package_tests.rs` (new, `#[cfg(test)]`):
  CON-3502 recognition tests for `Proof` and `Chain`, a `proptest`
  round-trip property (64 cases), and the REQ-3508 (d) `check_size` unit test.
- `crates/cbcl-state-proof/src/lib.rs`: `MAX_CHAIN_PACKAGE = 1_048_576`;
  doc comments on `Proof::to_json`, `Proof::from_json` and `Prover::prove`
  stating what each guarantees and rejects.
- `crates/cbcl-state-proof/src/chain.rs`: `Chain::to_json`/`from_json` use
  `MAX_CHAIN_PACKAGE` (was `MAX_PACKAGE`, 100,000). Proof limit unchanged.
- `crates/cbcl-state-proof/src/chain_tests.rs`: oversize-chain line uses the
  new constant (still rejects; not weakened).
- `crates/cbcl-state-proof/src/tests.rs`: `fixture` and `masks` made
  `pub(crate)` so the new module builds one real proof.
- `crates/cbcl-state-proof/Cargo.toml`: `proptest = "1"` dev-dependency
  (already in the workspace lock via cbcl-core); `Cargo.lock` gains one line.
- `crates/cbcl-state-proof/README.md`: limits paragraph updated.
- `fuzz/fuzz_targets/state_proof_package.rs` (new) and `fuzz/Cargo.toml`:
  dependency and `[[bin]]` entry. `fuzz/Cargo.lock` re-resolved offline to
  include the new dependency tree.

## Commands and results

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1
test result: ok. 44 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 38.69s
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.22s

$ cargo fmt --all --check
(no output; exit 0)

$ cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings
    Checking cbcl-state-proof v0.1.1 (/Users/anuna-02/Code/cbcl-rs-package-grammar-1/crates/cbcl-state-proof)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.65s

$ cargo check --manifest-path fuzz/Cargo.toml --offline --bin state_proof_package
    Checking cbcl-fuzz v0.0.0 (/Users/anuna-02/Code/cbcl-rs-package-grammar-1/fuzz)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.26s

$ cargo check --manifest-path fuzz/Cargo.toml --offline        # whole fuzz crate
error[E0063]: missing fields `causal_locality`, `causal_protocol`, `roles` and 3 other fields in initializer of `cbcl_core::dialect::Dialect`
error[E0063]: missing field `role` in initializer of `PerformativeDef`
error: could not compile `cbcl-fuzz` (bin "constraint_check") due to 2 previous errors
error: could not compile `cbcl-fuzz` (bin "template_expand") due to 2 previous errors
```

The two failing fuzz bins (`constraint_check`, `template_expand`) are untouched
since the initial commit and construct `Dialect` literals that predate fields
added later; they fail identically without this change. The new target and the
other four bins compile.

## Red gate

Tests were written first and run against the unchanged crate.

First run (no `proptest` dev-dependency, no `MAX_CHAIN_PACKAGE`): compile
failure.

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked package_tests -- --test-threads=1
error[E0425]: cannot find value `MAX_CHAIN_PACKAGE` in this scope   (x6)
error[E0433]: cannot find module or crate `proptest` in this scope  (x2)
error[E0405]: cannot find trait `Strategy` in this scope            (x4)
error: cannot find macro `proptest` in this scope
error: could not compile `cbcl-state-proof` (lib test) due to 15 previous errors
```

Second run, with only the dev-dependency and the constant declared and
`chain.rs` still enforcing the old 100,000-byte limit:

```
test package_tests::chain_package_limit_is_1_048_576_bytes ... FAILED
test package_tests::chain_round_trips ... FAILED
test package_tests::sixty_four_real_links_round_trip_and_sixty_five_are_rejected ... FAILED
thread 'package_tests::chain_package_limit_is_1_048_576_bytes' panicked at crates/cbcl-state-proof/src/package_tests.rs:178:62:
called `Result::unwrap()` on an `Err` value: "chain package exceeds limit"
thread 'package_tests::chain_round_trips' panicked at crates/cbcl-state-proof/src/package_tests.rs:293:1:
Test failed: called `Result::unwrap()` on an `Err` value: "chain package exceeds limit".
test result: FAILED. 11 passed; 3 failed; 0 ignored; 0 measured; 31 filtered out; finished in 9.35s
```

The duplicate-member, byte-value, trailing-whitespace, member-order and h32
tests passed on the first behavioural run: the behaviour was already provided
by `serde_json` with `deny_unknown_fields` but had no test. The mutation below
shows these tests detect a recogniser regression.

One test needed a correction after the limit change: four maximal links, not
three, are needed to exceed the 100,000-byte proof limit (three come to just
under it). Fixed and rerun.

## Mutation

Removed `#[serde(deny_unknown_fields)]` from `Statement` in `profile.rs`
(one-line deletion, `git diff --stat`: `1 deletion(-)`).

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked package_tests::unknown_member -- --test-threads=1
test package_tests::unknown_member_is_rejected ... FAILED
thread 'package_tests::unknown_member_is_rejected' panicked at crates/cbcl-state-proof/src/package_tests.rs:82:5:
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 44 filtered out; finished in 0.00s
```

Reverted with `git checkout crates/cbcl-state-proof/src/profile.rs`
(`git diff --stat` empty), rerun:

```
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 44 filtered out; finished in 0.00s
```

## Spec questions

- CON-3502 says a byte has "no fraction, exponent or sign". The tests check
  `1.0`, `1e0`, `-1`, `+1`, `01`, `"1"`, `true` and `null` are all rejected.
  `serde_json` also rejects `1.0` for `u8` even though RFC 8259 treats it as a
  number; the spec's stricter reading is the one implemented. No change needed.
- TEST-3507 says "a 64-link chain of real proofs accepted". The task says
  recognition only, no verify; the test round-trips one real proof repeated
  64 times through `to_json`/`from_json` and does not call `verify` (64
  identical links would not chain anyway). Taken as the intended reading.
- The fuzz check could only be run offline. `fuzz/Cargo.lock` is a separate
  lockfile and had to be re-resolved to add the `cbcl-state-proof` tree; the
  offline resolver also moved a few already-stale entries (for example
  `cbcl-core` 0.1.0 to 0.1.1, matching the workspace). Nothing in the main
  `Cargo.lock` changed except the new dev-dependency edge.

## Not done

- `cargo check --manifest-path fuzz/Cargo.toml` for the whole fuzz crate fails
  on two pre-existing targets (`constraint_check`, `template_expand`) that are
  out of date with `cbcl_core::dialect::Dialect`. Not touched: outside this
  task. The new `state_proof_package` target checks clean on its own
  (`--bin state_proof_package`).
- The fuzz target was not run (`cargo fuzz` is not installed); the spec names
  the CBCL maintainer as owner of the depth run.
