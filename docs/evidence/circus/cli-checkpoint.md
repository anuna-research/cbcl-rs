# cli-checkpoint — SPEC-035 REQ-3510, CON-3505, TEST-3509

Branch `circus/cli-checkpoint/1`. Generating model: Claude Fable 5.1.
Machine: Darwin 25.5.0, rustc 1.95.0.

Files: `crates/cbcl-cli/Cargo.toml` (feature `state-proof`, optional
`cbcl-state-proof` and `serde`), `crates/cbcl-cli/src/main.rs` (gated
`Checkpoint` variant), `crates/cbcl-cli/src/checkpoint.rs` (new, feature-only),
`crates/cbcl-cli/tests/checkpoint.rs` (new, `#![cfg(feature = "state-proof")]`),
`Cargo.lock` (two new optional edges on `cbcl-cli`; needed for `--locked`).

## Commands and results

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-cli --features state-proof --locked
     Running unittests src/main.rs
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
     Running tests/checkpoint.rs
test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 53.64s
     Running tests/verify_cli.rs
test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.02s

$ RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1
     Running unittests src/lib.rs
test result: ok. 30 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 32.27s
   Doc-tests cbcl_state_proof
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.11s

$ cargo fmt --all --check
(no output, exit 0)

$ cargo clippy -p cbcl-cli --all-targets --features state-proof --locked -- -D warnings
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 5.56s

$ cargo clippy -p cbcl-cli --all-targets --locked -- -D warnings
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 6.01s

$ cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 4.20s

$ cargo run -q -p cbcl-cli --locked -- checkpoint compile x.json      # no feature
error: unrecognized subcommand 'checkpoint'

Usage: cbcl-cli <COMMAND>

For more information, try '--help'.
exit code: 2

$ cargo tree -i cbcl-state-proof --locked
cbcl-state-proof v0.1.1 (…/crates/cbcl-state-proof)
$ cargo tree -i cbcl-state-proof --locked -p cbcl-cli --features state-proof
cbcl-state-proof v0.1.1 (…/crates/cbcl-state-proof)
└── cbcl-cli v0.1.1 (…/crates/cbcl-cli)
```

Real proving runs: two (`prove - -> opener`, `prove opener -> opener+write`),
both with `RAYON_NUM_THREADS=2`; every other run is compile/verify only.

## Red gate

Feature and test written first; no `Checkpoint` variant and no module.

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-cli --features state-proof --locked --test checkpoint
---- compile_prove_verify_and_chain_verify_round_trip stdout ----
thread 'compile_prove_verify_and_chain_verify_round_trip' panicked at crates/cbcl-cli/tests/checkpoint.rs:34:5:
missing warning line in stderr: error: unrecognized subcommand 'checkpoint'
---- malformed_profile_and_address_inputs_exit_one stdout ----
thread 'malformed_profile_and_address_inputs_exit_one' panicked at crates/cbcl-cli/tests/checkpoint.rs:34:5:
missing warning line in stderr: error: unrecognized subcommand 'checkpoint'
failures:
    compile_prove_verify_and_chain_verify_round_trip
    malformed_profile_and_address_inputs_exit_one
test result: FAILED. 1 passed; 2 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.50s
```

(`usage_errors_exit_two` passed before implementation because clap already
exits 2 on the unknown subcommand; it is kept as the usage-error check.)

## Mutation

Mutation (one line in `checkpoint.rs`, `Op::Verify`): verify against the
package's own statement instead of the receiver-derived one.

```
-            Verifier::new(profile)?.verify(&proof, &expected)?;
+            Verifier::new(profile)?.verify(&proof, &proof.statement)?;
```

```
$ RAYON_NUM_THREADS=2 cargo test -p cbcl-cli --features state-proof --locked --test checkpoint compile_prove
test compile_prove_verify_and_chain_verify_round_trip ... FAILED
thread 'compile_prove_verify_and_chain_verify_round_trip' panicked at crates/cbcl-cli/tests/checkpoint.rs:125:5:
assertion `left == right` failed: stdout: {"verified":true,"after":{...}}
  left: 0
 right: 1
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 2 filtered out; finished in 21.92s
```

Line 125 is the wrong-`--after` assertion (`verify` with `--after <opener>`
against the opener→two proof must exit 1). Reverted; `grep -n "verify(&proof"`
shows `verify(&proof, &expected)` and the full gate run above is post-revert.

## Spec questions

1. The task says "no new dependencies" and also "a serde struct with
   `deny_unknown_fields`". `cbcl-cli` had no `serde` dependency and neither
   `cbcl-core` nor `cbcl-state-proof` re-exports the derive. I added `serde`
   as an optional dependency enabled only by the `state-proof` feature, so the
   default build graph is unchanged (REQ-3509 b, REQ-3510 "binary unchanged").
2. CON-3505 does not say what `verify` prints on success or what `prove` prints
   on stdout when `--out` is given. Chosen: `verify` prints
   `{"verified":true,"after":<Checkpoint>}`; `prove --out` prints nothing on
   stdout. Both are compact JSON single lines where anything is printed.
3. CON-3502 (v0.2.1) sets the chain package limit at 1,048,576 bytes, but the
   library's `Chain::from_json` still caps at `MAX_PACKAGE` = 100,000 bytes
   (`chain.rs` imports the proof limit). The CLI caps the chain file read at
   1 MiB and lets the library recogniser decide after that, so it fails closed
   under either reading. Raising the library limit is outside this task.
4. Malformed address lists (not `-`, not `sha256-<hex64>`, unknown to the
   profile) are treated as rejections (exit 1), not usage errors (exit 2):
   they are data, recognised after the profile is compiled. Usage errors
   (missing required `--before`/`--after`, unknown subcommand) exit 2 via clap.

## Not done

Nothing left out from the task list. Not covered by an executed test: a
without-feature test in the same build (impossible, as the task states); the
no-feature behaviour is recorded above from a manual run.
