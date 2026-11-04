# workspace-gates (SPEC-035 REQ-3509, TEST-3508)

Branch `circus/workspace-gates/1`, worktree `cbcl-rs-workspace-gates-1`, 2026-11-04.
Generating model: Claude Fable 5.1. Host: macOS (Darwin 25.5.0), aarch64.

Changes: `git mv experiments/state-proof/mutate.py scripts/state-proof-mutations.py`
(`ROOT` now `parents[1]`, `EVIDENCE` now `docs/evidence/state-proof-mutations/`,
`mkdir(parents=True)`); one comment line in `mutants.toml`; one sentence in
`README.md`; the crate README's evidence block now names the moved runner.
No Rust source, `Cargo.toml` or `Cargo.lock` change was needed: the first
`make check` was already green with the crate present.

## Commands and results

`cargo fmt --all --check`

```
fmt exit=0
```

`cargo clippy --workspace --all-targets --locked -- -D warnings`

```
    Checking cbcl-cli v0.1.1 (/Users/anuna-02/Code/cbcl-rs-workspace-gates-1/crates/cbcl-cli)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 3.24s
clippy exit=0
```

`RAYON_NUM_THREADS=2 cargo test --workspace --locked` (run twice: before and after the changes)

```
suites=55 passed=1582 failed=0        # first run
suites=55 passed=1582 failed=0        # second run
test exit=0
```

No `FAILED` or `panicked` lines in either run; no rerun of any flaky test was needed.

`RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1`

```
     Running unittests src/lib.rs (target/debug/deps/cbcl_state_proof-32493cb2cbf048f7)
test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 14.87s
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
crate test exit=0
```

`cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings`

```
    Checking cbcl-state-proof v0.1.1 (/Users/anuna-02/Code/cbcl-rs-workspace-gates-1/crates/cbcl-state-proof)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 2.38s
crate clippy exit=0
```

`python3 scripts/state-proof-mutations.py`

```
{"mutant": "unbound-after-state", "test": "every_public_limb_is_constrained_without_the_host_precheck", "exit_code": 101, "killed": true, ...}
{"mutant": "unconstrained-admission-transition", "test": "previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks", "exit_code": 101, "killed": true, ...}
runner exit=0
```

Output committed at `docs/evidence/state-proof-mutations/` (`mutations.json`, two logs).
`git status` after the run showed `crates/cbcl-state-proof/src/circuit.rs` unmodified (sources restored).

`cargo tree -i cbcl-state-proof --workspace 2>&1 | head -20`

```
cbcl-state-proof v0.1.1 (/Users/anuna-02/Code/cbcl-rs-workspace-gates-1/crates/cbcl-state-proof)
```

Only `cbcl-state-proof` is listed.

`cargo check -p cbcl-core --no-default-features`

```
error: cannot find macro `vec` in this scope
   --> crates/cbcl-core/src/blame.rs:120:37
error: could not compile `cbcl-core` (lib) due to 1 previous error
exit=101
```

Pre-existing, not caused by this branch: `git diff main -- crates/cbcl-core` is empty,
and the identical command on a `git archive main` export (in `/tmp`, since deleted)
fails with the same error and `exit=101`. See `## Not done`.

`rustup target list --installed` includes `wasm32-unknown-unknown`.

`cargo check -p cbcl-wasm --target wasm32-unknown-unknown`

```
warning: `cbcl-wasm` (lib) generated 2 warnings
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 4.34s
exit=0
```

The two warnings are pre-existing in `cbcl-wasm` and unrelated to the new crate.

`mutants.toml`: `examine_re` lists only `cbcl-parser` and `cbcl-core` files; no
`cbcl-state-proof` entry. Added one comment line above `examine_re`.

## Red gate

Before step 2:

```
$ python3 scripts/state-proof-mutations.py
/Library/Developer/CommandLineTools/usr/bin/python3: can't open file '/Users/anuna-02/Code/cbcl-rs-workspace-gates-1/scripts/state-proof-mutations.py': [Errno 2] No such file or directory
exit=2
```

## Mutation

Satisfied by the runner's own two mutants of `crates/cbcl-state-proof/src/circuit.rs`
(the task adds no Rust behaviour of its own):

- `unbound-after-state`: skips `constrain_instance` for public limb 8. Named test
  `every_public_limb_is_constrained_without_the_host_precheck` panicked at
  `tests.rs:172:9`; `test result: FAILED. 0 passed; 1 failed`.
- `unconstrained-admission-transition`: removes `config.transition.enable`. Named test
  `previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks`
  panicked at `tests.rs:193:5`; `test result: FAILED. 0 passed; 1 failed`.

The runner restores `circuit.rs` in a `finally` block; `git status` confirmed no
diff in `crates/cbcl-state-proof/src` afterwards, and the subsequent full
`cargo test --workspace --locked` passed on the restored source.
`mutations.json` is at `docs/evidence/state-proof-mutations/mutations.json`.

## Spec questions

- TEST-3508 says `cargo check -p cbcl-core --no-default-features` is "unchanged".
  It fails identically on `main` (missing `use alloc::vec` in `blame.rs`), so it
  is unchanged but not passing. Chosen reading: record, do not fix; the task
  limits fixes to failures caused by the new crate and the fix is outside this
  crate. Fail closed: the evidence reports the failing exit code verbatim.

## Not done

- `cargo check -p cbcl-core --no-default-features` exits 101 on this branch and on
  `main` for a pre-existing `no_std` bug in `crates/cbcl-core/src/blame.rs:120`.
  Not fixed here: it is not caused by `cbcl-state-proof` and the task forbids
  touching unrelated code. It needs its own fix (and a `no_std` CI gate).
