---
id: BUG-004
title: "`cbcl-cli verify <file>` parses the path as dialect text and rejects every valid dialect"
severity: S3
priority: P1
status: new
reported-by: agent:claude-opus-5
assigned-to: unassigned
reported-date: 2026-08-09
component: crates/cbcl-cli/src/main.rs
---

# BUG-004: `cbcl-cli verify <file>` parses the path as dialect text and rejects every valid dialect

**Severity:** S3 (Moderate — a workaround exists)
**Priority:** P1 (the failure is confidently wrong, and it is on the README's
Quick start path)
**Status:** new
**Reported by:** agent:claude-opus-5 (Claude Code, 1M-context Opus 5)
**Assigned to:** unassigned

## Specification Reference

- **Violates:** `README.md:31`, which documents
  `cargo run -p cbcl-cli -- verify dialect.scm` as the way to verify a dialect.
  No `REQ-###` covers the CLI's input convention, so this is also a spec gap.
- **Related:** every file under `dialects/` is unverifiable by the documented
  command, including `usdd-work.cbcl`, `elephant.cbcl`, and `cli.cbcl`.

## Environment

- Repository: `cbcl-rs` at commit `634e997`, branch `codex/spec-053-selfsame-nif`
- Toolchain: the workspace pin in `rust-toolchain.toml`
- Detection method: attempted to verify a newly authored dialect while drafting
  `circus/specs/SPEC-002-leaderless-dispatch-loop.md`

## Steps to Reproduce

1. `cd cbcl-rs`
2. `cargo run -q -p cbcl-cli -- verify dialects/usdd-work.cbcl`
3. Observe the output.

## Expected Behaviour

The dialect is read from the named file and verified. `README.md:31` states the
command in exactly this form, and the `[INPUT]` metavar in
`verify --help` reads as a path to a reader following that README.

## Actual Behaviour

```console
$ cargo run -q -p cbcl-cli -- verify dialects/usdd-work.cbcl
dialect parse error: dialect definition must be a list
```

The shipped, valid dialect is reported as malformed. Redirecting the same file
through stdin verifies it:

```console
$ cargo run -q -p cbcl-cli -- verify < dialects/usdd-work.cbcl
dialect 'cbcl-usdd-work' passed all safety checks (R1, R2, R3, R5)
  performatives: 7
  resource bounds: depth=8, expansion=1024, time=30ms
  R5: pass
```

## Evidence

`crates/cbcl-cli/src/main.rs:82`:

```rust
fn read_input(arg: Option<String>) -> String {
    if let Some(input) = arg {
        input
    } else {
        let mut buf = String::new();
        io::stdin()
            .read_to_string(&mut buf)
            .expect("failed to read stdin");
        buf
    }
}
```

The positional argument is returned verbatim as the dialect *text*. So
`verify dialects/usdd-work.cbcl` attempts to parse the 25-character string
`dialects/usdd-work.cbcl` as a dialect definition. That string is an atom rather
than a list, which is exactly what the error says — the diagnostic is accurate
about the input it was given and useless about the input the user meant.

`cmd_parse` shares `read_input`, so `cbcl-cli parse <file>` has the same
behaviour.

## Root Cause

- **Category:** spec-gap
- **Analysis:** the CLI has no declared convention for whether a positional
  argument is a literal or a path, and the README assumes the opposite of what
  the code does. The help text (`Input dialect definition (reads from stdin if
  omitted)`) is defensible in isolation, which is why the divergence survived:
  each artefact is self-consistent and they contradict each other.

  The failure mode is the one that makes this worth a P1 rather than a
  documentation fix. A valid dialect is reported as invalid, with a message that
  describes a real property of a string the user never wrote. An agent
  authoring a dialect and following the README concludes its own work is
  malformed and edits correct output until it gives up.

## Proposed Resolution

Any one of the three closes it. The first is preferred.

1. **Treat an existing path as a path.** If the positional argument names a
   readable file, read it; otherwise treat it as literal text. Add
   `--file`/`-f` for the unambiguous form. This makes the README correct with no
   documentation change and keeps every existing invocation working.
2. **Path only.** Make the positional argument a path, and require `-` or an
   omitted argument for stdin. Cleanest convention, and it breaks any caller
   passing a literal.
3. **Documentation only.** Change `README.md:31` to
   `cargo run -p cbcl-cli -- verify < dialect.scm` and rename the metavar to
   `[DEFINITION]`. Cheapest, and it leaves the confident-wrong-answer failure
   mode in place for the next reader who guesses.

## Regression Test

Whichever resolution lands, add a CLI test that verifies a dialect **from a
file path** and asserts a zero exit, using `dialects/usdd-work.cbcl` as the
fixture. The absence of that test is why a documented command could stop working
without anything noticing — this is a `test-gap` alongside the `spec-gap`.
