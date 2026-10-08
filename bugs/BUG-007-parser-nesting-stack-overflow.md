---
id: BUG-007
title: "Balanced deep nesting overflows the parser's stack: browser WASM instances are poisoned, the BEAM node dies"
severity: S1
priority: P0
status: fixed-candidate
reported-by: "Svelte Chat source-adapter re-review 2, finding RR2-1 (cbcl-bus-svelte-plan)"
assigned-to: agent:claude-opus-5.5
reported-date: 2026-10-08
component: crates/cbcl-parser/src/parser.rs
---

# BUG-007: Balanced deep nesting overflows the parser's stack

**Severity:** S1 (Critical: one frame from any peer makes a client's verifier
terminally unavailable, or crashes the hub node).
**Priority:** P0. It blocks the Svelte Chat replacement.
**Status:** fixed-candidate. The fix is on branch
`circus/svelte-chat-parser-depth/1` and has not been merged.
**Fixed by:** agent:claude-opus-5.5 (Claude Code, Opus 5.5).

## Specification Reference

- **Violated:** [[SPEC-001#REQ-043]] claimed that fuel prevents unbounded
  stack growth. It does not. Fuel is proportional to input length, and one
  octet of `(` buys one level of recursion. The IETF draft's *Resource Bounding
  of Recognition* section required that recognition "never consumes unbounded
  stack".
- **Fixed by:** [[SPEC-001#REQ-046]], a fixed nesting limit of 256 enforced in
  `parse_with_fuel`.
- **Evidence:** [[parser-nesting-limit-evidence-2026-10-08]].

## Mechanism

`parse_expr` → `parse_list` → `parse_expr` recurses once per open list. The
only bound on that recursion was fuel, which defaults to the input's byte
length. So a frame of *n* balanced `(`…`)` recursed *n* levels deep. Every
downstream walker recursed *n* deep as well: message recognition, `read`'s
JSON, serialisation, `Debug`, drop.

- **Browser WASM:** the engine's stack overflows inside the module. Chromium
  then reports `memory access out of bounds` for every later call on that
  instance. The likely cause, which has not been confirmed, is that the trap
  leaves the module's shadow stack pointer unrestored. The source chat routes every member's decrypted MLS plaintext
  through this reader, so one member could make every recipient's client
  unusable.
- **BEAM NIF:** a stack overflow is not a Rust panic. The NIF's
  `catch_unwind` guard cannot contain it, and the whole node dies (SIGBUS).

## Reproduction (before the fix, at d2cbd96)

The same probes run against the base and fixed builds. Their full outputs are in
`outputs/parser-nesting-limit-2026-10-08/`.

| Host | Depth / input | Result before the fix |
|---|---|---|
| WebKit 26.0 (Playwright) | `parse_message`, depth 3000 (6 KB) | `RangeError: Maximum call stack size exceeded.`. `read` and `parse` at the same depth pass once, then overflow on the second call. |
| Chromium 145 | depth 7000 (14 KB) | `RangeError`, then `RuntimeError: memory access out of bounds` on every later call, benign frames included |
| Firefox 155 | depth 7000 | `InternalError: too much recursion` |
| BEAM (erl, release NIF) | `parse_message/1`, 1,000,000 × `(` | node exits with status 138 (SIGBUS) |
| `cargo test` | 1,000,000 × `(` | `thread has overflowed its stack`, SIGABRT |

## Root-cause taxonomy

- **Class:** resource exhaustion. The recursion depth was controlled by the
  input.
- **Origin:** a specification defect. REQ-043 treated a work bound (fuel) as
  a stack bound, and the implementation faithfully met the wrong requirement.

## Fix

`MAX_NESTING_DEPTH = 256` lives in `crates/cbcl-parser/src/parser.rs`. When
`parse_list` would open level 257, it returns
`ParseError::NestingTooDeep { offset, limit }` before recursing. The error
displays as `at byte <offset>: list nesting exceeds limit 256`. Every text entry
point reaches a tree through this one function, so there is no second scanner.
The list is the grammar's only recursive form; strings and comments are scanned
iteratively.

## Regression tests

- `crates/cbcl-parser/tests/nesting_limit.rs`: N-1, N and N+1; exact offsets;
  1,000,000 levels on a 256 KiB thread; siblings; strings and comments; every
  text export.
- `crates/cbcl-wasm/src/lib.rs`
  `over_deep_frames_are_refused_and_the_instance_stays_usable`.
- `crates/cbcl-erl/tests/nesting_limit.rs`, on a 320 KiB thread, plus
  REQ-046 checks in `crates/cbcl-erl/scripts/smoke.escript` on a real BEAM.
- `js/test/depth.test.ts` against the real wasm build, and
  `js/scripts/depth-probe.mjs` in Chromium, Firefox and WebKit.

## Downstream obligations

- The Chat client must pin a cbcl-rs build containing this fix. Its
  `parseSexpr`/`catch {}` call sites will then see an ordinary string refusal,
  not a fault. Fault classification (RR2-2) is still needed for other
  non-string throws, such as an out-of-memory error.
- The Lean model `Parser.lean` does not carry the limit yet; see the `Open:`
  entry in [[SPEC-001#REQ-046]] §3.5.1.
