# Parser nesting limit evidence (2026-10-08)

This report is the evidence for [[SPEC-001#REQ-046]] and the fix of
[[BUG-007-parser-nesting-stack-overflow]]. The candidate is on branch
`circus/svelte-chat-parser-depth/1`, based on
`d2cbd968e36dbc0d5876a878e65a89942386890c`, and has not been merged. The raw
logs are in `outputs/parser-nesting-limit-2026-10-08/`, with local paths
replaced by `<worktree>` and `~`. The work was produced by Claude Opus 5.5
(Claude Code) in an isolated Circus worktree.

## What changed

- **The limit.** `parser.rs` gains `MAX_NESTING_DEPTH = 256`, a `depth` counter
  in `ParserState`, and `ParseError::NestingTooDeep { offset, limit }`.
  `parse_list` checks the counter before it consumes the `(` and recurses. It
  increments the counter on entry and decrements it on exit, so sibling lists
  do not accumulate depth.
- **One choke point.** Every text entry point reaches a tree through
  `parse_with_fuel`: `parse`, explicit-fuel parsing, the pipeline, `read`, and
  the dialect, state, shape and object exports. The same holds for the wasm
  byte and bindgen exports, the Erlang NIFs and the C FFI. No second scanner
  was added. The `FromStr for SExpr` recogniser in `cbcl-core` is the separate
  issue [[BUG-005-two-sexpr-recognisers-disagree]]; only tests and benches call it, and it is unchanged.
- **Recursive forms.** The grammar (`docs/cbcl-grammar.ebnf`, Layer 1) has
  exactly one: `list`. There is no quote, datum comment, vector or other
  collection syntax. `#` reads only `#t`/`#f`, and strings and `;` comments are
  scanned in loops. Tests pin that a parenthesis inside a string or comment is
  not nesting.

## Choosing 256

| Quantity | Value | Source |
|---|---|---|
| WebKit 26 overflow, base build | depth 3000 | `browser-probe-base.txt`; RR2-1 |
| Chromium 145 overflow + poisoning | depth 7000 | `browser-probe-base.txt` |
| Firefox 155 overflow | depth 7000 | `browser-probe-base.txt` |
| Deepest dialect-corpus frame | 4 | scan of `dialects/*.cbcl` |
| Largest declarable expansion `max-depth` | 64 | [[SPEC-001#REQ-024]] |
| Native stack needed at depth 256, every export (release) | 64–128 KiB | measurement below |
| Native stack needed at depth 256, every export (debug) | 256–512 KiB | measurement below |
| BEAM dirty-scheduler default stack | 40 kilowords = 320 KiB | erl `+sssdcpu` default (documentation, not measured) |

At 256, WebKit keeps 11.7× margin at the depth where it overflowed (3000 / 256).
The limit is also 64 times the deepest real frame. The measurement ran a
throwaway example (not committed) that parsed `(tell @room ((…)))` at depth 256
through `parse`, `read_str`, `run_pipeline`, `parse_message` + `Debug`,
`read_act_str`, `define_text_str`, `describe_dialect_str`,
`verify_message_shape_str`, `fold_str`, `admit_str`, `serialize` and
`parse_message_lax`, all on one thread of a given stack size:

```
debug:   512 KiB ok, 256 KiB ok, 128 KiB overflow
release: 128 KiB ok,  64 KiB overflow
```

Under mutation M4 below, with the limit raised to 4096, the native test that
runs every export overflows even the 2 MiB `cargo test` thread. Most of the
stack goes to the tree walkers downstream of the parser.

## Red gate

`native-red-gate.log`. The test file and the API (the constant and the error
variant) were written before any enforcement:

- The 1,000,000-level test aborted the whole binary: `thread '<unknown>' has
  overflowed its stack`, SIGABRT.
- With that test skipped, 5 of the 11 remaining tests failed: N+1 refusal,
  offsets, separators, every entry point, and reuse after a refusal.

## Results after the fix

| Suite | Result | Log |
|---|---|---|
| `cargo test -p cbcl-parser --test nesting_limit` | 12 passed | (run in session) |
| `cargo test -p cbcl-wasm over_deep` | 1 passed | (run in session) |
| `cargo test -p cbcl-erl --test nesting_limit` | 2 passed, on a 320 KiB thread | (run in session) |
| `cargo test --workspace` | 1428 passed, 0 failed | (run in session) |
| `crates/cbcl-erl/scripts/smoke.escript` (real BEAM, release NIF) | 42 checks, 0 failed | `beam-smoke-fixed.log` |
| same smoke script against the base NIF | node killed, exit 138 (SIGBUS), at the 1,000,000-level `parse_message/1` check | `beam-smoke-base.log` |
| `node --test js/test/*.test.ts` (wasm build of this tree) | 20 passed | `node-depth-test-fixed.log` (depth file) |
| `js/test/depth.test.ts` against the base wasm | 3 of 3 failed | `node-depth-test-base.log` |
| `js/scripts/depth-probe.mjs`: Chromium 145, Firefox 155, WebKit 26 | 63 of 63 PASS | `browser-probe-fixed.txt` |
| same probe against the base wasm | 45 FAIL | `browser-probe-base.txt` |

The browser probe gives each depth a fresh Blob-isolated instance, the Chat
loader shape. It calls `parse_message`, `read` and `parse` twice at depths
255, 256, 257, 3000, 7000, 20000 and 100000, then sends a benign frame on the
same instance. After the fix, depths 255 and 256 succeed. Every deeper call
throws a **string**, `[parse error: ]at byte 267: list nesting exceeds limit
256`, on both calls. The benign frame succeeds afterwards in all three engines.

The browser builds were Playwright's cached Chromium 145.0.7632.6 (1208),
Firefox 155.0 (1543) and WebKit 26.0 (2359), driven by playwright-core 1.58.2.
These are the same builds the RR2 re-review used, not shipping Safari or
Firefox.

```sh
npm --prefix js run build:wasm      # wasm-bindgen 0.2.114 (matches Cargo.lock)
CBCL_PROBE_FIREFOX=~/Library/Caches/ms-playwright/firefox-1543/firefox/Nightly.app/Contents/MacOS/firefox \
CBCL_PROBE_WEBKIT=~/Library/Caches/ms-playwright/webkit-2359/pw_run.sh \
CBCL_PROBE_CHROMIUM=~/Library/Caches/ms-playwright/chromium-1208/chrome-mac-arm64/'Google Chrome for Testing.app'/Contents/MacOS/'Google Chrome for Testing' \
  node js/scripts/depth-probe.mjs <playwright-core dir>            [glue dir]
crates/cbcl-erl/scripts/smoke.escript
```

The base-revision artefacts were built from `git archive d2cbd96` in a
scratch directory. The new smoke script and `depth.test.ts` were copied in,
nothing else.

## Mutations

`mutations.log`. Each mutation was applied alone to `parser.rs`, then
`cargo test -p cbcl-parser --test nesting_limit` was run.

| Mutation | Outcome |
|---|---|
| M1 remove the depth check | stack overflow, SIGABRT (killed) |
| M2 drop the decrement on exit | `sibling_lists_do_not_accumulate_depth` fails (killed) |
| M3 `==` → `>` (off by one) | 6 tests fail (killed) |
| M4 raise the limit to 4096 | stack overflow in the every-export test (killed) |
| M5 count only the top level (`depth = 1`) | stack overflow, SIGABRT (killed) |

## Limitations and open obligations

- Stack depths depend on the engine build and on how much stack the caller
  has already used. The margin was measured from a shallow call site.
- The Lean model `Parser.lean` does not carry the limit, so Rust–Lean parity
  holds only at depth 256 or less. See the `Open:` entry in SPEC-001 §3.5.1.
- `js` `npm run check` (tsc) was not run: `js/node_modules` is not installed
  in this worktree. The node tests run through `--experimental-strip-types`.
- A full `cargo mutants` sweep of `parser.rs` was not run. The five targeted
  mutations above were.
- Downstream, the Chat client must pin a build with this fix. A non-string
  throw (for example out of memory) still needs RR2-2 fault classification.
