# Bounded repeat execution

`(protocol (then begin (repeat 100 tick)))` expands at installation into
`tick#1` through `tick#100`. Those names are internal: `#` is outside the
wire symbol alphabet. Messages keep the declared verb `tick`.

The causal verifier resolves a message's possible expanded positions from its
same-thread `:caused-by` ancestry. A tick after `begin` inhabits the first copy;
a tick after one at position n inhabits n+1, if that copy exists. Missing
ancestry is Unknown, a missing causal reference is a Violation, and a tick after
the hundredth copy is a Violation. Neither arrival order nor derived state
participates in acceptance. Nested repeats and structural Any/All seams use
the expanded finite DAG in the same way. Copies inherit the base role
annotation; indexed-role fan-in coverage must refer to the same copy position.

The resolver evaluates the referenced causal closure against the expanded DAG
in topological order. It memoises each message/copy verdict and does not recurse
on message history. Malformed cyclic references cannot grow an unbounded call
stack. Full messages and authenticated v2/v3 causal headers can establish safety
positions; sealed causal openings leave a position Unknown. Completion-level
occupant fan-in still requires full messages, as before.

The intent binder uses these resolved types, prefers the furthest ready repeat
position, and does not deliberately emit an already occupied repeat copy. A
repeated opener verb remains available for later positions. For All fan-ins,
the binder includes each indexed sender-role occupant at that copy. This is a
local authoring policy, not distributed exclusion: concurrent peers can emit
different messages at the same position.

## Depth and message count are different

The repeat bounds each valid causal chain, not the cardinality of the accepted
set. Two peers can independently follow position 99 and both inhabit position
100. `(count tick)` counts both messages, so its result can exceed 100 across
branches. Exact duplicate delivery does not add another message.

A bounded shared *progress* view takes the maximum established protocol
position. The `(progress verb)` state rule provides this view for causally
ordered occurrences; see [protocol progress](protocol-progress.md).

## Verification boundary

`LeanCbcl/Repeat.lean` formalises typed copy names, structural expansion,
resource size, and an executable single-verb causal-position resolver. The
resolver has proofs of soundness, completeness with sufficient fuel, valid
position bounds, and stability under immutable store growth. It also checks a
concurrent-fork example. No new axioms or admitted proofs are introduced.

General multi-verb, nested, Any/All, roles, and envelope behavior have native
Rust regression coverage. A finite live comparison checks native Rust verdicts
against kernel-reduced Lean single-verb examples (including the 100/101 boundary,
missing references, and missing predecessors). This tests the transcription
boundary; it is not a universal Rust/Lean refinement proof.

```sh
cargo test -p cbcl-core -p cbcl-parser --lib --tests
cd lean-cbcl && lake build && lake exe runLinter LeanCbcl
# From the repository root, after the Lean build:
cargo test -p cbcl-parser --test repeat_execution -- --include-ignored
scripts/check-axioms.sh
```
