# Protocol progress as state

```lisp
(define count-to-one-hundred (cbcl) @author
  (extend tick (to) (tell to))
  (protocol (then begin (repeat 100 tick)))
  (state (number (progress tick))))
```

`(progress tick)` returns the greatest established protocol position of an
accepted tick, or zero when there is none. It is an integer state field.
Unlike `(count tick)`, it measures protocol progress rather than message count:

```text
                 → B's tick, position 100
… → position 99
                 → C's tick, position 100
```

Both messages remain accepted evidence. Progress is 100, even though counting
the accepted tick messages would give 101. No branch is elected and neither
message is erased. The rule does not provide mutual exclusion for conflicting
business actions. Agents may temporarily display different progress until
messages arrive; the same accepted evidence gives the same result.

## Installation and execution

R7 requires the selected verb to occur in the expanded finite protocol. Its
occurrences must be totally ordered by causal reachability; incomparable
positions are rejected rather than numbered by a map's arbitrary sort order.
The rank is 1..N in that order. Nested repeats and other intervening verbs are
allowed. Other verbs do not add to the selected verb's rank. Thus four tick
positions separated by other acts still produce progress in 0..4.

The kernel selects established `(message, position)` pairs using the existing
repeat resolver, then takes their maximum with zero as the empty identity.
Positions are derived from same-thread causal evidence, never supplied as a
numeric payload. Unresolved/invalid positions contribute nothing. R6 resolution
uses the accepted cast-bearing root. The fold deduplicates by content address
and never traverses an edge into another thread.

This rule observes protocol metadata over all accepted acts. Application-data
`domain` filters continue to apply to data rules such as `count`; they do not
hide causal progress. This distinction prevents changes in a data projection
from moving protocol progress backwards. The acceptance monitor never reads
this state field: the protocol constrains acceptance, and the state observes it.

The native JSON contract accepts `["progress", "tick"]`. JavaScript authoring
provides `c.progress('tick')`. Consumers need a WASM/NIF build from this revision;
a downstream application's older pinned runtime does not gain the new rule
merely by changing its contract text.

## Lean and test boundary

`LeanCbcl/StateProgress.lean` defines the maximum reduction, a position selector
using the proved `Repeat.resolve`, and `State.protocolProgress` over accepted
act addresses. Its theorems establish:

- Zero for the empty selection and an upper bound independent of branch count.
- Membership, permutation, and duplicate invariance.
- Monotonicity as immutable evidence and accepted-address sets grow.
- Stability once the installed bound is reached.
- Agreement of the maximum over combined selections under a fixed evidence interpretation.

The last property is not a claim that separately evaluated incomplete stores
can always merge their displayed numbers by max: merging evidence can resolve
previously missing ancestry. The message stores are merged, then state is folded.

The maximum algebra is generic. The concrete Lean causal selector models
single-verb bounded repetition; general ordered multi-verb/role protocols have
Rust regression coverage. A live comparison takes actual Rust fold outputs
and asks Lean's kernel to reduce the corresponding single-verb evidence graph,
including competing branches at position 100, duplicates, reversed order, and
missing ancestry. These are finite correspondence tests, not a universal proof
of the Rust implementation. Axiom audits reject admitted proofs.

```sh
cd lean-cbcl && lake build && lake exe runLinter LeanCbcl
# From the repository root:
cargo test -p cbcl-parser --test state_progress -- --include-ignored
scripts/check-axioms.sh
```
