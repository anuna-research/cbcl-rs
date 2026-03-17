# Mutation Testing

CBCL uses [cargo-mutants](https://mutants.rs/) to verify that the test suite
detects real faults in critical-path modules. The goal is a **90% kill rate**
(mutants caught or timed-out vs. total generated).

## Targeted Modules

Only the following modules are mutated. These form the critical execution path
from parsing through constraint checking, template expansion, and evaluation:

| Crate | Module | Reason |
|---|---|---|
| `cbcl-parser` | `parser.rs` | Hand-rolled S-expression parser; correctness is foundational |
| `cbcl-parser` | `message_parser.rs` | SExpr to Message conversion; classification logic |
| `cbcl-core` | `r1.rs` | R1 no-recursion safety constraint |
| `cbcl-core` | `r3.rs` | R3 core-preservation safety constraint |
| `cbcl-core` | `template.rs` | Template expansion engine with resource bounds |
| `cbcl-core` | `msg_tag.rs` | Deterministic message tagging (DCFL) |
| `cbcl-core` | `evaluator.rs` | Message evaluator: dispatch, expansion, effects |

## How to Run

```bash
# Install cargo-mutants (one-time)
cargo install cargo-mutants

# Run mutation tests with the wrapper script
./scripts/run-mutation-tests.sh

# Dry-run: list mutants that would be generated
./scripts/run-mutation-tests.sh --list

# Or run cargo-mutants directly
cargo mutants --in-place --package cbcl-core --package cbcl-parser
```

Configuration lives in `mutants.toml` at the workspace root.

## Interpreting Results

- **Caught**: The test suite detected the mutant (a test failed). Good.
- **Timeout**: The mutant caused a test to hang. Counted as caught.
- **Missed**: No test detected the mutant. Indicates a coverage gap.
- **Unviable**: The mutant caused a compilation error. Not counted.

The wrapper script enforces a 90% kill rate threshold. If the kill rate drops
below 90%, the script exits with a non-zero status.

Detailed per-mutant results are written to `mutants.out/` in the workspace root.
Review missed mutants there to identify specific coverage gaps.

## Configuration Notes

- **Timeout multiplier**: Set to 3.0 because proptest-based tests can be slow.
- **Minimum test timeout**: 30 seconds to avoid false timeouts.
- Test files and benchmark files are excluded from mutation.

## Known Equivalent Mutants

None identified yet. If you encounter mutants that are missed but provably
equivalent (the mutation does not change observable behaviour), add them to the
`exclude_re` list in `mutants.toml` with a comment explaining why.
