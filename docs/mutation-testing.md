# Mutation Testing

CBCL uses [cargo-mutants](https://mutants.rs/) to verify that the test suite
detects real faults in critical-path modules. The goal is a **90% kill rate**
(mutants caught or timed-out divided by viable mutants; compilation failures
are excluded).

## Automatic campaign paused

The maintainer paused full mutation campaigns on pull requests and the weekly
schedule on 9 November 2026. The workflow now supports manual dispatch; the local
wrapper and its score gate remain available. Targeted CLOK semantic mutation
scripts are also retained.

[Run 333](https://git.anuna.io/anuna-research/cbcl-rs/actions/runs/333/jobs/0)
hit the three-hour job limit. Mutations that prevent the parser from advancing
each spent 385 seconds waiting for timeout. Those timeouts detect nontermination;
they are distinct from the surviving numeric-parser boundary mutation, which
still needs a discriminating test. Pausing the campaign does not establish a
passing mutation score or close that coverage gap.

The implementer owns restoring automatic runs after bounding campaign runtime,
correcting configuration loading and addressing surviving mutants.

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
| `cbcl-core` | `role.rs` | Role declarations and sealed casts |
| `cbcl-core` | `r6.rs` | Role-layer installation checks |
| `cbcl-core` | `projection.rs` | Role projection and repeat occupancy |

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

The workflow can also be started manually once this workflow definition is
available on the default branch.

## Interpreting Results

- **Caught**: The test suite detected the mutant (a test failed). Good.
- **Timeout**: The mutant caused a test to hang. Counted as caught.
- **Missed**: No test detected the mutant. Indicates a coverage gap.
- **Unviable**: The mutant caused a compilation error. Not counted.

The wrapper script enforces a 90% kill rate threshold. If the kill rate drops
below 90%, the script exits with a non-zero status.

The wrapper prints the temporary `mutants.out/` artifact directory for each run.
Review missed mutants there to identify specific coverage gaps.

## Configuration Notes

The root `mutants.toml` declares a 3.0 timeout multiplier and a 30-second minimum.
However, the wrapper does not pass that file, and cargo-mutants defaults to
`.cargo/mutants.toml`. Its declared settings are therefore not currently applied.
The root file also uses filename patterns ending in `.rs$` for `examine_re`,
which matches complete mutation descriptions rather than filenames; simply
loading it would select no mutants. Both issues must be corrected before
re-enabling automatic campaigns. The wrapper's explicit file flags still select
the critical modules listed above.

## Known Equivalent Mutants

None identified yet. If you encounter mutants that are missed but provably
equivalent (the mutation does not change observable behaviour), add them to the
`exclude_re` list in `mutants.toml` with a comment explaining why.
