# cbcl-arena

A deterministic multi-agent arena simulator for evaluating CBCL's
structural defences against the Arena public agents. Implements
SPEC-011: three challenges (Private Set Intersection, Yao's Millionaire,
Dining Cryptographers) × two agent strategies (CBCL-disciplined,
Vanilla NL-chat) × three attacker categories (Honest-cooperative,
Malicious-published, Malicious-novel). Powers the comparative table
(§4.2.1) of the LangSec '26 camera-ready.

Specification: `specs/SPEC-011-arena-simulator.md`. The simulator runs
locally with no network calls; live-LLM cells (REQ-1140) are out of
scope for v0.1.

## Quick Start

```bash
cargo run --release --example cbcl-arena -- --n 300 --out report.md
```

Runs the full 18-cell matrix at N=300 (≈10 s on Apple Silicon, well
under the 600 s NFR-1111 budget), writes Table 4 + Scope + Failure
Modes to `report.md`, and prints headline-prediction pass/fail to
stderr. Exit code is non-zero if any OBS-1110 prediction is violated.

## Programmatic API

```rust
use cbcl_arena::measurement::{measure, MeasurementConfig};
use cbcl_arena::artefact::emit_full_artefact;

let cfg = MeasurementConfig::default();          // N=300, all 18 cells
let report = measure(&cfg);

let mut out = std::io::stdout();
emit_full_artefact(&report, &mut out)?;
```

For one-game runs:

```rust
use cbcl_arena::driver::run_game;
use cbcl_arena::operator::psi::PsiOperator;
use cbcl_arena::agents::cbcl::{CbclAgent, load_dialect};
use cbcl_arena::agents::cbcl::psi::PsiCbclStrategy;

let dialect = load_dialect(include_str!("../../demo/dialects/psi.cbcl"))?;
let op = PsiOperator::default_psi();
let mut agents = vec![
    CbclAgent::new(dialect.clone(), PsiCbclStrategy::new(), "g1", "alice"),
    CbclAgent::new(dialect, PsiCbclStrategy::new(), "g1", "bob"),
];
let result = run_game(&op, &mut agents, 0xdeadbeef,
    |s| s.set.clone(),
    |g| g.clone());
```

## Architecture

The crate follows the SPEC-011 Purity Boundary Map:

| Layer  | Modules                                | Responsibility |
|--------|----------------------------------------|----------------|
| Pure   | `statistics`, `operator`, `agents`, `attackers` | Deterministic. No I/O, no clock, no env. |
| Shell  | `driver`, `measurement`, `manifest`, `artefact` | Orchestration, file I/O, build metadata. |

- `operator` — per-challenge operators (PSI, Yao, DC) implementing the
  `Operator` trait (CON-1100). Each issues per-seat private setups and
  scores chat transcripts + final guesses.
- `agents::cbcl` — disciplined agents that emit dialect-conformant
  CBCL messages and quarantine inbound bytes that fail parse,
  causal-protocol verification, or dialect membership.
- `agents::vanilla` — free-form NL-chat agents with configurable
  `ResponsePolicy { Comply, Refuse, Acknowledge }` (REQ-1121).
- `attackers` — per-challenge slates of attack patterns
  (`{Honest, Published, Novel}`, ≥4 patterns per malicious family per
  challenge). Each pattern is a small deterministic state machine.
  Novel patterns each have a rationale doc under `attackers/novel/`.
- `driver::run_game` — the per-game runner. Round-robin steps over a
  homogeneous slate of `DrivenAgent`s; bounded at `MAX_ROUNDS = 256`.
- `measurement::measure` — orchestrates the full 18-cell matrix at
  N≥1, threads a per-cell SHA-256-derived seed, aggregates Wilson 95%
  confidence intervals (`statistics::wilson_ci`), and returns a
  `ComparativeReport` plus a `ReproducibilityManifest` (REQ-1151) with
  git commit, dialect SHA-256s, per-cell seeds, and platform identifier.
- `artefact::emit_full_artefact` — writes Table 4 (REQ-1160), the scope
  statement (REQ-1170), and the known failure modes (REQ-1180) as a
  single markdown blob suitable for `\input{}` into the LaTeX source.

## Calibration

At N=300 (release build, Apple Silicon):

| Cell                                | Rate  | 95% CI         | SPEC band      |
|-------------------------------------|-------|----------------|----------------|
| Vanilla × Published × PSI           | 0.460 | (0.404, 0.517) | [0.35, 0.50] ✓ |
| CBCL × Published × PSI              | 0.000 | (0.000, 0.013) | [0.00, 0.01] ✓ |
| CBCL × Novel × PSI                  | 0.000 | (0.000, 0.013) | [0.00, 0.01] ✓ |

## Development

```bash
cargo test  -p cbcl-arena --lib                # 143 unit tests
cargo test  -p cbcl-arena --tests              # integration tests
cargo test  -p cbcl-arena --release -- --ignored   # latency + N=300 calibration
cargo check -p cbcl-arena
```

The `--ignored` suite covers TEST-1190 (per-game p95 ≤ 50 ms),
TEST-1191 (full-matrix runtime ≤ 600 s), and the OBS-1110 calibration
cells. CI runs all of them in release mode.

## License

Same as the workspace.
