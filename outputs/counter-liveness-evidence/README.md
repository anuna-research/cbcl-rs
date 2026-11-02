# Counter availability evidence

Report: [[counter-availability-investigation]]. Independent review: [[counter-availability-review]]. Runtime baseline: commit `3bacf55`, `state-rules-spec`, at `/private/tmp/cbcl-bounded-counter`.

## Executable model evidence

- `ResidualBalanceAudit.lean`: authorized unit spend on unit balance cannot be signed/finalized under current fractional guards, including a valid version-advance witness. Arbitrary finite static DAG parameter, one fixed transaction, no credits/cancellation. Includes a target-action-fair infinite execution. This is not a larger-balance spend-down trace or universal protocol impossibility result.
- `CancellationRaceAudit.lean`: actual accepted ideal-authorized execution forms an operation certificate then splits one honest effects vote versus two honest fences, with the Byzantine witness silent. Neither outcome forms. Target signing/effects/new-fence fairness holds. No future version/actor-packet refinement is claimed.

Replay from the repository root:

```sh
python3 outputs/counter-liveness-evidence/verify.py
```

Or from `lean-cbcl/`:

```sh
lake env lean ../outputs/counter-liveness-evidence/ResidualBalanceAudit.lean
lake env lean ../outputs/counter-liveness-evidence/CancellationRaceAudit.lean
```

`verification.json` records successful kernel checks and rejection of deliberate negative controls. Changed-cost and removed-split mutants must fail by proof errors, not missing imports. Printed axiom dependencies contain only standard Lean axioms. The verification program checks baseline source hashes; a changed baseline requires a new audit rather than silently relabeling old results. Log files remain local.

These are research audits of current models, not a replacement implementation or a new proof of complete fund availability. No new primitive, unsafe refund or consensus fallback has been added to Rust.

## Primary literature and search limits

ar-crawl session `a53a8d66-005b-40fc-99b2-f2de308f7e93` captured version-pinned Stingray, FastPay, AT2, Astro and CryptoConcurrency full text. The PMC browser capture is blocked/unusable; the consensus-number text was inspected with the web reader as explicitly described in the report. `crawl-manifest.json` records capture hashes and usability. `sources.json` records URLs, `search-scope.json` records purposive queries and abstract-only leads. A successful navigation does not imply a usable paper capture.

Raw L01–L06 JSON, session recording, transcript and paper text remain local and ignored. Curated manifests, audit sources and report are intended for version control. This is not an exhaustive literature survey or a formally verified interpretation of the external papers.

## Elephant

Local theory `cbcl-counter-availability`, ID `e0227fa8ede5981f00a61947dda257f515832c9e3db7eba19af5a6acd504ba69`. No peers or daemon configuration were changed. Signed findings distinguish paper interpretation, kernel-checked current-model results, required no-consensus availability, and the unproved replacement lifecycle.

```sh
elephant explain '(finding current-availability-contract-insufficient)' -t cbcl-counter-availability --json
elephant status -t cbcl-counter-availability --json
```

Raw signed journal/operation exports are local. Signing a research assertion establishes its authorship, not its truth; the Lean files and recorded kernel runs establish the stated model theorems.
