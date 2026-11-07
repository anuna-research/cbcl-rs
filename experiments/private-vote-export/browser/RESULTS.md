# Jolt/Dory browser runtime experiment

The combined portability fix produced a real browser ZK proof that verified in
a fresh browser worker and an independent native receiver under the original
operator pins, without a history file. Browser proving took 860.6 seconds
(14.3 minutes); the managed end-to-end run took 878.5 seconds. This supports the
backend direction and a native-prover/browser-verifier path. Browser proving is
currently expensive and requires nearly the full 4 GiB WASM address space.

Measured on 2026-11-07 on Apple M2 / macOS, using
HeadlessChrome 145.0.7632.6 (Playwright headless shell), Rust 1.95.0 and
wasm-bindgen 0.2.126. This is an actual browser Web Worker experiment, using
Jolt `beebf45d829f5aecc5d330f78879cd914e47541e` and the exact guest from
[the native experiment](../RESULTS.md). The initial runs changed only the vendor
workspace manifest and dependency lock.
A subsequent upstream portability patch widens partition and lookup-capacity
products;
it preserves the mathematical partition and does not alter proof constraints.

The four-message witness contains an opening, a discussion message and two votes.
The guest authenticates four messages and two unanimous closing endorsements.
Its ELF SHA-256 is
`7cc6a3a76581e43c05cf4ad1d96e00b5319627869ee3fc36fb92bc06cb3bb870`.
It uses experimental signed envelopes and a fixed voting dialect, not native R4
v2 authentication or a general dialect export API. All keys and inputs are
synthetic. The public roster identifies signing keys, not verified human identities.

## Executed gates

The final module allows 4 GiB of WASM linear address space; the outer monitor
retains a sampled 4 GiB aggregate process RSS limit, a 1 GiB disk reserve and a
30-minute deadline. Address-space allowance is not measured physical memory.

| Gate | Observed result |
|---|---|
| Native ZK proof verified in browser | Pass; cryptographic verification 508.1 ms, preprocessing/proof decode 846.7 ms, total 1,354.8 ms |
| Receiver negative cases | Wrong expected statement, wrong setup, clear-mode proof, coherent tally/IO tamper and populated advice all rejected for the expected reason |
| Valid guest execution | 8,182,464 rows, padded to 8,388,608; execution/count 284.9 ms |
| Guest authentication/closure negatives | Bad signature and missing closure signer rejected inside the VM with host native precheck bypassed |
| Oversized valid workload | Sixteen-message fixture rejected at the selected trace bound; same-worker native-proof verification then succeeded |
| Cancel at actual trace | Worker terminated, no proof published, fresh-worker verification succeeded |
| Cancel at proving | Worker terminated, no proof published, fresh-worker verification succeeded |
| Full browser proof | Pass after both portability fixes; prove 860.6 s, trace 947.9 ms, profile decode 13.23 s, local verify 465.3 ms |
| Fresh browser verification of generated proof | Pass; crypto 505.8 ms, decode 836.1 ms |
| Independent native receiver, original pins, no history | Pass; crypto 199.2 ms, decode 337.9 ms, total 537.1 ms |

Sampled aggregate process RSS was 685,309,952 bytes for verification,
772,227,072 bytes for the count/negative suite and 2,208,071,680 bytes for proving
cancellation. These are sampled process totals, not WASM heap sizes or guarantees
of the true instantaneous peak. WASM capacity at entry to proving was
2,496,004,096 bytes. Verification capacity was 245,104,640 bytes. The successful
full proving run
peaked at 2,781,970,432 bytes sampled aggregate RSS (2.59 GiB), while its final
WASM capacity was 4,221,108,224 bytes (3.93 GiB). No monitor limit triggered.
These figures do not support a mobile-browser feasibility claim.

The earlier module with a 3 GiB virtual maximum trapped with `unreachable` after
460.9 seconds in the browser (463.2 seconds managed wall time). It produced no
proof, and its sampled aggregate RSS peaked at 2,728,771,584 bytes without
triggering the configured monitor limits. That run did not retain the trap stack
or post-failure linear capacity. Memory exhaustion was a hypothesis, not an
established cause. The unpatched 4 GiB retry failed after 477.3 seconds managed
wall time with a concrete Rust panic at
`crates/jolt-kernels/src/optimized/registers_read_write/sparse/ops.rs:24`:
`attempt to multiply with overflow`. Its sampled aggregate RSS peaked at
2,783,395,840 bytes; no monitor cap triggered. The fail-closed CDP observer
retained the panic in its console ledger and stopped the run before a result
POST completed. No proof artifacts were published.

The upstream partition expression `block * len / block_count` uses `usize`,
which is 32 bits in this WASM build. The patch widens the intermediate product
to `u128`, then divides and converts the bounded index back to `usize`. It does
not disable overflow checks or change the guest image, constraints, transcript,
setup or verification rules. A real wasm32 regression evaluates 396,796
boundaries against JavaScript BigInt arithmetic, including 395,899 whose
original intermediate product overflows. This establishes arithmetic equivalence
for those vectors, not successful proving. The partition-only proof retry passed
that location but failed at `sparse.rs:30` after 496.8 seconds managed wall time:
a lookup saturation predicate squared 65,536 using 32-bit `usize`. No cap
triggered; sampled aggregate peak was 2,537,996,288 bytes. No proof was published.
The portability patch also widens this capacity comparison before squaring,
preserving its exact threshold. An additional 65,539 real wasm32 saturation
checks match BigInt arithmetic, including the equality/transition boundaries.
The guest image and native verifier pins remain unchanged. The combined-patch
full proof subsequently succeeded and passed both fresh verification paths.

## Packaging and trust

The current uncompressed generated WASM is 18,026,141 bytes and its JS loader is
18,765 bytes. The full public prover preprocessing is 11,342,578 bytes; verifier
preprocessing is 9,769,212 bytes. The generated proof is 92,796 bytes and public
IO is 913 bytes. These sizes exclude the reusable preprocessing and program
distribution. The browser imports the full native-generated
prover profile so that its verifier preprocessing matches the independently
pinned native key exactly. The native and WASM setup-generation paths differ in
this pinned upstream revision; constructing a new browser setup is not treated
as equivalent to importing the pinned one.

The local harness serves operator pins and the profile from fixed asset routes,
separately from a submitted proof. Its complete expected fixture is a test oracle;
the production target in [SPEC-038](../../../specs/SPEC-038-optional-thread-proof-export.md)
instead separates trusted context from the unknown outcome. The browser verifier
checks ZK mode, pins, public IO and absent advice. The shareable artifacts are
proof and public IO, interpreted with independently trusted program/profile
configuration. Debug metrics and synthetic fixtures are not a production package.

The worker is single-threaded; the monitor's `RAYON_NUM_THREADS=4` environment is
for native subprocesses and does not enable WASM threads. Native four-message
proving previously took 93.3 seconds with four native Rayon workers. Browser and
native timing therefore differ in both runtime and parallelism; this is not a
controlled backend comparison.

Only loopback requests are allowed. CDP Fetch interception is supported on the
page, not this browser's worker target; strict CSP and CDP Network monitoring
also cover workers. Service workers and external requests fail the harness.
Verification does not fetch witness data. Proving fetches only known local
synthetic witness fixtures; there is no witness-upload route or server prover.
Cancellation terminates the worker without an automatic remote/native fallback.
Chrome and CDP bootstraps register their process groups with the supervisor and
wait for acknowledgement before executing. The supervisor records a default
negative artifact verdict before work, removes public artifacts on failure, and
publishes success only after a clean runner result. Real runner SIGKILL before
registration, SIGKILL after artifact publication, deadline failure, clean control
and SIGTERM cleanup tests passed. This supervision closes the observed startup
and artifact-cleanup races; RSS is still sampled every two seconds rather than
enforced by a hard kernel resource sandbox. The UI exposes public publication as
a commit point after fresh verification; Cancel is disabled during publication.

## Evidence and limits

Raw ledgers, phase logs, browser network records, package hashes and artifacts
are deliberately excluded from git under `outputs/jolt-dory-browser/`.
Final combined-patch runtime records use `headless-portability/`; the partition-only
fix uses `headless-index-fix/`. Unpatched 4 GiB and 3 GiB attempts use
`headless-run4g/` and `headless-run2/`. Separate build provenance records all four
module generations, source and patch hashes. The final native receipt is
`portability-native-receiver.log` with its managed ledger.
`partition-regression/result.json` records the initial partition arithmetic check;
`portability-regression/result.json` covers both widened expressions.
`review.json` records independent acceptance of the measured experimental gate,
with no unresolved prototype runtime findings. The Orientation-only comprehension
record is separate from production review. Elephant theory `spec-038` derives
`completed browser-feasibility` from the inspected runtime/review evidence; other
production tasks remain pending. The manager's detached-process SIGTERM smoke passed.
Vendor manifest/lock backups and the two upstream source files were restored
after all builds/runs; the committed patch reproduces the measured changes.

Earlier launch failures with installed Chrome and a cached full Chromium, and an
initial unsupported CDP worker interception command, were automation failures,
not cryptographic results. They were retained separately and do not count as
proof successes or failures.

These measurements do not establish mobile support, production memory/latency
budgets, native R4 correspondence, arbitrary dialect support, or a cryptographic
audit. Jolt/Dory ZK is the selected implementation direction; browser proving
support beyond this desktop fixture remains conditional on production
integration, further measurements and a device support policy.

Validation also passed Python/JS syntax and Rust formatting checks. The specs-only
zetl scan reports zero syntax/SPL errors and no dead links from SPEC-038; it still
exits nonzero for 38 existing dead links elsewhere in the vault.
