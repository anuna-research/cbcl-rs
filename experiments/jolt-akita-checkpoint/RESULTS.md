# Jolt/Akita checkpoint results

Real Akita proofs of the same bounded native CBCL consumer succeeded on an
8 GB Apple M2, four Rayon threads, Jolt
`beebf45d829f5aecc5d330f78879cd914e47541e`, Rust 1.95.0, upstream build-fast
CPU profile. No Metal, mock proof or upstream cryptographic modifications.

| Fixture | Messages | Trace rows | Trace | Setup | Prove | Proof bytes | Producer verify |
|---|---:|---:|---:|---:|---:|---:|---:|
| Drawing, one payload chunk | 2 | 1,609,395 | 0.196 s | 0.305 s | 9.417 s | 106,630 | 24 ms |
| Status register | 9 | 3,222,118 | 0.278 s | 0.997 s | 22.202 s | 109,904 | 28 ms |
| Drawing, eight payload chunks | 9 | 3,917,940 | 0.312 s | 1.009 s | 26.183 s | 109,917 | 29 ms |

Single observations, not repeated statistical benchmarks. Build time excluded.
Trace+setup+proof is 9.918 s, 23.477 s and 27.504 s respectively. Whole managed
invocations took 16.225 s, 24.281 s and 28.349 s, including cached guest build,
serialization and other host work. Sampled process-tree peaks were 1.25 GB,
1.41 GB and 1.39 GB; sampling interval two seconds, not exact maxima.

For the identical two-message drawing baseline, RISC Zero execution+proof was
313.601 s and succinct compression added 213.212 s. Akita trace+proof is
9.613 s: about 32.6x faster than execution+proof, or 54.8x versus the pipeline
including succinct compression. Including Akita setup gives 9.918 s. These are
local end-to-end phase comparisons, not a universal backend throughput claim.
The nine-message status baseline was 660.998 s plus 476.364 s compression.

## Bandwidth and receiver

| Fixture | Proof + public IO + state | Full setup | Cold total |
|---|---:|---:|---:|
| Drawing 2 | 107,512 B | 13,051,098 B | 13,158,610 B |
| Status 9 | 110,773 B | 13,057,041 B | 13,167,814 B |
| Drawing 9 | 111,093 B | 13,057,041 B | 13,168,134 B |

Warm figures assume the exact authenticated verifier preprocessing is installed.
The two nine-message setups are byte-identical (SHA in summary.json); the
smaller drawing setup differs. Reuse across arbitrary lengths is not established.
Verifier software and acquiring authenticated expected commitments are excluded
from both byte totals. These tiny histories remain cheaper to replay; no
bandwidth break-even for thousands of messages was measured.

Fresh-process receiver verification reads no history. Its verification timing is
recorded in each receiver-negative JSON; it includes lazy verification work and
is slower than warm producer verification (approximately 0.11 s for drawing2
and 1.07 s for status9 in the final runs). It excludes loading/deserializing the
setup before the timer. Do not present warm 24–29 ms as cold receiver latency.
The setup SHA must come from a trusted operator build; ELF SHA is provenance.

All 12 native adapter tests pass. Each of three serialized receiver suites accepts
the honest proof and rejects wrong thread, dialect, message-set hash, source hash,
count, state, corrupt proof/setup/public IO, and wrong setup pin. A coherent
public-output tamper changes the thread in BOTH public IO and expected journal;
it reaches upstream verification and fails ProofOfWorkRejected at Stage1Tau.
This checks proof/output binding beyond a local expected-output comparison.

## Scope and remaining work

Same guest ELF across both dialects; no circuit for individual dialects. The
proof certifies strict parsing, installed dialect execution, native shape/causal
admission and folding over the supplied set. It does not authenticate Ed25519
signatures, signer labels, transport identity, global completeness/freshness,
external-effect authorization or continuation from a previous state. Akita's
current backend is non-zero-knowledge; advice is omitted from public IO but that
is not a privacy guarantee.

This trial caps input at 1 MiB, records at 256 and padded trace at 2^22. Drawing9
nearly reaches the trace cap. Thousands-message drawings, larger-machine scaling,
committed-program preprocessing to reduce cold setup, and recursive/incremental
composition remain unmeasured. Published CPU/Metal throughput must not be used
to extrapolate CBCL performance. Fresh-context adversarial review completed; required cross-model diversity is
unestablished. Human cryptographic review and production protocol design remain
open.

The initial integration failures are retained: missing guest trusted-advice
capacity caused an MMU layout mismatch; explicit zero fixed it. Packaged dense
catalogs require W8R2 producer profile, while one-hot trace geometry stays W1R0.
No bounds or schedule audits were weakened. Initial nextest CLI profile syntax
was corrected; that first exit was not a test failure. Build logs and resource
ledgers preserve one-time costs separately from proof times.
