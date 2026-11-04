import json,re
from pathlib import Path
root=Path(__file__).resolve().parent
out=root/'evidence'
def load(path):return json.loads((root/path).read_text())
def success(label):
 p=out/f'{label}-run.json'
 if not p.exists():return False
 r=json.loads(p.read_text());return r['exit_code']==0 and r['limit_reason'] is None
rows=[]
for case,prove_dir,prove_label,compress_dir,compress_label,verify_label in [
 ('drawing-1','proved-drawing-1-tuned','prove-drawing-1-tuned','succinct-drawing-1','compress-drawing-1','standalone-succinct-verification'),
 ('status-8','proved-status-8','prove-status-8','succinct-status-8','compress-status-8','standalone-status-verification')]:
 if not success(prove_label):rows.append(f'| {case} | pending | | | | | |');continue
 p=load(f'evidence/{prove_dir}/prove-metrics.json')
 c=load(f'evidence/{compress_dir}/compress-metrics.json') if success(compress_label) else None
 v=None
 if success(verify_label):
  v=json.loads((out/f'{verify_label}.log').read_text().splitlines()[-1])
 rows.append(f"| {case} | {p['count']} | {p['prove_including_execute_ms']/1000:.3f} s | {p['receipt_bytes']:,} | {c['compress_ms']/1000 if c else 'pending'} s | {format(c['receipt_bytes'],',') if c else 'pending'} | {str(v['verify_ms'])+' ms' if v else 'pending'} |")
metrics=load('evidence/bandwidth.json') if (out/'bandwidth.json').exists() else None
bandwidth='Bandwidth accounting remains pending.'
if metrics:
 case=metrics.get('cases',{}).get('drawing-1',metrics)
 r=case['replay'];s=case['bundles'].get('succinct')
 bandwidth=f"""For the tiny drawing fixture, measured replay transport is {r['raw']:,} bytes raw,
{r['gzip9']:,} gzip9 and {r['brotli5']:,} Brotli5. """
 if s:bandwidth+=f"""The measured succinct checkpoint transport bundle is
{s['raw']:,} bytes raw, {s['gzip9']:,} gzip9 and {s['brotli5']:,} Brotli5.
It includes the full dialect source closure, program image ID, snapshot and
base64 receipt; it is much larger than this tiny history. No bandwidth saving
has been demonstrated. """
 bandwidth+=f"""The measured host executable is {metrics['firstDownloadHostBinaryBytes']:,}
bytes and is excluded only for a warm client with a pinned verifier installed.
It includes execution/proving support, not a minimal browser verifier. Acquisition/authentication of independently expected commitments is also
excluded and unmeasured: these sizes assume the client already pins the expected
head and program, so they are not an end-to-end first-sync bandwidth measurement.
Compression
was applied symmetrically with byte-exact round trips. No proof-only-versus-history
comparison is presented as usable snapshot bandwidth.
"""
if metrics and 'cases' in metrics:
 bandwidth+='\n| Fixture | Messages | Replay Brotli5 bytes | Snapshot/receipt Brotli5 bytes |\n|---|---:|---:|---:|\n'
 for name,row in metrics['cases'].items():
  bundle=row['bundles'].get('succinct')
  bandwidth+=f"| {name} | {row['messages']} | {row['replay']['brotli5']:,} | {bundle['brotli5'] if bundle else 'pending'} |\n"
text='''---
mode: explanation
status: experimental-evidence
---
# General CBCL kernel execution proofs

## Finding

The existing native CBCL consumer computation can run inside a verifiable VM
with the dialect supplied as data. A real RISC Zero receipt for the drawing
fixture has been generated and independently verified without the history file.
This is a general kernel guest, rather than a new circuit for each dialect.
It establishes a working execution-proof architecture for this bounded profile;
it does not establish practical bandwidth savings or production readiness.

The public statement binds native-kernel semantics revision, full supplied dialect
source/ancestor registry, canonical dialect identity, thread, unique canonical
message/signer set, count and state hash. The guest installs the dialect,
recognizes message syntax, checks context, admits from empty with deterministic
pending retries, and calls the native fold. It accepts no claimed state or
precomputed verdict. The receiver pins the compiled image and compares the
journal to independently obtained expected commitments, then checks snapshot bytes.

Signer labels, including their binding to wire sender/signature metadata, remain
host assertions: no Ed25519 or transport authentication is performed. Native
consumer shape/causal admission and fold are proved; separate escrow authorization
for external effects, global completeness/freshness and safe continuation from
snapshot alone are not. The profile requires a state projection and imposes
resource/input bounds (256 records and 1 MiB for this local experiment). That
limit is a harness profile, not the former circuit candidate ceiling. It is generic across supplied dialect definitions, not a
claim that every message envelope or host-policy API is covered.

## Actual proof measurements

Apple M2, 8 GiB RAM, SDK/r0vm 3.0.6, recorded RISC Zero Rust 1.97.0, one prover
process with tuned Rayon setting 4, exponent 18 segments. Shared workstation;
small fixture/test compilation overlapped proving, so no dedicated-machine
throughput guarantee. Times are API calls including executor/IPC/setup and any
SDK verification, not isolated field-arithmetic benchmarks. Compression converts
the already verified composite receipt into a succinct receipt; its time is
additional. Final verification is a separate process reading receipt, expected
journal and snapshot, with no message history input. Verification milliseconds
cover receipt checking, expected-journal comparison and snapshot hashing after
file loading/deserialization; process startup, decoding and download are excluded.

| Fixture | Messages including opener | Prove call | Composite receipt bytes | Additional compression | Succinct receipt bytes | Standalone succinct verification |
|---|---:|---:|---:|---:|---:|---:|
'''+ '\n'.join(rows)+'''

The initial exponent 16/Rayon 1 attempt was interrupted after 1,284.056 seconds
without a proof; it is partial tuning evidence, not a successful proving time.
The tuned drawing proof call took 313.601 seconds and compression 213.212 seconds,
a total 526.813 seconds (8.78 minutes), excluding compilation and independent checks.
Its proving run observed 2,208,153,600 bytes of aggregate process-tree RSS.
Sampled two-second peaks can miss brief spikes; this is not an OS memory limit.

## Bandwidth

'''+bandwidth+'''
## Coverage and acceptance

The same compiled image executes drawing latest-per-key list payloads, a native
latest-per-signer replacement register with count, an authored role/cast checklist,
and an ancestor-dependent dialect. Execution/native journal agreement and exact
snapshot bytes are checked across the fixture matrix. An ancestor omission test
requires a protocol reference that actually needs that parent: unresolved unused
names are allowed by native registry semantics. The experiment preserves that
behavior instead of inventing a stricter kernel.

Native rejection tests cover schema/size, canonicality, duplicate addresses,
context, bad shape, missing dependencies, invalid dialect and ancestor binding.
Direct guest negatives bypass the host native precheck, first execute a valid
control, and require the expected guest rejection reason; infrastructure failures
cannot count as rejection. Serialized-receipt checks cover independent expectations,
wrong thread/dialect/history/source commitment, altered snapshot, corrupted proof
and a fake receipt even with SDK dev mode enabled. A valid receipt rejects the
wrong program image. Host mode explicitly rejects fake receipts.

Final mutation checks start from a passing baseline and target each corresponding
test. Earlier mutation records used a failing ancestor fixture and are retained
under pre-ancestor-fixture-fix as non-authoritative; they are not acceptance evidence.
Resource-runner descendant/SIGINT cleanup has a regression check. Installation
peak RSS was not sampled. SIGKILL cannot be caught by the supervisor.

Cross-model fresh reviews and dispositions are recorded in evidence/REVIEW.md.
Human cryptographic review remains open; no production API, kernel or deployment
configuration changed. Full scripts/locks, source/WASM/image hashes, staged logs,
partial attempt records and serialized receipts are retained.

## Backend alternatives and next action

The user identified SP1, Nexus and Jolt; primary-source findings are in
[[experiments/general-kernel-checkpoint/BACKENDS]]. They have not been measured
on CBCL. Jolt's UntrustedAdvice input can keep history out of the verifier call
without requiring ZK, directly matching the bandwidth goal, but requires advice
validation and rejection of panic outcomes. SP1 provides another Rust zkVM path;
its published local proving minimums exceed this workstation. Nexus's current
Stwo-based main is experimental; older Nova descriptions are legacy.

The maintainer can now compare other backends against the same computation and
input/journal contract. Measure full verifier/preprocessing download and compressed
checkpoint bytes on histories large enough to test bandwidth benefit, as well as
proving latency/memory. Existing specialized-register results do not predict this
kernel or any other VM. A successor specification must settle message authentication,
image/semantics upgrades, accepted-set anchoring and any resumable-state contract.
The experiment is governed by [[experiments/general-kernel-checkpoint/BRIEF]];
commands are in [[experiments/general-kernel-checkpoint/REPRODUCE]].
'''
(root/'RESULTS.md').write_text(text)
