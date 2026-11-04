#!/usr/bin/env python3
"""Render aggregate evidence without copying private drawing payloads."""
import glob
import hashlib
import json
from pathlib import Path
import platform
import os
import subprocess

root = Path(__file__).resolve().parent
out = root / 'evidence/benchmark'
bus = Path(os.environ.get('CBCL_BUS_REPO', root.parents[2] / 'cbcl-bus')).resolve()
# Retrospective metadata completion for the first measurements, whose timed
# round-trip checks included assertions. Do not label them pure decoder timings.
for path in sorted(out.glob('drawing-*.json')):
    data = json.loads(path.read_text())
    if 'sizes' not in data:
        continue
    for row in data['sizes'].values():
        for old, new in [('gunzipMs','gunzipAndValidateMs'),('unbrotliMs','unbrotliAndValidateMs'),('parseMs','parseRoundTripAndValidateMs')]:
            if old in row:
                row[new] = row.pop(old)
    for name in ['apps/cbcl_chat/priv/web/cbcl/cbcl_wasm.js','apps/cbcl_chat/priv/web/cbcl/cbcl_wasm_bg.wasm','apps/cbcl_chat/priv/web/cbcl/object/compile.js','apps/cbcl_chat/priv/web/cbcl/object/index.js']:
        if name not in data['sources']:
            data['sources'][name] = hashlib.sha256((bus/name).read_bytes()).hexdigest()
            data.setdefault('retrospectiveProvenance', []).append(name)
    path.write_text(json.dumps(data, indent=2)+'\n')
env = {'capturedAfterMeasurements':True,'machine':subprocess.check_output(['sysctl','-n','machdep.cpu.brand_string'],text=True).strip(),'memoryBytes':int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True)),'os':platform.platform(),'cbclBusCommit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=bus,text=True).strip(),'timingConditions':'Single samples on a shared workstation. Native drawing runs overlapped each other and recursive proving; a release Rust build overlapped an earlier proof batch. No dedicated-machine performance guarantee.'}
(out/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
rows=[]
for n in [128,1024,4096]:
 for p in [4,30]:
  path=out/f'drawing-{n}-{p}.json'
  runpath=out/f'drawing-{n}-{p}-run.json'
  successful=not runpath.exists() or json.loads(runpath.read_text()).get('exit') == 0
  if path.exists() and successful:
   d=json.loads(path.read_text()); r=d['sizes']['replay'];s=d['sizes']['nativeState']
   rows.append(f"| {n:,} | {p} | {r['raw']:,} | {r['gzip9']:,} | {s['gzip9']:,} | {r['brotli5']:,} | {s['brotli5']:,} | {(1-s['brotli5']/r['brotli5'])*100:.1f}% | {d['freshNativeAdmissionAndFoldMs']/1000:.3f} s |")
  else:
   status='pending'
   if runpath.exists(): status=json.loads(runpath.read_text()).get('status','failed')
   rows.append(f'| {n:,} | {p} | {status} | | | | | | |')
proof=json.loads((out/'proof-timings.json').read_text())
prooftext='Numeric proof calibration is still running; no completion claimed.'
if proof['status']=='passed':
 c=proof['cases'][0];stages=proof['stages'];extra=sum(s['ms'] for s in stages if s['name'].startswith('control-whole-history-'))
 prooftext=f'''The unchanged numeric-register circuit produced and verified one proof covering
all **{c['writes']} writes from empty genesis**. Its binary proof is
{c['proofBinaryBytes']:,} bytes (compact JSON {c['proofJsonBytes']:,} bytes).
Cumulative actual genesis and batch proof calls took **{c['cumulativeGenesisProofCallMs']/1000:.3f} seconds
({c['cumulativeGenesisProofCallMs']/60000:.2f} minutes)**, summed across the original
128-write run and the resumed extension. The additional 128 writes took
{extra/1000:.3f} seconds of completed proof calls. This is not a fresh uninterrupted
wall time. Final in-process verification took {c['verifyMs']/1000:.3f} seconds.
Cached setup for the resumed worker was {proof['setupMs']/1000:.3f} seconds;
setup, witnesses, serialization and interrupted work are excluded from the proof-call sum.
The original cold source setup was recorded separately in
[[experiments/incremental-state-proof/RECURSION-RESULTS]].

This is calibration for sequential UInt32 registers. **It does not prove a drawing,
and drawing proof-generation time remains unmeasured.** Extrapolating these timings
would not establish drawing circuit performance or proof size.
'''
text='''---
mode: explanation
status: experimental-evidence
---
# Drawing state versus replay, and proof generation cost

The app-format experiment shows why a proof does not eliminate drawing state:
unique stroke chunks carry the geometry that must still be delivered. Ordinary
compression removes much of the repeated native-message syntax already.

## Dataset and measurements

These are deterministic synthetic traces generated through cbcl-bus's actual
shared-drawing contract and SDK, not a captured user drawing. Four signer labels,
eight operations per stroke, and periodic erasure of one in five strokes. Small
chunks have four coordinate pairs; maximum chunks have thirty. Each row also
contains one drawing opener. No signatures are counted; signer authentication is
assumed. Actual native fresh admission and fold must equal independently accumulated
expected title, chunks and erased markers. No circuit was changed.

All sizes are bytes. Replay includes canonical messages and signer labels. Full
view is the complete native fold output including erased chunks and tombstones.
Savings compare Brotli full view to Brotli replay, not raw replay to compressed state.

| Operations | Points/chunk | Replay raw | Replay gzip9 | Full view gzip9 | Replay Brotli5 | Full view Brotli5 | View saving | Native fresh replay |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
'''+ '\n'.join(rows)+'''

The view is **not a resumable checkpoint**: the existing native admission path
still requires history. Visible-only previews are measured separately in the
JSON evidence, but discard erased chunks and cannot substitute for full native
state. These views have no drawing proof. Therefore no measured proof-plus-drawing
checkpoint bundle or continuation speedup is claimed. A usable replacement needs
a specified drawing transition kernel, authenticated state and available future
witnesses, including concurrency and late delivery semantics.

Compression round trips were byte-exact. Decode/parse validation timing fields
include assertions and are labelled accordingly; they are not pure client decode
latencies. Measurements are single samples on an Apple M2 with 8 GiB RAM; native
runs and proving overlapped on a shared workstation. Source and WASM hashes are
recorded with each row. Early WASM/compiler metadata added after the run is
explicitly marked retrospective, so it is weaker than hashes captured during a
measurement. The SDK fresh admission loop serializes the growing accepted history
for each individual admission, so these replay times include that repeated work;
they are not a lower bound for an optimized native batch/incremental API.
Structured, smooth synthetic strokes may compress better
than an actual user's drawing. A real history location/export is still requested.

## Recursive proof calibration

'''+prooftext+'''
## Reproduction and next action

From this experiment directory, set `CBCL_BUS_REPO` to the sibling app repository
and run `python3 run-drawing-benchmark.py`, then `python3 summarize-benchmark.py`.
Each drawing process has a five-minute limit. Proof calibration uses
`python3 run-benchmark-proof.py --control-only` with the original recursive prefix
artifacts and native oracle configured as in the earlier experiment; add
`--resume-control` only with a consistent saved latest proof/timing ledger.
The runner overwrites its new benchmark output files, so preserve evidence before
rerunning. No app network traffic or production changes occur.

Next: the maintainer supplies an actual history location for an aggregate-only
measurement and decides whether avoiding replay CPU warrants a drawing-specific
checkpoint successor. Recursive numeric proofs are demonstrated; general drawing
proofs and production cryptographic review remain open. Scope and acceptance are
recorded in [[experiments/incremental-state-proof/BENCHMARK-BRIEF]].
'''
(root/'BENCHMARK-RESULTS.md').write_text(text)
