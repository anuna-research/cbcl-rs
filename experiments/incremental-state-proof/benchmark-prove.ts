import assert from 'node:assert/strict';
import { mkdir, readFile, rename, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { Cache, setNumberOfWorkers } from 'o1js';
import { Checkpoint } from './program.js';
import { assertCheckpoint, objectId, operation, State, stateFromNative, trace } from './helpers.js';
import { baseContext, makeBatch } from './recursive-helpers.js';
import { BATCH, HistoryProof, historyProgram } from './recursive-program.js';
import { verifyHistory } from './recursive-receiver.js';
import { Profile, workload } from './benchmark-data.js';
setNumberOfWorkers(1);
const dir = 'evidence/benchmark'; await mkdir(dir, { recursive: true });
const onlyControl = process.argv.includes('--control-only');
assert.ok(onlyControl, 'pass --control-only: only the numeric calibration is retained after drawing workload steering');
const resumeControl = process.argv.includes('--resume-control');
const record: { status: string; setupMs?: number; genesisMs?: number; verificationKeyHash?: string; stages: unknown[]; cases: unknown[]; [key: string]: unknown } = resumeControl ? JSON.parse(await readFile(dir + '/proof-timings.json', 'utf8')) : { status: 'running', stages: [], cases: [] };
record.status = 'running';
if (onlyControl) record.workloadSteering = 'User identified cbcl-bus drawing workload; numeric proofs retained as calibration only';
async function atomic(path: string, value: unknown) { const temp = path + '.tmp-' + process.pid; await writeFile(temp, JSON.stringify(value, null, 2) + '\n'); await rename(temp, path); }
async function save() { await atomic(dir + '/proof-timings.json', record); }
async function timed<T>(name: string, action: () => Promise<T>) {
  console.log(JSON.stringify({ name, status: 'started' })); const start = performance.now();
  const value = await action(), ms = Math.round(performance.now() - start);
  record.stages.push({ name, ms, rss: process.memoryUsage().rss }); console.log(JSON.stringify({ name, ms, status: 'passed' })); await save(); return { value, ms };
}
try {
  const compiled = await timed('shared-cached-source-setup', () => historyProgram.compile({ cache: Cache.FileSystem('.cache-recursive') }));
  const key = compiled.value.verificationKey; record.setupMs = compiled.ms; record.verificationKeyHash = key.hash.toString();
  const oldKey = JSON.parse(await readFile('evidence/recursive/verification-key.json', 'utf8'));
  assert.equal(oldKey.hash, key.hash.toString()); assert.equal(oldKey.data, key.data, 'benchmark must use unchanged circuit');
  await atomic(dir + '/verification-key.json', { hash: key.hash.toString(), data: key.data });
  const object = objectId(trace(0));
  const fresh = resumeControl ? { value: { proof: await HistoryProof.fromJSON(JSON.parse(await readFile('evidence/recursive/history-0.json', 'utf8'))) }, ms: 0 } : await timed('shared-fresh-genesis', () => historyProgram.base(baseContext(object)));
  const genesis = fresh.value.proof; if (!resumeControl) record.genesisMs = fresh.ms;
  assert.equal(await verifyHistory(genesis, { object, checkpoint: new State(object).checkpoint() }, key.data), true);
  const cases: [Profile, number, boolean][] = [['control',256,true]];
  for (const [profile, target, resume] of cases) {
    const caseStart = performance.now(), nativeStart = performance.now(), data = workload(profile, target), nativeMs = Math.round(performance.now() - nativeStart);
    assert.equal(objectId(data.oracle).toString(), object.toString());
    const state = new State(object); let parent: HistoryProof = genesis, prefixMs = 0, prefixWrites = 0;
    if (resume) {
      parent = await HistoryProof.fromJSON(JSON.parse(await readFile('evidence/recursive/history-128.json', 'utf8')));
      if (resumeControl) parent = await HistoryProof.fromJSON(JSON.parse(await readFile(dir + '/control-latest-proof.json', 'utf8')));
      const prefixCount = Number(parent.publicOutput.count.toBigint());
      assert.ok(prefixCount >= 128 && prefixCount <= target && prefixCount % BATCH === 0);
      data.oracle.messages.slice(0, prefixCount).forEach(message => state.apply(operation(message)));
      assertCheckpoint(state.checkpoint(), parent.publicOutput);
      assert.equal(await verifyHistory(parent, { object, checkpoint: state.checkpoint() }, key.data), true, 'prefix is recursively valid, never newly trusted');
      const old = JSON.parse(await readFile('evidence/recursive/initial-progress.json', 'utf8'));
      const prefixCalls = old.stages.filter((s: { name: string; status: string }) => s.status === 'passed' && (s.name === 'base' || s.name.startsWith('batch-history-')));
      assert.equal(prefixCalls.length, 17, 'one base plus sixteen real prefix batch calls');
      prefixMs = prefixCalls.reduce((sum: number, s: { ms: number }) => sum + s.ms, 0); prefixWrites = prefixCount;
      const resumedCalls = (record.stages as {name:string;ms:number}[]).filter(s => /^control-whole-history-\d+$/.test(s.name) && Number(s.name.split('-').at(-1)) <= prefixCount);
      assert.equal(resumedCalls.length, (prefixCount-128)/BATCH);
      prefixMs += resumedCalls.reduce((sum,s) => sum+s.ms,0);
    }
    let witnessMs = 0, newProofMs = 0; const batches: { from: number; to: number; witnessMs: number; proofMs: number }[] = [];
    while (state.count < target) {
      const from = state.count, witnessStart = performance.now(), batch = makeBatch(state, data.oracle.messages.slice(from, from + BATCH));
      const preparation = Math.round(performance.now() - witnessStart); witnessMs += preparation;
      assertCheckpoint(parent.publicOutput, batch.context.before);
      const result = await timed(`${profile}-whole-history-${state.count}`, () => historyProgram.batch(batch.context, parent, batch.updates));
      parent = result.value.proof; assertCheckpoint(parent.publicOutput, batch.after);
      newProofMs += result.ms; batches.push({ from, to: state.count, witnessMs: preparation, proofMs: result.ms });
      await atomic(`${dir}/${profile}-latest-proof.json`, parent.toJSON());
      record[profile + 'LatestCompleteWrites'] = state.count; await save();
    }
    const expectedStart = performance.now(), expected = stateFromNative(data.oracle).checkpoint(), expectedMs = Math.round(performance.now() - expectedStart);
    assertCheckpoint(expected, parent.publicOutput);
    const serialized = parent.toJSON(), restored = await HistoryProof.fromJSON(serialized);
    const verified = await timed(`${profile}-verify-final`, () => verifyHistory(restored, { object, checkpoint: expected }, key.data));
    assert.equal(verified.value, true);
    await atomic(`${dir}/${profile}-history-${target}.json`, serialized);
    await atomic(`${dir}/${profile}-expected-head.json`, { object: object.toString(), checkpoint: Checkpoint.toJSON(expected) });
    const currentGenesisMs = resume ? 0 : fresh.ms;
    record.cases.push({ profile, writes: target, prefixWrites, writers: data.writers, nativeFixtureMs: nativeMs, witnessMs, newProofCallMs: newProofMs, prefixProofCallMs: prefixMs, genesisMsCharged: currentGenesisMs, cumulativeGenesisProofCallMs: prefixMs + currentGenesisMs + newProofMs, cumulativeTimingNote: resume ? 'sum of actually measured prior base/prefix calls and current extension calls across separate runs; not a fresh uninterrupted wall time' : 'fresh complete history from a separately measured shared genesis; shared source setup is excluded', expectedRootReconstructionMs: expectedMs, verifyMs: verified.ms, caseWallMs: Math.round(performance.now() - caseStart), proofBinaryBytes: Buffer.from(serialized.proof, 'base64').length, proofJsonBytes: Buffer.byteLength(JSON.stringify(serialized)), batches, verified: true });
    await save();
  }
  assert.deepEqual(record.cases.map((x: any) => [x.profile, x.writes]), cases.map(([profile,target]) => [profile,target]));
  record.status = 'passed';
} catch (error) { record.status = 'failed'; record.error = String(error); throw error; }
finally { await save(); }
