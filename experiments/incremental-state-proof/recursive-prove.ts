import assert from 'node:assert/strict';
import { mkdir, readFile, rename, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { Cache, Field, setNumberOfWorkers, verify } from 'o1js';
import { Checkpoint } from './program.js';
import { assertCheckpoint, objectId, operation, State, stateFromNative, trace } from './helpers.js';
import { baseContext, makeBatch, stepContext } from './recursive-helpers.js';
import { BATCH, HistoryProof, historyProgram } from './recursive-program.js';
import { verifyHistory } from './recursive-receiver.js';
setNumberOfWorkers(1);
const target = Number(process.argv.find(x => x.startsWith('--target='))?.slice(9) ?? 128);
assert.ok([128, 256].includes(target), 'measured targets are 128 or 256');
const resume = process.argv.includes('--resume');
const dir = 'evidence/recursive'; await mkdir(dir, { recursive: true });
const nativeStart = performance.now(), oracle = trace(target), object = objectId(oracle);
const expectedAt = (n: number) => ({ object, checkpoint: stateFromNative(trace(n)).checkpoint() });
interface ProofRow { history: number; file: string; binaryBytes: number; jsonBytes: number; canonicalMessageBytes: number; canonicalMessageJsonBytes: number; verified: boolean; expected: { object: string; checkpoint: ReturnType<typeof Checkpoint.toJSON> } }
interface Record { status: string; target: number; object: string; batchSize: number; verificationKeyHash?: string; nativeTraceMs: number; stages: unknown[]; proofs: ProofRow[]; [key: string]: unknown }
const record: Record = resume ? JSON.parse(await readFile(dir + '/progress.json', 'utf8')) : { status: 'running', target, object: object.toString(), batchSize: BATCH, nativeTraceMs: Math.round(performance.now() - nativeStart), stages: [], proofs: [] };
record.target = target; record.status = 'running';
async function atomicWrite(path: string, text: string) {
  const temporary = path + '.tmp-' + process.pid;
  await writeFile(temporary, text); await rename(temporary, path);
}
async function persist() { await atomicWrite(dir + '/progress.json', JSON.stringify(record, null, 2) + '\n'); }
async function stage<T>(name: string, action: () => Promise<T>): Promise<T> {
  console.log(JSON.stringify({ name, status: 'started' }));
  const start = performance.now();
  try {
    const result = await action();
    const row = { name, ms: Math.round(performance.now() - start), rss: process.memoryUsage().rss, status: 'passed' };
    record.stages.push(row); console.log(JSON.stringify(row)); await persist(); return result;
  } catch (error) {
    const row = { name, ms: Math.round(performance.now() - start), status: 'rejected', error: String(error).slice(0, 2000) };
    record.stages.push(row); console.log(JSON.stringify(row)); await persist(); throw error;
  }
}
async function saveProof(proof: HistoryProof, n: number, key: string, file = `history-${n}.json`, milestone = true) {
  const json = proof.toJSON(), restored = await HistoryProof.fromJSON(json), expected = expectedAt(n);
  assert.equal(await stage(`verify-history-${n}`, () => verifyHistory(restored, expected, key)), true);
  await atomicWrite(`${dir}/${file}`, JSON.stringify(json, null, 2) + '\n');
  if (milestone) {
    const tampered = { ...json, publicOutput: [...json.publicOutput] };
    tampered.publicOutput[0] = Field(tampered.publicOutput[0]).add(1).toString();
    assert.equal(await verify(tampered, key), false, 'tampered complete-history root must fail cryptographic verification');
    await assert.rejects(() => verifyHistory(restored, { ...expected, object: object.add(1) }, key), /unexpected history object/);
    const row: ProofRow = { history: n, file, binaryBytes: Buffer.from(json.proof, 'base64').length, jsonBytes: Buffer.byteLength(JSON.stringify(json)), canonicalMessageBytes: oracle.messages.slice(0, n).reduce((bytes, message) => bytes + Buffer.byteLength(message.canonical), 0), canonicalMessageJsonBytes: Buffer.byteLength(JSON.stringify(oracle.messages.slice(0, n).map(message => message.canonical))), verified: true, expected: { object: object.toString(), checkpoint: Checkpoint.toJSON(expected.checkpoint) } };
    record.proofs = record.proofs.filter(p => p.history !== n).concat(row).sort((a, b) => a.history - b.history);
  }
  await persist();
}
try {
  const { verificationKey } = await stage('compile', () => historyProgram.compile({ cache: Cache.FileSystem('.cache-recursive') }));
  if (record.verificationKeyHash) assert.equal(record.verificationKeyHash, verificationKey.hash.toString(), 'resume key differs');
  record.verificationKeyHash = verificationKey.hash.toString();
  await atomicWrite(dir + '/verification-key.json', JSON.stringify({ hash: verificationKey.hash.toString(), data: verificationKey.data }, null, 2) + '\n');
  const state = new State(object);
  let parent: HistoryProof, baseProof: HistoryProof;
  if (resume) {
    assert.equal(record.object, object.toString());
    baseProof = await HistoryProof.fromJSON(JSON.parse(await readFile(dir + '/history-0.json', 'utf8')));
    parent = await HistoryProof.fromJSON(JSON.parse(await readFile(dir + '/latest-proof.json', 'utf8')));
    const n = Number(parent.publicOutput.count.toBigint());
    assert.ok(n % BATCH === 0 && n <= target);
    assert.equal(await verifyHistory(baseProof, expectedAt(0), verificationKey.data), true, 'resumed base must verify');
    assert.equal(await verifyHistory(parent, expectedAt(n), verificationKey.data), true, 'resumed full history must verify');
    oracle.messages.slice(0, n).forEach(message => state.apply(operation(message)));
    assertCheckpoint(state.checkpoint(), parent.publicOutput);
    if ([8, 32, 128, 256].includes(n) && !record.proofs.some(p => p.history === n)) {
      await saveProof(parent, n, verificationKey.data);
    }
    for (const row of record.proofs) {
      row.canonicalMessageJsonBytes = Buffer.byteLength(JSON.stringify(oracle.messages.slice(0, row.history).map(message => message.canonical)));
    }
  } else {
    baseProof = (await stage('base', () => historyProgram.base(baseContext(object)))).proof;
    await saveProof(baseProof, 0, verificationKey.data);
    const op = operation(oracle.messages[0]), w = state.witness(op);
    const first = (await stage('single-history-1', () => historyProgram.step(stepContext(w.context), baseProof, op, w.head, w.statePath, w.historyPath))).proof;
    await saveProof(first, 1, verificationKey.data);
    parent = baseProof;
  }
  const milestones = new Set([8, 32, 128, target]);
  while (state.count < target) {
    const start = state.count, batch = makeBatch(state, oracle.messages.slice(start, start + BATCH));
    assertCheckpoint(parent.publicOutput, batch.context.before);
    parent = (await stage(`batch-history-${state.count}`, () => historyProgram.batch(batch.context, parent, batch.updates))).proof;
    assertCheckpoint(parent.publicOutput, batch.after);
    // Commit required artifacts BEFORE advancing the durable resume checkpoint.
    if (milestones.has(state.count)) await saveProof(parent, state.count, verificationKey.data);
    await atomicWrite(dir + '/latest-proof.json', JSON.stringify(parent.toJSON(), null, 2) + '\n');
    record.latestCompleteWrites = state.count; await persist();
  }
  assert.deepEqual(record.proofs.map(p => p.history), [0, 1, 8, 32, 128, ...(target === 256 ? [256] : [])], 'all promised complete-history milestones must be durable');
  await assert.rejects(() => verifyHistory(baseProof, expectedAt(target), verificationKey.data), /unexpected final checkpoint/);
  record.oldValidHeadRejected = true;
  // Forge a real base's public output to a locally consistent eight-write state.
  // Its proof bytes never established those writes. Only recursive verification
  // can reject its otherwise valid extension with the next eight operations.
  const negativeState = new State(object);
  oracle.messages.slice(0, BATCH).forEach(message => negativeState.apply(operation(message)));
  const forgedJson = baseProof.toJSON();
  forgedJson.publicOutput = Checkpoint.toFields(negativeState.checkpoint()).map(x => x.toString());
  const forgedParent = await HistoryProof.fromJSON(forgedJson);
  assert.equal(await verify(forgedParent, verificationKey.data), false, 'adversarial parent must be cryptographically invalid');
  const next = makeBatch(negativeState, oracle.messages.slice(BATCH, 2 * BATCH));
  let status = 'inconclusive';
  try {
    const attempted = (await stage('extend-cryptographically-invalid-parent', () => historyProgram.batch(next.context, forgedParent, next.updates))).proof;
    status = await verify(attempted, verificationKey.data) ? 'failed-laundered-parent' : 'rejected-by-verifier';
  } catch (error) {
    const text = String(error); record.recursionNegativeError = text.slice(0, 4000);
    if (/constraint.*unsatisfied|verification.*fail|proof.*verif.*fail|previous.*proof.*invalid/i.test(text)) status = 'rejected-during-proving';
  }
  record.recursionNegativeStatus = status;
  assert.ok(status === 'rejected-during-proving' || status === 'rejected-by-verifier', 'forged-parent rejection must be classified, not a generic backend failure');
  record.status = 'passed';
} catch (error) {
  record.status = 'failed'; record.error = String(error).slice(0, 4000); throw error;
} finally { await persist(); }
