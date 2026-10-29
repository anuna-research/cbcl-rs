import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { Bool, Cache, Field, Provable, SelfProof, Signature, UInt32, UInt64, ZkProgram, setNumberOfWorkers, verify } from 'o1js';
import { Context, makeProgram, Record as Operation, Snapshot, Summary } from './program.js';
import { appendContext, baseContext, Data, mergeContext, native, objectId, operation, publicKeys, snapshot, testKeys } from './helpers.js';

setNumberOfWorkers(1);
const object = objectId(), program = makeProgram(publicKeys);
class StateProof extends ZkProgram.Proof(program) {}
const a: Data = { nonce: 1, amount: 5, author: false };
const b: Data = { nonce: 1, amount: 7, author: true };
const c: Data = { nonce: 2, amount: 3, author: false };
const rogue: Data = { nonce: 99, amount: 100, author: false };
const evidence: { mode: string; stages: unknown[]; constraints: string[]; native: unknown[]; [key: string]: unknown } = {
  mode: process.argv.includes('--prove') ? 'real-proofs' : 'constraints-only', stages: [], constraints: [], native: [],
};
function signature(data: Data, context = object) {
  return Signature.create(testKeys[Number(data.author)], operation(data).fields(context));
}
function checkNative(records: Data[]) {
  const state = snapshot(object, records).summarize(object), oracle = native(records);
  assert.equal(state.count.toBigint(), BigInt(oracle.state.count));
  assert.equal(state.total.toBigInt(), BigInt(oracle.state.total));
  evidence.native.push({ records, count: oracle.state.count, total: oracle.state.total });
}
function parent(records: Data[], context = object) {
  // Used only by constraint tests: this is NOT a cryptographic proof. rawMethods
  // let arithmetic run under runAndCheck; predecessor proof validity is tested
  // separately in the --prove run using an adversarial serialized real proof.
  return new StateProof({ proof: undefined, publicInput: baseContext(context), publicOutput: snapshot(context, records).summarize(context), maxProofsVerified: 2 });
}
async function appendConstraint(old: Data[], added: Data, next: Data[], options: { before?: Data[]; context?: Context; sig?: Signature } = {}) {
  await Provable.runAndCheck(async () => {
    await program.rawMethods.append(options.context ?? appendContext(object, snapshot(object, old).summarize(object).root, added), parent(old),
      Provable.witness(Snapshot, () => snapshot(object, options.before ?? old)),
      Provable.witness(Operation, () => operation(added)),
      Provable.witness(Signature, () => options.sig ?? signature(added)),
      Provable.witness(Snapshot, () => snapshot(object, next)));
  });
}
async function mergeConstraint(left: Data[], right: Data[], union: Data[]) {
  await Provable.runAndCheck(async () => {
    await program.rawMethods.merge(mergeContext(object, snapshot(object, left).summarize(object).root, snapshot(object, right).summarize(object).root), parent(left), parent(right),
      Provable.witness(Snapshot, () => snapshot(object, left)),
      Provable.witness(Snapshot, () => snapshot(object, right)),
      Provable.witness(Snapshot, () => snapshot(object, union)));
  });
}
async function rejection(name: string, work: () => Promise<unknown>) {
  await assert.rejects(work, name); evidence.constraints.push(name);
}
async function constraints() {
  await appendConstraint([], a, [a]);
  await appendConstraint([a], a, [a]);
  await mergeConstraint([a, b], [a, c], [a, b, c]);
  await mergeConstraint([a, b, c], [a, b, c], [a, b, c]);
  evidence.constraints.push('valid append, duplicate append, fork union, self merge');
  await rejection('invalid signature', () => appendConstraint([], a, [a], { sig: Signature.create(testKeys[1], operation(a).fields(object)) }));
  await rejection('signature bound to object', () => appendConstraint([], a, [a], { sig: signature(a, object.add(1)) }));
  await rejection('predecessor belongs to another object', () => appendConstraint([a], b, [a, b], { context: appendContext(object.add(1), snapshot(object, [a]).summarize(object).root, b) }));
  await rejection('snapshot differs from predecessor commitment', () => appendConstraint([a], b, [b], { before: [] }));
  await rejection('append omitted previous record', () => appendConstraint([a], b, [b]));
  await rejection('append omitted new record', () => appendConstraint([a], b, [a]));
  await rejection('append injected unrelated record', () => appendConstraint([a], b, [a, b, rogue]));
  await rejection('merge omitted right contribution', () => mergeConstraint([a, b], [a, c], [a, b]));
  await rejection('merge omitted shared ancestor', () => mergeConstraint([a, b], [a, c], [b, c]));
  await rejection('merge injected unrelated record', () => mergeConstraint([a, b], [a, c], [a, b, c, rogue]));
  const claimed = appendContext(object, snapshot(object, [a]).summarize(object).root, b);
  await rejection('append public parent root binding', () => appendConstraint([a], b, [a, b], { context: new Context({ ...claimed, left: claimed.left.add(1) }) }));
  await rejection('append public operation binding', () => appendConstraint([a], b, [a, b], { context: new Context({ ...claimed, operation: claimed.operation.add(1) }) }));
  await rejection('append public method kind binding', () => appendConstraint([a], b, [a, b], { context: new Context({ ...claimed, kind: Field(2) }) }));
  await rejection('zero contribution', () => appendConstraint([], { ...a, amount: 0 }, [{ ...a, amount: 0 }]));
  await rejection('duplicate noncanonical set entries', async () => {
    const invalid = snapshot(object, [a]); invalid.present[1] = Bool(true); invalid.records[1] = operation(a);
    await Provable.runAndCheck(() => { Provable.witness(Snapshot, () => invalid).summarize(object); });
  });
  await rejection('noncanonical absent record', async () => {
    const invalid = snapshot(object, []); invalid.records[0] = operation(a);
    await Provable.runAndCheck(() => { Provable.witness(Snapshot, () => invalid).summarize(object); });
  });
  assert.throws(() => snapshot(object, [a, b, c, rogue, { ...rogue, nonce: 100 }]));
  evidence.constraints.push('capacity overflow rejected before proving');
  for (const data of [[], [a], [a, b], [a, c], [a, b, c], [a, b, c, a]]) checkNative(data);
}
async function stage<T>(name: string, action: () => Promise<T>): Promise<T> {
  console.log(JSON.stringify({ stage: name, status: 'started' }));
  const start = performance.now(); const value = await action();
  const row = { stage: name, ms: Math.round(performance.now() - start), rss: process.memoryUsage().rss };
  evidence.stages.push(row); console.log(JSON.stringify(row)); return value;
}
async function verifyFor(proof: StateProof, expected: Context, key: string) {
  assert.deepEqual(Context.toFields(proof.publicInput).map(x => x.toString()), Context.toFields(expected).map(x => x.toString()), 'proof covers unexpected object, parents or operation');
  return verify(proof, key);
}
async function realProofs() {
  const { verificationKey } = await stage('compile', () => program.compile({ cache: Cache.FileSystem('.cache') }));
  const root = (records: Data[]) => snapshot(object, records).summarize(object).root;
  const contexts = [baseContext(object), appendContext(object, root([]), a),
    appendContext(object, root([a]), b), appendContext(object, root([a]), c),
    mergeContext(object, root([a, b]), root([a, c])),
    mergeContext(object, root([a, b, c]), root([a, b, c])),
    appendContext(object, root([a, b, c]), a)];
  const genesis = (await stage('base', () => program.base(contexts[0]))).proof;
  const seed = (await stage('shared-ancestor', () => program.append(contexts[1], genesis, snapshot(object, []), operation(a), signature(a), snapshot(object, [a])))).proof;
  const left = (await stage('left-fork', () => program.append(contexts[2], seed, snapshot(object, [a]), operation(b), signature(b), snapshot(object, [a, b])))).proof;
  const right = (await stage('right-fork', () => program.append(contexts[3], seed, snapshot(object, [a]), operation(c), signature(c), snapshot(object, [a, c])))).proof;
  const merged = (await stage('merge-shared-ancestor', () => program.merge(contexts[4], left, right, snapshot(object, [a, b]), snapshot(object, [a, c]), snapshot(object, [a, b, c])))).proof;
  const self = (await stage('idempotent-self-merge', () => program.merge(contexts[5], merged, merged, snapshot(object, [a, b, c]), snapshot(object, [a, b, c]), snapshot(object, [a, b, c])))).proof;
  const duplicate = (await stage('idempotent-duplicate-append', () => program.append(contexts[6], merged, snapshot(object, [a, b, c]), operation(a), signature(a), snapshot(object, [a, b, c])))).proof;
  assert.equal(merged.publicOutput.total.toBigInt(), 15n);
  assert.equal(merged.publicOutput.count.toBigint(), 3n);
  for (const proof of [self, duplicate]) assert.equal(proof.publicOutput.root.toString(), merged.publicOutput.root.toString());
  const sizes = [];
  for (const [i, proof] of [genesis, seed, left, right, merged, self, duplicate].entries()) {
    const serialized = JSON.stringify(proof.toJSON());
    const received = await StateProof.fromJSON(JSON.parse(serialized));
    const valid = await stage(`receiver-verifies-serialized-proof-${i}`, () => verifyFor(received, contexts[i], verificationKey.data));
    assert.equal(valid, true);
    sizes.push({ index: i, proofBytes: Buffer.from(proof.toJSON().proof, 'base64').length, jsonBytes: Buffer.byteLength(serialized) });
  }
  // Receiver gets the final proof, expected heads and trusted verification key;
  // it needs neither predecessor proofs nor the canonical operation snapshots.
  const serialized = JSON.stringify(merged.toJSON());
  const modified = JSON.parse(serialized); modified.publicOutput[2] = '999';
  assert.equal(await verify(modified, verificationKey.data), false);
  evidence.constraints.push('serialized final total tampering rejected by real verifier');
  await assert.rejects(() => verifyFor(self, contexts[4], verificationKey.data));
  await assert.rejects(() => verifyFor(left, contexts[4], verificationKey.data));
  evidence.constraints.push('valid unrelated merge/old branch rejected for expected member heads');
  // A forged parent has an internally consistent snapshot of an unsigned record.
  // All local append checks can succeed. Recursive verification must prevent
  // laundering it. Generic backend failures are explicitly inconclusive.
  const forgedJson = seed.toJSON();
  forgedJson.publicOutput = Summary.toFields(snapshot(object, [rogue]).summarize(object)).map(x => x.toString());
  const forgedParent = await StateProof.fromJSON(forgedJson);
  assert.equal(await verify(forgedParent, verificationKey.data), false);
  let negativeStatus = 'inconclusive';
  try {
    const attempted = (await stage('reject-forged-predecessor', () => program.append(appendContext(object, root([rogue]), b), forgedParent, snapshot(object, [rogue]), operation(b), signature(b), snapshot(object, [rogue, b])))).proof;
    negativeStatus = await verify(attempted, verificationKey.data) ? 'failed' : 'rejected-by-verifier';
  } catch (error) {
    const message = String(error);
    evidence.recursionNegativeError = message.slice(0, 2000);
    if (/constraint.*unsatisfied|verification.*fail|proof.*verif.*fail|previous.*proof.*invalid/i.test(message)) negativeStatus = 'rejected-during-proving';
  }
  evidence.recursionNegativeStatus = negativeStatus;
  assert.notEqual(negativeStatus, 'failed', 'a forged predecessor was laundered');
  assert.notEqual(negativeStatus, 'inconclusive', 'unclassified backend failure is not rejection evidence');
  evidence.final = { count: 3, total: 15, proofSizes: sizes, oneVerificationKey: verificationKey.hash.toString(), expectedStatement: Context.toJSON(contexts[4]), object: object.toString() };
}
await mkdir('evidence', { recursive: true });
try {
  await constraints();
  if (process.argv.includes('--prove')) await realProofs();
  evidence.status = 'passed';
} catch (error) {
  evidence.status = 'failed'; evidence.error = String(error); process.exitCode = 1;
  console.error(error);
} finally {
  evidence.date = new Date().toISOString(); evidence.node = process.version;
  evidence.peakRssBytes = process.resourceUsage().maxRSS * 1024;
  await writeFile(`evidence/${evidence.mode}.json`, `${JSON.stringify(evidence, null, 2)}\n`);
  console.log(JSON.stringify({ status: evidence.status, mode: evidence.mode }));
}
