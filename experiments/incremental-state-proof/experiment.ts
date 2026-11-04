import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { Bool, Cache, Field, Provable, UInt32, ZkProgram, setNumberOfWorkers, verify } from 'o1js';
import { CAPACITY, Checkpoint, Context, Head, HEIGHT, Operation, Path, program } from './program.js';
import { assertCheckpoint, fields, native, objectId, operation, State, stateFromNative, trace } from './helpers.js';
setNumberOfWorkers(1);
await mkdir('evidence', { recursive: true });
type Witness = ReturnType<State['witness']>;
const results: { name: string; result: string; ms: number; [key: string]: unknown }[] = [];
const only = process.argv.find(x => x.startsWith('--only='))?.slice(7);
async function check(w: Witness, expected?: Checkpoint) {
  await Provable.runAndCheck(async () => {
    const result = await program.rawMethods.step(
      Provable.witness(Context, () => w.context),
      Provable.witness(Operation, () => w.operation),
      Provable.witness(Head, () => w.head),
      Provable.witness(Path, () => w.statePath),
      Provable.witness(Path, () => w.historyPath));
    if (expected) {
      result.publicOutput.state.assertEquals(expected.state, 'next state');
      result.publicOutput.history.assertEquals(expected.history, 'next history');
      result.publicOutput.count.value.assertEquals(expected.count.value, 'next count');
    }
  });
}
async function test(name: string, action: () => Promise<void>) {
  if (only && only !== name) return;
  const start = performance.now();
  await action();
  const row = { name, result: 'pass', ms: Math.round(performance.now() - start) };
  results.push(row); console.log(JSON.stringify(row));
}
async function reject(w: Witness) {
  // Host/type exceptions do not count as circuit rejection.
  await assert.rejects(() => check(w), /Constraint unsatisfied/i);
}
function withOperation(w: Witness, op: Operation): Witness {
  return { ...w, operation: op, context: new Context({ ...w.context, operation: op.digest(w.context.object) }) };
}
function setup(length: number, signers = 4) {
  const start = performance.now(), oracle = trace(length + 1, signers), nativeMs = performance.now() - start;
  const state = new State(objectId(oracle));
  oracle.messages.slice(0, -1).forEach(m => state.apply(operation(m)));
  const op = operation(oracle.messages.at(-1)!);
  const witness = state.witness(op), expected = state.apply(op);
  assertCheckpoint(expected, stateFromNative(oracle).checkpoint());
  return { witness, expected, oracle, nativeMs };
}
async function constraints() {
  const parityCosts: { writes: number; nativeOracleMs: number }[] = [];
  for (const n of [1, 8, 64, 256]) {
    await test(`native-parity-${n}`, async () => {
      const sample = setup(n - 1);
      await check(sample.witness, sample.expected);
      parityCosts.push({ writes: n, nativeOracleMs: Math.round(sample.nativeMs) });
    });
  }
  const sample = setup(1, 1), w = sample.witness;
  await test('valid-replacement', () => check(w, sample.expected));
  await test('wrong-old-value', () => reject({ ...w, head: new Head({ ...w.head, value: w.head.value.add(1) }) }));
  await test('wrong-replacement', () => reject(withOperation(w, new Operation({ ...w.operation, previousLo: w.operation.previousLo.add(1) }))));
  await test('wrong-sequence', () => reject(withOperation(w, new Operation({ ...w.operation, seq: w.operation.seq.add(1) }))));
  await test('wrong-signer-index', async () => {
    const first = setup(0, 1).witness;
    await check(first); // Correctly indexed first write is the positive control.
    await reject(withOperation(first, new Operation({ ...first.operation, signer: UInt32.from(1) })));
  });
  await test('wrong-state-path', () => {
    const path = new Path(new State(w.context.object).heads.getWitness(0n));
    path.path[0] = path.path[0].add(1);
    return reject({ ...w, statePath: path });
  });
  await test('wrong-state-root', () => reject({ ...w, context: new Context({ ...w.context, before: new Checkpoint({ ...w.context.before, state: w.context.before.state.add(1) }) }) }));
  await test('wrong-history-root', () => reject({ ...w, context: new Context({ ...w.context, before: new Checkpoint({ ...w.context.before, history: w.context.before.history.add(1) }) }) }));
  await test('wrong-count', () => reject({ ...w, context: new Context({ ...w.context, before: new Checkpoint({ ...w.context.before, count: w.context.before.count.add(1) }) }) }));
  await test('wrong-object', () => reject({ ...w, context: new Context({ ...w.context, object: w.context.object.add(1) }) }));
  await test('wrong-operation', () => reject({ ...w, context: new Context({ ...w.context, operation: w.context.operation.add(1) }) }));
  await test('wrong-append-index', () => {
    const state = new State(w.context.object);
    state.apply(operation(sample.oracle.messages[0]));
    return reject({ ...w, historyPath: new Path(state.history.getWitness(2n)) });
  });
  await test('occupied-append-slot', async () => {
    const state = new State(w.context.object), first = operation(sample.oracle.messages[0]);
    state.apply(first); state.history.setLeaf(1n, Field(99));
    await reject(state.witness(w.operation));
  });
  await test('history-capacity', () => reject({ ...w, context: new Context({ ...w.context, before: new Checkpoint({ ...w.context.before, count: UInt32.from(CAPACITY) }) }) }));
  await test('noncanonical-empty-head', () => {
    const first = setup(0, 1).witness;
    return reject({ ...first, head: new Head({ ...first.head, value: UInt32.one }) });
  });
  await test('sequence-overflow', async () => {
    const state = new State(w.context.object), head = new Head({ ...w.head, seq: UInt32.MAXINT() });
    state.bySigner.set(0, head); state.heads.setLeaf(0n, head.leaf(w.context.object, UInt32.zero));
    const op = new Operation({ ...w.operation, seq: UInt32.zero });
    await reject(state.witness(op));
  });
  await test('replayed-write', async () => {
    const state = new State(w.context.object), first = operation(sample.oracle.messages[0]);
    state.apply(first); await reject(state.witness(first));
  });
  await test('unsupported-concurrency', async () => {
    const oracle = native([{ signer: 0, seq: 0, value: 10, replaces: null }, { signer: 0, seq: 1, value: 20, replaces: null }]);
    assert.equal(oracle.messages.length, 2, 'native CBCL admits this excluded concurrent case');
    const state = new State(objectId(oracle)); state.apply(operation(oracle.messages[0]));
    await reject(state.witness(operation(oracle.messages[1])));
  });
  await test('sibling-forks-require-receiver-selection', async () => {
    const first = sample.oracle.messages[0];
    const branch = native([
      { signer: first.signer, seq: first.seq, value: first.value, replaces: first.replaces },
      { signer: 0, seq: 1, value: 999, replaces: first.address },
    ]);
    const alternate = operation(branch.messages[1]);
    await check(w); await check(withOperation(w, alternate));
    // Both transitions prove from the same prior. A receiver that selected the
    // first successor must reject the sibling's prior on the next acceptance.
    assert.notDeepEqual(fields(Checkpoint, w.context.before), fields(Checkpoint, sample.expected));
    const advanced = { ...withOperation(w, alternate), context: new Context({ ...withOperation(w, alternate).context, before: sample.expected }) };
    await reject(advanced);
  });
  if (only) { assert.equal(results.length, 1, 'named test must execute'); return; }
  const analysis = await program.analyzeMethods();
  const witnesses = [1, 8, 64, 256].map(history => ({ history, privateFields: Operation.sizeInFields() + Head.sizeInFields() + 2 * Path.sizeInFields(), pathFields: 2 * Path.sizeInFields() }));
  await writeFile('evidence/constraints.json', JSON.stringify({ tests: results, parityCosts, analysis: { rows: analysis.step.rows, digest: analysis.step.digest }, height: HEIGHT, capacity: CAPACITY, witnesses }, null, 2) + '\n');
}
class StepProof extends ZkProgram.Proof(program) {}
async function verifyExpected(proof: StepProof, expected: Context, output: Checkpoint, key: string) {
  assert.deepEqual(fields(Context, proof.publicInput), fields(Context, expected), 'unexpected checkpoint context');
  assertCheckpoint(proof.publicOutput, output);
  return verify(proof, key);
}
async function realProofs() {
  const stages: unknown[] = [];
  async function stage<T>(name: string, action: () => Promise<T>) {
    console.log(JSON.stringify({ name, status: 'started' }));
    const start = performance.now(), value = await action();
    const row = { name, ms: Math.round(performance.now() - start), rss: process.memoryUsage().rss };
    stages.push(row); console.log(JSON.stringify(row)); return value;
  }
  const { verificationKey } = await stage('compile', () => program.compile({ cache: Cache.FileSystem('.cache') }));
  const proofs: unknown[] = [];
  for (const n of [8, 256]) {
    const sample = setup(n), w = sample.witness;
    const { proof } = await stage(`prove-after-${n}`, () => program.step(w.context, w.operation, w.head, w.statePath, w.historyPath));
    const json = proof.toJSON(), restored = await StepProof.fromJSON(json);
    const valid = await stage(`verify-after-${n}`, () => verifyExpected(restored, w.context, sample.expected, verificationKey.data));
    assert.equal(valid, true);
    const tampered = { ...json, publicOutput: [...json.publicOutput] };
    tampered.publicOutput[0] = Field(tampered.publicOutput[0]).add(1).toString();
    assert.equal(await verify(tampered, verificationKey.data), false, 'tampered root must fail cryptographic verification');
    await assert.rejects(() => verifyExpected(restored, new Context({ ...w.context, object: w.context.object.add(1) }), sample.expected, verificationKey.data), /unexpected checkpoint context/);
    proofs.push({ history: n, nativeMs: Math.round(sample.nativeMs), binaryBytes: Buffer.from(json.proof, 'base64').length, jsonBytes: Buffer.byteLength(JSON.stringify(json)), verified: true, tamperedOutputRejected: true, wrongContextRejected: true, proof: json });
  }
  await writeFile('evidence/real-proofs.json', JSON.stringify({ verificationKeyHash: verificationKey.hash.toString(), stages, proofs }, null, 2) + '\n');
}
if (process.argv.includes('--prove')) await realProofs(); else await constraints();
