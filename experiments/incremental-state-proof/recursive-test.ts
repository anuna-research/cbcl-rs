import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { Field, Provable, UInt32, setNumberOfWorkers } from 'o1js';
import { Checkpoint, Head, Operation, Path } from './program.js';
import { assertCheckpoint, objectId, operation, State, stateFromNative, trace } from './helpers.js';
import { baseContext, makeBatch, stepContext, unreachablePrefix } from './recursive-helpers.js';
import { batchDigest, emptyCheckpoint, HistoryContext, HistoryProof, historyProgram, Updates } from './recursive-program.js';
setNumberOfWorkers(1);
const only = process.argv.find(x => x.startsWith('--only='))?.slice(7);
const results: { name: string; result: string }[] = [];
async function test(name: string, action: () => Promise<unknown>) {
  if (only && only !== name) return;
  await action(); results.push({ name, result: 'pass' }); console.log(JSON.stringify(results.at(-1)));
}
const oracle = trace(16), object = objectId(oracle);
async function base(context: HistoryContext) {
  await Provable.runAndCheck(async () => { await historyProgram.rawMethods.base(Provable.witness(HistoryContext, () => context)); });
}
await test('valid-genesis', () => base(baseContext(object)));
await test('forged-genesis-state', () => assert.rejects(() => base(new HistoryContext({ ...baseContext(object), before: new Checkpoint({ ...emptyCheckpoint(), state: Field(7) }) })), /Constraint unsatisfied/i));

await test('forged-genesis-history', () => assert.rejects(() => base(new HistoryContext({ ...baseContext(object), before: new Checkpoint({ ...emptyCheckpoint(), history: Field(7) }) })), /Constraint unsatisfied/i));
await test('forged-genesis-count', () => assert.rejects(() => base(new HistoryContext({ ...baseContext(object), before: new Checkpoint({ ...emptyCheckpoint(), count: UInt32.one }) })), /Constraint unsatisfied/i));
await test('wrong-genesis-method', () => assert.rejects(() => base(new HistoryContext({ ...baseContext(object), kind: Field(1) })), /Constraint unsatisfied/i));
await test('wrong-genesis-operation', () => assert.rejects(() => base(new HistoryContext({ ...baseContext(object), operation: Field(1) })), /Constraint unsatisfied/i));
// These are arithmetic-only parent stubs. Their proof bytes are intentionally
// absent; only real proving can test SelfProof verification.
function parent(input: HistoryContext, output: Checkpoint) {
  return new HistoryProof({ proof: undefined, publicInput: Provable.witness(HistoryContext, () => input), publicOutput: Provable.witness(Checkpoint, () => output), maxProofsVerified: 1 });
}
const state = new State(object), batch = makeBatch(state, oracle.messages.slice(0, 8));
async function batchCheck(context = batch.context, updates = batch.updates, parentInput = baseContext(object), parentOutput = emptyCheckpoint(), expected?: Checkpoint) {
  await Provable.runAndCheck(async () => {
    const result = await historyProgram.rawMethods.batch(Provable.witness(HistoryContext, () => context), parent(parentInput, parentOutput), Provable.witness(Updates, () => updates));
    if (expected) {
      result.publicOutput.state.assertEquals(expected.state);
      result.publicOutput.history.assertEquals(expected.history);
      result.publicOutput.count.value.assertEquals(expected.count.value);
    }
  });
}
async function rejects(action: () => Promise<unknown>) { await assert.rejects(action, /Constraint unsatisfied/i); }
await test('valid-batch-native-parity', async () => {
  const expected = stateFromNative(trace(8)).checkpoint();
  assertCheckpoint(batch.after, expected);
  await batchCheck(batch.context, batch.updates, baseContext(object), emptyCheckpoint(), expected);
});
await test('wrong-parent-object', () => rejects(() => batchCheck(batch.context, batch.updates, new HistoryContext({ ...baseContext(object), object: object.add(1) }))));
await test('wrong-parent-output', () => rejects(() => batchCheck(batch.context, batch.updates, baseContext(object), new Checkpoint({ ...emptyCheckpoint(), state: Field(77) }))));
await test('wrong-parent-count', () => rejects(() => batchCheck(batch.context, batch.updates, baseContext(object), new Checkpoint({ ...emptyCheckpoint(), count: UInt32.one }))));
await test('wrong-parent-history', () => rejects(() => batchCheck(batch.context, batch.updates, baseContext(object), new Checkpoint({ ...emptyCheckpoint(), history: Field(77) }))));
await test('wrong-batch-digest', () => rejects(() => batchCheck(new HistoryContext({ ...batch.context, operation: batch.context.operation.add(1) }))));
await test('wrong-batch-method', () => rejects(() => batchCheck(new HistoryContext({ ...batch.context, kind: Field(1) }))));
await test('wrong-operation-inside-batch', () => {
  const operations = [...batch.updates.operations];
  operations[7] = new Operation({ ...operations[7], previousLo: operations[7].previousLo.add(1) });
  return rejects(() => batchCheck(new HistoryContext({ ...batch.context, operation: batchDigest(object, operations) }), new Updates({ ...batch.updates, operations })));
});
await test('wrong-path-inside-batch', () => {
  const heads = [...batch.updates.heads];
  heads[7] = new Head({ ...heads[7], value: heads[7].value.add(1) });
  return rejects(() => batchCheck(batch.context, new Updates({ ...batch.updates, heads })));
});
await test('reordered-batch', () => {
  const reverse = <T>(x: T[]) => [...x].reverse();
  return rejects(() => batchCheck(batch.context, new Updates({ operations: reverse(batch.updates.operations), heads: reverse(batch.updates.heads), statePaths: reverse(batch.updates.statePaths), historyPaths: reverse(batch.updates.historyPaths) })));
});
await test('single-step-tail-native-parity', async () => {
  const singleState = new State(object), op = operation(oracle.messages[0]), w = singleState.witness(op);
  const expected = singleState.apply(op);
  assertCheckpoint(expected, stateFromNative(trace(1)).checkpoint());
  await Provable.runAndCheck(async () => {
    const result = await historyProgram.rawMethods.step(Provable.witness(HistoryContext, () => stepContext(w.context)), parent(baseContext(object), emptyCheckpoint()), Provable.witness(Operation, () => op), Provable.witness(Head, () => w.head), Provable.witness(Path, () => w.statePath), Provable.witness(Path, () => w.historyPath));
    result.publicOutput.state.assertEquals(expected.state);
    result.publicOutput.history.assertEquals(expected.history);
    result.publicOutput.count.value.assertEquals(expected.count.value);
  });
});
await test('forged-parent-passes-local-arithmetic-control', async () => {
  // A forged base can claim eight unproved writes. Arithmetic is consistent;
  // the real negative MUST be rejected by recursive proof verification.
  const forged = unreachablePrefix();
  await batchCheck(forged.next.context, forged.next.updates, baseContext(object), forged.checkpoint, forged.next.after);
});
if (only) { assert.equal(results.length, 1, 'named test must execute'); } else {
  const analysis = await historyProgram.analyzeMethods();
  await mkdir('evidence/recursive', { recursive: true });
  await writeFile('evidence/recursive/analysis.json', JSON.stringify(Object.fromEntries(Object.entries(analysis).map(([name, a]) => [name, { rows: a.rows, digest: a.digest }])), null, 2) + '\n');
  await writeFile('evidence/recursive/constraints.json', JSON.stringify(results, null, 2) + '\n');
}
