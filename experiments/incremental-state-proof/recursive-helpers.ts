import assert from 'node:assert/strict';
import { Field } from 'o1js';
import { Context } from './program.js';
import { Message, native, objectId, operation, State } from './helpers.js';
import { BATCH, batchDigest, emptyCheckpoint, HistoryContext, Updates } from './recursive-program.js';
export function baseContext(object: Field) { return new HistoryContext({ kind: Field(0), object, before: emptyCheckpoint(), operation: Field(0) }); }
export function stepContext(context: Context) { return new HistoryContext({ kind: Field(1), ...context }); }
export function makeBatch(state: State, messages: Message[]) {
  assert.equal(messages.length, BATCH, 'exact batch size');
  const before = state.checkpoint();
  const witnesses = messages.map(message => {
    const op = operation(message), witness = state.witness(op);
    state.apply(op); return witness;
  });
  const updates = new Updates({ operations: witnesses.map(w => w.operation), heads: witnesses.map(w => w.head), statePaths: witnesses.map(w => w.statePath), historyPaths: witnesses.map(w => w.historyPath) });
  const context = new HistoryContext({ kind: Field(2), object: state.object, before, operation: batchDigest(state.object, updates.operations) });
  return { updates, context, after: state.checkpoint() };
}

/** Unreachable from genesis: count eight cannot contain signer sequences 100+.
 * Native CBCL admits these fixtures; the experimental sequential model does not.
 * The next eight transitions are locally valid against the forged checkpoint.
 */
export function unreachablePrefix() {
  const oracle = native(Array.from({ length: 2 * BATCH }, (_, i) => ({
    signer: i % 4, seq: 100 + Math.floor(i / 4), value: i * 19 + 3,
    replaces: i < 4 ? null : '$head',
  })));
  const state = new State(objectId(oracle));
  oracle.messages.slice(0, BATCH).forEach(message => state.apply(operation(message)));
  const checkpoint = state.checkpoint();
  const next = makeBatch(state, oracle.messages.slice(BATCH));
  return { oracle, checkpoint, next };
}
