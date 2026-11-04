import assert from 'node:assert/strict';
import { Field } from 'o1js';
import { Context } from './program.js';
import { Message, operation, State } from './helpers.js';
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
