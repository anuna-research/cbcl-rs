import assert from 'node:assert/strict';
import { Field, verify } from 'o1js';
import { Checkpoint } from './program.js';
import { HistoryProof } from './recursive-program.js';
export interface ExpectedHead { object: Field; checkpoint: Checkpoint }
/** Receiver-owned key/object/tip; no predecessor proof or message is consulted. */
export async function verifyHistory(proof: HistoryProof, expected: ExpectedHead, key: string) {
  assert.equal(proof.publicInput.object.toString(), expected.object.toString(), 'unexpected history object');
  assert.deepEqual(Checkpoint.toFields(proof.publicOutput).map(x => x.toString()), Checkpoint.toFields(expected.checkpoint).map(x => x.toString()), 'unexpected final checkpoint');
  return verify(proof, key);
}
