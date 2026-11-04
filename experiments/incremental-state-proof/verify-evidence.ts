/** Reverify serialized artifacts and independently reconstruct native expectations. */
import assert from 'node:assert/strict';
import { readFile, writeFile } from 'node:fs/promises';
import { Cache, ZkProgram, setNumberOfWorkers, verify } from 'o1js';
import { Checkpoint, Context, program } from './program.js';
import { assertCheckpoint, fields, objectId, operation, State, stateFromNative, trace } from './helpers.js';
setNumberOfWorkers(1);
const record = JSON.parse(await readFile('evidence/real-proofs.json', 'utf8'));
assert.ok(Array.isArray(record.proofs), 'proof artifacts must be an array');
assert.deepEqual(record.proofs.map((row: { history: number }) => row.history), [8, 256], 'both promised histories must be present');
const { verificationKey } = await program.compile({ cache: Cache.FileSystem('.cache') });
assert.equal(verificationKey.hash.toString(), record.verificationKeyHash);
await writeFile('evidence/verification-key.json', JSON.stringify({ hash: verificationKey.hash.toString(), data: verificationKey.data }, null, 2) + '\n');
class StepProof extends ZkProgram.Proof(program) {}
for (const row of record.proofs) {
  const oracle = trace(row.history + 1), state = new State(objectId(oracle));
  oracle.messages.slice(0, -1).forEach(m => state.apply(operation(m)));
  const expected = state.witness(operation(oracle.messages.at(-1)!)).context;
  const proof = await StepProof.fromJSON(row.proof);
  assert.deepEqual(fields(Context, proof.publicInput), fields(Context, expected));
  assertCheckpoint(proof.publicOutput, stateFromNative(oracle).checkpoint());
  assert.equal(await verify(row.proof, verificationKey.data), true);
  console.log(JSON.stringify({ history: row.history, nativeExpectationsMatch: true, serializedProofVerified: true, verificationKeyHash: verificationKey.hash.toString() }));
}
