// Extra adversarial arithmetic checks; these do NOT verify cryptographic proofs.
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { Field, Provable, Signature, ZkProgram } from 'o1js';
import { Context, makeProgram, Record as Operation, Snapshot } from './program.js';
import { appendContext, baseContext, Data, mergeContext, objectId, operation, publicKeys, snapshot, testKeys } from './helpers.js';
const object = objectId(), program = makeProgram(publicKeys);
class StateProof extends ZkProgram.Proof(program) {}
const records: Data[] = Array.from({ length: 5 }, (_, i) => ({ nonce: i + 1, amount: i + 2, author: i % 2 === 1 }));
function parent(data: Data[]) {
  return new StateProof({ proof: undefined, publicInput: baseContext(object), publicOutput: snapshot(object, data).summarize(object), maxProofsVerified: 2 });
}
const left = records.slice(0, 3), right = records.slice(2), dropped = records.slice(0, 4);
const context = mergeContext(object, snapshot(object, left).summarize(object).root, snapshot(object, right).summarize(object).root);
const results = [];
await assert.rejects(() => Provable.runAndCheck(async () => {
  await program.rawMethods.merge(context, parent(left), parent(right),
    Provable.witness(Snapshot, () => snapshot(object, left)),
    Provable.witness(Snapshot, () => snapshot(object, right)),
    Provable.witness(Snapshot, () => snapshot(object, dropped)));
}), /union omitted a record/);
results.push('union exceeding capacity cannot silently omit the fifth record');
const expected = mergeContext(object, snapshot(object, records.slice(0, 2)).summarize(object).root, snapshot(object, records.slice(1, 3)).summarize(object).root);
await Provable.runAndCheck(async () => {
  await program.rawMethods.merge(expected, parent(records.slice(0, 2)), parent(records.slice(1, 3)),
    Provable.witness(Snapshot, () => snapshot(object, records.slice(0, 2))),
    Provable.witness(Snapshot, () => snapshot(object, records.slice(1, 3))),
    Provable.witness(Snapshot, () => snapshot(object, records.slice(0, 3))));
});
for (const field of ['left', 'right', 'kind', 'operation'] as const) {
  await assert.rejects(() => Provable.runAndCheck(async () => {
    await program.rawMethods.merge(new Context({ ...expected, [field]: expected[field].add(1) }), parent(records.slice(0, 2)), parent(records.slice(1, 3)),
      Provable.witness(Snapshot, () => snapshot(object, records.slice(0, 2))),
      Provable.witness(Snapshot, () => snapshot(object, records.slice(1, 3))),
      Provable.witness(Snapshot, () => snapshot(object, records.slice(0, 3))));
  }));
  results.push(`merge public ${field} commitment cannot be changed`);
}
// A consistent claimed parent snapshot can pass all local arithmetic checks.
// This control shows why the real forged-parent test needs recursive proof verification.
const fabricated = records.slice(0, 1), added = records[1];
await Provable.runAndCheck(async () => {
  await program.rawMethods.append(appendContext(object, snapshot(object, fabricated).summarize(object).root, added), parent(fabricated),
    Provable.witness(Snapshot, () => snapshot(object, fabricated)),
    Provable.witness(Operation, () => operation(added)),
    Provable.witness(Signature, () => Signature.create(testKeys[Number(added.author)], operation(added).fields(object))),
    Provable.witness(Snapshot, () => snapshot(object, [fabricated[0], added])));
});
results.push('control: locally consistent fabricated parent requires cryptographic recursion to reject');
await mkdir('evidence', { recursive: true });
await writeFile('evidence/additional-checks.json', JSON.stringify({ status: 'passed', mode: 'constraints-only', results }, null, 2) + '\n');
console.log(JSON.stringify({ status: 'passed', checks: results }));
