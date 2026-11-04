/** Audit the serialized deliberately unsafe mutant evidence without reproving. */
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { setNumberOfWorkers, verify } from 'o1js';
setNumberOfWorkers(1);
const dir = 'evidence/recursive';
const mutant = JSON.parse(await readFile(dir + '/proof-verification-mutant-artifact.json', 'utf8'));
const honest = JSON.parse(await readFile(dir + '/verification-key.json', 'utf8'));
assert.equal(mutant.unsafeVariant, true);
assert.equal(await verify(mutant.forgedParent, mutant.verificationKey.data), false);
assert.equal(await verify(mutant.child, mutant.verificationKey.data), true);
assert.equal(await verify(mutant.child, honest.data), false);
console.log(JSON.stringify({ serializedInvalidParentRejected: true, serializedMutantChildVerifiedWithUnsafeKey: true, serializedMutantChildRejectedWithHonestKey: true }));
