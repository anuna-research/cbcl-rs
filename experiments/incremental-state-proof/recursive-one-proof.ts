/** Minimal receiver: caller owns key and expected head; provider supplies proof. */
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { Field, setNumberOfWorkers } from 'o1js';
import { Checkpoint } from './program.js';
import { HistoryProof } from './recursive-program.js';
import { verifyHistory } from './recursive-receiver.js';
setNumberOfWorkers(1);
const args = process.argv.slice(2);
assert.equal(args.length, 3, 'usage: recursive-one-proof.ts proof.json trusted-key.json expected-head.json');
const [proofPath, keyPath, headPath] = args;
const proof = await HistoryProof.fromJSON(JSON.parse(await readFile(proofPath, 'utf8')));
const key = JSON.parse(await readFile(keyPath, 'utf8'));
const head = JSON.parse(await readFile(headPath, 'utf8'));
const expected = { object: Field(head.object), checkpoint: Checkpoint.fromJSON(head.checkpoint) };
assert.equal(await verifyHistory(proof, expected, key.data), true);
console.log(JSON.stringify({ completeWrites: expected.checkpoint.count.toString(), verified: true, proofFilesRead: 1, predecessorProofFilesRead: 0 }));
