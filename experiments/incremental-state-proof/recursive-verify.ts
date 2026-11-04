/** A receiver verifies one final artifact; no native replay or predecessor file. */
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { Cache, Field, setNumberOfWorkers } from 'o1js';
import { Checkpoint } from './program.js';
import { HistoryProof, historyProgram } from './recursive-program.js';
import { verifyHistory } from './recursive-receiver.js';
setNumberOfWorkers(1);
const dir = 'evidence/recursive';
const record = JSON.parse(await readFile(dir + '/progress.json', 'utf8'));
assert.equal(record.status, 'passed', 'recursive run must finish its real negative checks');
assert.ok([128, 256].includes(record.target));
const histories = [0, 1, 8, 32, 128, ...(record.target === 256 ? [256] : [])];
assert.deepEqual(record.proofs.map((row: { history: number }) => row.history), histories, 'all promised complete histories must exist');
const selected = process.argv.find(x => x.startsWith('--history='))?.slice(10);
const wanted = selected === undefined ? histories : [Number(selected)];
assert.ok(wanted.every(n => histories.includes(n)), 'history was not proved');
const { verificationKey } = await historyProgram.compile({ cache: Cache.FileSystem('.cache-recursive') });
assert.equal(verificationKey.hash.toString(), record.verificationKeyHash);
const savedKey = JSON.parse(await readFile(dir + '/verification-key.json', 'utf8'));
assert.equal(savedKey.hash, verificationKey.hash.toString());
assert.equal(savedKey.data, verificationKey.data);
for (const n of wanted) {
  const row = record.proofs.find((r: { history: number }) => r.history === n);
  assert.equal(row.file, `history-${n}.json`, 'artifact path must match selected history');
  const proof = await HistoryProof.fromJSON(JSON.parse(await readFile(`${dir}/${row.file}`, 'utf8')));
  const expected = { object: Field(row.expected.object), checkpoint: Checkpoint.fromJSON(row.expected.checkpoint) };
  assert.equal(expected.object.toString(), record.object);
  assert.equal(expected.checkpoint.count.toBigint(), BigInt(n));
  assert.equal(await verifyHistory(proof, expected, verificationKey.data), true);
  console.log(JSON.stringify({ history: n, verifiedSingleFinalProof: true, verificationKeyHash: verificationKey.hash.toString() }));
}
