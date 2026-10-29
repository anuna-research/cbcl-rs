import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { Bool, Field, PrivateKey, UInt32 } from 'o1js';
import { CAPACITY, Context, Record as Operation, Snapshot } from './program.js';

export interface Data { nonce: number; amount: number; author: boolean }
// Public synthetic test secrets. Never enrol these keys in a real system.
export const testKeys = [PrivateKey.fromBigInt(1n), PrivateKey.fromBigInt(2n)] as const;
export const publicKeys = [testKeys[0].toPublicKey(), testKeys[1].toPublicKey()] as [ReturnType<PrivateKey['toPublicKey']>, ReturnType<PrivateKey['toPublicKey']>];
export function operation(data: Data) {
  return new Operation({ nonce: UInt32.from(data.nonce), amount: UInt32.from(data.amount), author: Bool(data.author) });
}
export function snapshot(object: Field, records: Data[]) {
  const unique = new Map<string, Data>();
  for (const data of records) unique.set(operation(data).id(object).toString(), data);
  const sorted = [...unique].sort(([a], [b]) => BigInt(a) < BigInt(b) ? -1 : BigInt(a) > BigInt(b) ? 1 : 0).map(([, data]) => data);
  if (sorted.length > CAPACITY) throw new Error('snapshot capacity exceeded');
  return new Snapshot({
    present: Array.from({ length: CAPACITY }, (_, i) => Bool(i < sorted.length)),
    records: Array.from({ length: CAPACITY }, (_, i) => operation(sorted[i] ?? { nonce: 0, amount: 0, author: false })),
  });
}
export function native(records: Data[]) {
  const binary = fileURLToPath(new URL('../../target/debug/examples/recursive_oracle', import.meta.url));
  const run = spawnSync(binary, { input: JSON.stringify({ records }), encoding: 'utf8', maxBuffer: 100_000 });
  if (run.status !== 0 || run.error) throw new Error(`native oracle: ${run.error ?? run.stderr}`);
  return JSON.parse(run.stdout) as { dialect: string; opener: string; thread: string; state: { count: number; total: number }; messages: unknown[] };
}
export function objectId() {
  const oracle = native([]);
  // An externally established binding to the expected native object. The
  // circuit checks this Field everywhere; it does not implement SHA-256/CBCL.
  const digest = createHash('sha256').update(JSON.stringify(['recursive-contributions-v1', oracle.dialect, oracle.opener, oracle.thread])).digest('hex');
  return Field(BigInt(`0x${digest}`) % Field.ORDER);
}

export function baseContext(object: Field) {
  return new Context({ object, kind: Field(0), left: Field(0), right: Field(0), operation: Field(0) });
}
export function appendContext(object: Field, before: Field, data: Data) {
  return new Context({ object, kind: Field(1), left: before, right: Field(0), operation: operation(data).id(object) });
}
export function mergeContext(object: Field, left: Field, right: Field) {
  return new Context({ object, kind: Field(2), left, right, operation: Field(0) });
}
