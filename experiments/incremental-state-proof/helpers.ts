import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { Bool, Field, MerkleTree, UInt32 } from 'o1js';
import { Checkpoint, Context, Head, HEIGHT, Operation, Path } from './program.js';

export interface Data { signer: number; seq: number; value: number; replaces: string | null }
export interface Message extends Data { address: string; canonical: string }
export interface Oracle { source: string; thread: string; opener: string; messages: Message[]; state: { entries: Record<string, string>; sequences: Record<string, number>; all: Record<string, { by: string; value: string }> } }
export function native(records: Data[]): Oracle {
  const binary = process.env.CBCL_INCREMENTAL_ORACLE ?? fileURLToPath(new URL('../../target/debug/examples/incremental_oracle', import.meta.url));
  const result = spawnSync(binary, { input: JSON.stringify({ records }), encoding: 'utf8', maxBuffer: 8 << 20 });
  if (result.status !== 0 || result.error) throw new Error(`oracle failed: ${result.error ?? result.stderr}`);
  return JSON.parse(result.stdout) as Oracle;
}
export function objectId(oracle: Oracle) {
  return Field(BigInt('0x' + createHash('sha256').update(JSON.stringify(['incremental-register-v1', oracle.source, oracle.opener, oracle.thread])).digest('hex')) % Field.ORDER);
}
export function limbs(address: string | null): [Field, Field] {
  if (address === null) return [Field(0), Field(0)];
  assert.match(address, /^sha256-[0-9a-f]{64}$/);
  return [Field(BigInt('0x' + address.slice(7, 39))), Field(BigInt('0x' + address.slice(39)))];
}
export function operation(message: Message) {
  const [lo, hi] = limbs(message.address), [previousLo, previousHi] = limbs(message.replaces);
  return new Operation({ signer: UInt32.from(message.signer), seq: UInt32.from(message.seq), value: UInt32.from(message.value), previousLo, previousHi, lo, hi });
}
export function emptyHead() { return new Head({ present: Bool(false), lo: Field(0), hi: Field(0), seq: UInt32.zero, value: UInt32.zero }); }
export class State {
  readonly heads = new MerkleTree(HEIGHT);
  readonly history = new MerkleTree(HEIGHT);
  readonly bySigner = new Map<number, Head>();
  count = 0;
  constructor(readonly object: Field) {}
  checkpoint() { return new Checkpoint({ state: this.heads.getRoot(), history: this.history.getRoot(), count: UInt32.from(this.count) }); }
  witness(op: Operation) {
    const signer = Number(op.signer.toBigint());
    return {
      context: new Context({ object: this.object, before: this.checkpoint(), operation: op.digest(this.object) }),
      operation: op,
      head: this.bySigner.get(signer) ?? emptyHead(),
      statePath: new Path(this.heads.getWitness(BigInt(signer))),
      historyPath: new Path(this.history.getWitness(BigInt(this.count))),
    };
  }
  apply(op: Operation) {
    const head = op.head(), signer = Number(op.signer.toBigint());
    this.heads.setLeaf(BigInt(signer), head.leaf(this.object, op.signer));
    this.history.setLeaf(BigInt(this.count), op.digest(this.object));
    this.bySigner.set(signer, head); this.count++;
    return this.checkpoint();
  }
}
export function fields<T>(type: { toFields(value: T): Field[] }, value: T) { return type.toFields(value).map(x => x.toString()); }
export function assertCheckpoint(a: Checkpoint, b: Checkpoint) { assert.deepEqual(fields(Checkpoint, a), fields(Checkpoint, b)); }

/** Fixture generator; `$head` is resolved to native wire addresses by the oracle. */
export function trace(length: number, signers = 4) {
  return native(Array.from({ length }, (_, i) => ({ signer: i % signers, seq: Math.floor(i / signers), value: i * 19 + 3, replaces: i < signers ? null : '$head' })));
}
export function stateFromNative(oracle: Oracle) {
  const object = objectId(oracle), state = new State(object);
  // Reconstruct head values from native fold output, not host apply's last head.
  for (const [label, value] of Object.entries(oracle.state.entries)) {
    const signer = Number(label.slice('@writer'.length));
    const seq = oracle.state.sequences[label];
    const message = oracle.messages.find(m => m.signer === signer && m.seq === seq);
    assert.ok(message, 'native sequence must identify a fixture message');
    const [lo, hi] = limbs(message.address);
    const head = new Head({ present: Bool(true), lo, hi, seq: UInt32.from(seq), value: UInt32.from(Number(value)) });
    state.heads.setLeaf(BigInt(signer), head.leaf(object, UInt32.from(signer)));
    state.bySigner.set(signer, head);
  }
  oracle.messages.forEach((message, i) => state.history.setLeaf(BigInt(i), operation(message).digest(object)));
  state.count = oracle.messages.length;
  return state;
}
