import { Bool, Field, MerkleWitness, Poseidon, Provable, Struct, UInt32, ZkProgram } from 'o1js';

export const HEIGHT = 17;
export const CAPACITY = 2 ** (HEIGHT - 1);
const HEAD_DOMAIN = Field(2026110401);
const OP_DOMAIN = Field(2026110402);
export class Path extends MerkleWitness(HEIGHT) {}
export class Head extends Struct({ present: Bool, lo: Field, hi: Field, seq: UInt32, value: UInt32 }) {
  leaf(object: Field, signer: UInt32) {
    this.lo.toBits(128); this.hi.toBits(128);
    for (const field of [this.lo, this.hi, this.seq.value, this.value.value]) {
      this.present.or(field.equals(0)).assertTrue('noncanonical empty head');
    }
    return Provable.if(this.present, Poseidon.hash([HEAD_DOMAIN, object, signer.value, this.lo, this.hi, this.seq.value, this.value.value]), Field(0));
  }
}
export class Operation extends Struct({ signer: UInt32, seq: UInt32, value: UInt32, previousLo: Field, previousHi: Field, lo: Field, hi: Field }) {
  digest(object: Field) {
    for (const field of [this.previousLo, this.previousHi, this.lo, this.hi]) field.toBits(128);
    this.lo.equals(0).and(this.hi.equals(0)).assertFalse('zero wire address');
    return Poseidon.hash([OP_DOMAIN, object, ...Operation.toFields(this)]);
  }
  head() { return new Head({ present: Bool(true), lo: this.lo, hi: this.hi, seq: this.seq, value: this.value }); }
}
export class Checkpoint extends Struct({ state: Field, history: Field, count: UInt32 }) {}
export class Context extends Struct({ object: Field, before: Checkpoint, operation: Field }) {}

export const program = ZkProgram({
  name: 'cbcl-incremental-register-paths-v1',
  publicInput: Context,
  publicOutput: Checkpoint,
  methods: {
    step: {
      privateInputs: [Operation, Head, Path, Path],
      async method(context: Context, operation: Operation, head: Head, statePath: Path, historyPath: Path) {
        // SIMPLIFY: sequential per-signer subset only; authenticated active-head
        // indexes and native concurrency semantics are successor work (BRIEF P1/P2).
        operation.digest(context.object).assertEquals(context.operation, 'operation binding');
        statePath.calculateIndex().assertEquals(operation.signer.value, 'signer index');
        const oldLeaf = head.leaf(context.object, operation.signer);
        statePath.calculateRoot(oldLeaf).assertEquals(context.before.state, 'old state root');
        operation.previousLo.assertEquals(head.lo, 'replacement low');
        operation.previousHi.assertEquals(head.hi, 'replacement high');
        const nextSeq = Provable.if(head.present, UInt32, head.seq.add(1), UInt32.zero);
        operation.seq.value.assertEquals(nextSeq.value, 'sequential write');
        context.before.count.lessThan(UInt32.from(CAPACITY)).assertTrue('history capacity');
        historyPath.calculateIndex().assertEquals(context.before.count.value, 'append index');
        historyPath.calculateRoot(Field(0)).assertEquals(context.before.history, 'append slot must be empty');
        const nextLeaf = operation.head().leaf(context.object, operation.signer);
        nextLeaf.equals(0).assertFalse('reserved empty head hash');
        context.operation.equals(0).assertFalse('reserved empty history hash');
        return { publicOutput: new Checkpoint({
          state: statePath.calculateRoot(nextLeaf),
          history: historyPath.calculateRoot(context.operation),
          count: context.before.count.add(1),
        }) };
      },
    },
  },
});
