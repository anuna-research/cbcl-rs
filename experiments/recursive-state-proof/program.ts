// Proof-carrying CRDT experiment, inspired by kit-dsn/proof-carrying-crdts.
// MIT-licensed upstream architecture; new fixed-set circuit below is original.
import {
  Bool, Field, Poseidon, Provable, PublicKey, SelfProof, Signature, Struct,
  UInt32, UInt64, ZkProgram,
} from 'o1js';

export const CAPACITY = 4;
const DOMAIN = Field(2026103001);

export class Record extends Struct({ nonce: UInt32, amount: UInt32, author: Bool }) {
  fields(object: Field) {
    return [DOMAIN, object, this.nonce.value, this.amount.value, this.author.toField()];
  }
  id(object: Field) { return Poseidon.hash(this.fields(object)); }
}
export class Context extends Struct({
  object: Field, kind: Field, left: Field, right: Field, operation: Field,
}) {}
export class Summary extends Struct({ root: Field, count: UInt32, total: UInt64 }) {}
export class Snapshot extends Struct({
  present: Provable.Array(Bool, CAPACITY),
  records: Provable.Array(Record, CAPACITY),
}) {
  summarize(object: Field): Summary {
    const ids = this.records.map(record => record.id(object));
    let count = UInt32.zero, total = UInt64.zero;
    for (let i = 0; i < CAPACITY; i++) {
      const active = this.present[i], record = this.records[i];
      // Canonical absent encoding and nonzero active amounts.
      active.or(record.nonce.equals(UInt32.zero)).assertTrue('absent nonce');
      active.or(record.amount.equals(UInt32.zero)).assertTrue('absent amount');
      active.or(record.author.not()).assertTrue('absent author');
      active.not().or(record.amount.equals(UInt32.zero).not()).assertTrue('zero contribution');
      if (i > 0) {
        active.not().or(this.present[i - 1]).assertTrue('padding must be trailing');
        active.not().or(ids[i - 1].lessThan(ids[i])).assertTrue('set must be sorted and unique');
      }
      count = count.add(Provable.if(active, UInt32, UInt32.one, UInt32.zero));
      total = total.add(Provable.if(active, UInt64, UInt64.from(record.amount), UInt64.zero));
    }
    const leaves = ids.map((id, i) => Provable.if(this.present[i], id, Field(0)));
    return new Summary({ root: Poseidon.hash([DOMAIN, object, ...leaves]), count, total });
  }
  assertMatches(object: Field, expected: Summary) {
    const actual = this.summarize(object);
    actual.root.assertEquals(expected.root, 'snapshot root');
    actual.count.value.assertEquals(expected.count.value, 'snapshot count');
    actual.total.value.assertEquals(expected.total.value, 'snapshot total');
  }
  contains(object: Field, id: Field) {
    return this.records.reduce((found, record, i) =>
      found.or(this.present[i].and(record.id(object).equals(id))), Bool(false));
  }
}

function assertSubset(object: Field, source: Snapshot, target: Snapshot) {
  for (let i = 0; i < CAPACITY; i++) {
    source.present[i].not().or(target.contains(object, source.records[i].id(object)))
      .assertTrue('union omitted a record');
  }
}

export function makeProgram(publicKeys: [PublicKey, PublicKey]) {
  return ZkProgram({
    name: 'cbcl-recursive-contributions-v2',
    publicInput: Context, // Receiver-owned object, parent roots and operation commitment.
    publicOutput: Summary,
    methods: {
      base: {
        privateInputs: [],
        async method(context: Context) {
          const object = context.object;
          context.kind.assertEquals(Field(0));
          context.left.assertEquals(Field(0)); context.right.assertEquals(Field(0)); context.operation.assertEquals(Field(0));
          const snapshot = new Snapshot({
            present: Array.from({ length: CAPACITY }, () => Bool(false)),
            records: Array.from({ length: CAPACITY }, () => new Record({ nonce: UInt32.zero, amount: UInt32.zero, author: Bool(false) })),
          });
          return { publicOutput: snapshot.summarize(object) };
        },
      },
      append: {
        privateInputs: [SelfProof, Snapshot, Record, Signature, Snapshot],
        async method(context: Context, previous: SelfProof<Context, Summary>, before: Snapshot,
          record: Record, signature: Signature, after: Snapshot) {
          const object = context.object;
          previous.verify();
          previous.publicInput.object.assertEquals(object, 'different object');
          context.kind.assertEquals(Field(1)); context.right.assertEquals(Field(0));
          context.left.assertEquals(previous.publicOutput.root, 'unexpected predecessor');
          context.operation.assertEquals(record.id(object), 'unexpected operation');
          before.assertMatches(object, previous.publicOutput);
          record.amount.greaterThan(UInt32.zero).assertTrue('zero contribution');
          const author = Provable.if(record.author, PublicKey, publicKeys[1], publicKeys[0]);
          signature.verify(author, record.fields(object)).assertTrue('invalid signature');
          assertSubset(object, before, after);
          const id = record.id(object);
          after.contains(object, id).assertTrue('appended record missing');
          for (let i = 0; i < CAPACITY; i++) {
            const nextId = after.records[i].id(object);
            after.present[i].not().or(before.contains(object, nextId).or(nextId.equals(id)))
              .assertTrue('append injected a record');
          }
          return { publicOutput: after.summarize(object) };
        },
      },
      merge: {
        privateInputs: [SelfProof, SelfProof, Snapshot, Snapshot, Snapshot],
        async method(context: Context, left: SelfProof<Context, Summary>, right: SelfProof<Context, Summary>,
          a: Snapshot, b: Snapshot, union: Snapshot) {
          const object = context.object;
          left.verify();
          right.verify();
          left.publicInput.object.assertEquals(object, 'different left object');
          right.publicInput.object.assertEquals(object, 'different right object');
          context.kind.assertEquals(Field(2)); context.operation.assertEquals(Field(0));
          context.left.assertEquals(left.publicOutput.root, 'unexpected left head');
          context.right.assertEquals(right.publicOutput.root, 'unexpected right head');
          a.assertMatches(object, left.publicOutput);
          b.assertMatches(object, right.publicOutput);
          assertSubset(object, a, union);
          assertSubset(object, b, union);
          for (let i = 0; i < CAPACITY; i++) {
            const id = union.records[i].id(object);
            union.present[i].not().or(a.contains(object, id).or(b.contains(object, id)))
              .assertTrue('union injected a record');
          }
          return { publicOutput: union.summarize(object) };
        },
      },
    },
  });
}
