import { Field, MerkleTree, Poseidon, Provable, SelfProof, Struct, UInt32, ZkProgram } from 'o1js';
import { Checkpoint, Context, Head, HEIGHT, Operation, Path, program as transition } from './program.js';

export const BATCH = 8;
export const EMPTY_ROOT = new MerkleTree(HEIGHT).getRoot();
const BATCH_DOMAIN = Field(2026110403);
export class HistoryContext extends Struct({ kind: Field, object: Field, before: Checkpoint, operation: Field }) {}
export class Updates extends Struct({
  operations: Provable.Array(Operation, BATCH),
  heads: Provable.Array(Head, BATCH),
  statePaths: Provable.Array(Path, BATCH),
  historyPaths: Provable.Array(Path, BATCH),
}) {}
export function emptyCheckpoint() { return new Checkpoint({ state: EMPTY_ROOT, history: EMPTY_ROOT, count: UInt32.zero }); }
export function batchDigest(object: Field, operations: Operation[]) {
  return Poseidon.hash([BATCH_DOMAIN, object, ...operations.map(op => op.digest(object))]);
}
function sameCheckpoint(a: Checkpoint, b: Checkpoint, label: string) {
  a.state.assertEquals(b.state, label + ' state');
  a.history.assertEquals(b.history, label + ' history');
  a.count.value.assertEquals(b.count.value, label + ' count');
}
function bindParent(context: HistoryContext, previous: SelfProof<HistoryContext, Checkpoint>) {
  previous.verify();
  previous.publicInput.object.assertEquals(context.object, 'predecessor object');
  sameCheckpoint(previous.publicOutput, context.before, 'predecessor checkpoint');
}
export const historyProgram = ZkProgram({
  name: 'cbcl-recursive-register-paths-b8-v1',
  publicInput: HistoryContext,
  publicOutput: Checkpoint,
  methods: {
    base: {
      privateInputs: [],
      async method(context: HistoryContext) {
        context.kind.assertEquals(0, 'genesis method');
        context.operation.assertEquals(0, 'genesis operation');
        context.before.count.value.assertEquals(0, 'genesis count');
        context.before.state.assertEquals(EMPTY_ROOT, 'genesis state');
        context.before.history.assertEquals(EMPTY_ROOT, 'genesis history');
        return { publicOutput: context.before };
      },
    },
    step: {
      privateInputs: [SelfProof, Operation, Head, Path, Path],
      async method(context: HistoryContext, previous: SelfProof<HistoryContext, Checkpoint>, operation: Operation, head: Head, statePath: Path, historyPath: Path) {
        context.kind.assertEquals(1, 'step method');
        bindParent(context, previous);
        return transition.rawMethods.step(new Context({ object: context.object, before: context.before, operation: context.operation }), operation, head, statePath, historyPath);
      },
    },
    batch: {
      privateInputs: [SelfProof, Updates],
      async method(context: HistoryContext, previous: SelfProof<HistoryContext, Checkpoint>, updates: Updates) {
        context.kind.assertEquals(2, 'batch method');
        bindParent(context, previous);
        batchDigest(context.object, updates.operations).assertEquals(context.operation, 'batch operation digest');
        let current = context.before;
        // SIMPLIFY: fixed batches amortize recursion; step handles shorter tails.
        // Authenticated state remains capped by the original tree depth (RECURSION-BRIEF).
        for (let i = 0; i < BATCH; i++) {
          const operation = updates.operations[i];
          const result = await transition.rawMethods.step(new Context({ object: context.object, before: current, operation: operation.digest(context.object) }), operation, updates.heads[i], updates.statePaths[i], updates.historyPaths[i]);
          current = result.publicOutput;
        }
        return { publicOutput: current };
      },
    },
  },
});
export class HistoryProof extends ZkProgram.Proof(historyProgram) {}
