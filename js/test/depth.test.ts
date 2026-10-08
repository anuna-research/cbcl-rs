// SPEC-001 REQ-046 (BUG-007) on the real wasm build: a frame nested past the
// parser's limit is refused with the parser's ordinary reason — a string from
// the raw glue, never a RangeError or a trap — and the same instance then
// reads valid frames. Before the limit, a balanced 7000-deep frame overflowed
// node's stack and a second call poisoned the instance ("memory access out
// of bounds" for every later call).
import test from 'node:test';
import assert from 'node:assert/strict';
import { read, parse, parseMessage, readAct, foldState, messageHash } from '../src/index.ts';
import * as glue from '../src/cbcl_wasm.js';

const LIMIT = 256;
const nest = (depth: number) => '('.repeat(depth) + ')'.repeat(depth);
const tell = (depth: number) => `(tell @room ${nest(depth - 1)})`;
const OFFSET = '(tell @room '.length + LIMIT - 1;
const REASON = `at byte ${OFFSET}: list nesting exceeds limit ${LIMIT}`;

function thrown(call: () => unknown): unknown {
  try { call(); } catch (error) { return error; }
  assert.fail('expected a refusal');
}

test('the raw glue refuses past the limit with a string, repeatedly, and keeps working', () => {
  const far = `(tell @room ${'('.repeat(100_000)}`;
  for (const name of ['parse', 'read', 'parse_message', 'run_pipeline', 'message_hash', 'read_act', 'fold', 'admit'] as const) {
    const exp = glue[name] as (s: string) => string;
    for (let i = 0; i < 3; i++) {
      for (const input of [tell(LIMIT + 1), far]) {
        const error = thrown(() => exp(input));
        assert.equal(typeof error, 'string', `${name}: ${String(error)}`);
        assert.ok((error as string).includes(REASON), `${name}: ${String(error)}`);
      }
      assert.equal(glue.parse_message('(tell @room "hi")'), '(tell @room "hi")', `${name}: benign after refusal`);
    }
  }
});

test('depth N-1 and N are read; N+1 is refused at the first parenthesis past the limit', () => {
  assert.equal(parse(nest(LIMIT - 1)), nest(LIMIT - 1));
  assert.equal(parse(nest(LIMIT)), nest(LIMIT));
  assert.throws(() => parse(nest(LIMIT + 1)), { message: `at byte ${LIMIT}: list nesting exceeds limit ${LIMIT}` });
  let tree = read(tell(LIMIT));
  let depth = 0;
  while (Array.isArray(tree)) { depth++; tree = tree[tree.length - 1]; }
  assert.equal(depth, LIMIT);
  assert.ok(parseMessage(tell(LIMIT)).startsWith('(tell @room ((('));
});

test('the typed wrappers carry the parser reason and the instance stays usable', () => {
  for (let i = 0; i < 3; i++) {
    for (const call of [() => read(tell(LIMIT + 1)), () => parseMessage(tell(LIMIT + 1)), () => readAct(tell(LIMIT + 1)), () => foldState(tell(LIMIT + 1)), () => messageHash(tell(LIMIT + 1))]) {
      const error = thrown(call);
      assert.ok(error instanceof Error && !(error instanceof RangeError));
      assert.match(error.message, /list nesting exceeds limit 256/);
    }
    assert.deepEqual(read('(tell @room "hi")'), ['tell', '@room', { str: 'hi' }]);
  }
});
