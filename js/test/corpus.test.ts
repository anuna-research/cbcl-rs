// SPEC-019 REQ-1931: the runtime reproduces every vector of the conformance
// corpus (test-vectors/state): verdicts, state, and intents; forward,
// reversed, and duplicated. The runtime adds no semantics of its own.
import test from 'node:test';
import assert from 'node:assert/strict';
import { readdir, readFile } from 'node:fs/promises';
import { wireAddress } from '../src/index.ts';
import { createRuntime } from '../src/object/index.ts';

const dir = new URL('../../test-vectors/state/', import.meta.url);
const vectors = (await readdir(dir)).filter(name => name.endsWith('.json')).sort();

interface Vector {
  thread?: string; contract: string;
  messages: { canonical: string; signer: string }[];
  expect: { addresses: string[]; verdicts: Record<string, string>; state: unknown; intents?: unknown[] };
  intents?: { signer: string; verb: string; fields: Record<string, never> }[];
}

for (const name of vectors) {
  test(`corpus ${name}: verdicts, state, and intents match cbcl-rs`, async () => {
    const vector = JSON.parse(await readFile(new URL(name, dir), 'utf8')) as Vector;
    const thread = vector.thread ?? 't';
    const messages = vector.messages.map(m => ({ cid: wireAddress(m.canonical), signer: m.signer, canonical: m.canonical, thread }));
    assert.deepEqual(messages.map(m => m.cid), vector.expect.addresses);
    const runtime = createRuntime(vector.contract);
    assert.deepEqual(Object.fromEntries(runtime.verdicts(thread, messages)), vector.expect.verdicts);
    assert.deepEqual(runtime.read(thread, messages), vector.expect.state);
    const reversed = messages.slice().reverse();
    assert.deepEqual(createRuntime(vector.contract).read(thread, reversed), vector.expect.state);
    assert.deepEqual(runtime.read(thread, reversed, { fresh: true }), vector.expect.state);
    assert.deepEqual(createRuntime(vector.contract).read(thread, [...messages, ...messages]), vector.expect.state);
    const intents = (vector.intents || []).map(({ signer, verb, fields }) => {
      const bound = runtime.intend(thread, messages, signer, verb, fields);
      return bound.ok ? { canonical: bound.canonical } : { reject: bound.reject };
    });
    assert.deepEqual(intents, vector.expect.intents || []);
  });
}

test('the corpus is present', () => { assert.ok(vectors.length >= 3, vectors.join(', ')); });

// SPEC-019 REQ-1934: semantic corpus revisions are explicit.
test('the state corpus version is pinned', async () => {
  assert.equal((await readFile(new URL('VERSION', dir), 'utf8')).trim(), '1.0.0');
});
