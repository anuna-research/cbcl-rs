import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { recipientOf, recipientOfLax, parseMessage } from '../src/index.ts';

test('audience uses the compiled parser and preserves the sigil', () => {
  for (const frame of ['(tell @bob hello)', '(lang d (ask @bob hello))', '(tell @bob "β")']) {
    const expected = '@bob';
    assert.equal(recipientOf(frame), expected);
    assert.equal(recipientOf(parseMessage(frame)), expected);
  }
  for (const frame of [
    '(envelope :via @other :to @room (tell @bob hello))',
    '(envelope :to @room :via @other (tell @bob hello))',
  ]) assert.equal(recipientOf(frame), '@room');
});

test('strict and host-authorized lax accessors share rejection boundaries', () => {
  assert.throws(() => recipientOf('(history @room :limit 5)'), /core performative/);
  assert.equal(recipientOfLax('(history @room :limit 5)'), '@room');
  for (const frame of [
    '(reply hello)', '(tell (@a @b) hello)', '(meta (define d (cbcl) @a))',
    '(envelope :to @a :to @b (tell @bob hello))',
    '(envelope :to @a :to @a (tell @bob hello))',
    '(envelope :to @a (tell @bob hello) :to @b)',
    '(envelope :to @a (tell () ()))',
  ]) {
    assert.throws(() => recipientOf(frame), Error, frame);
    assert.throws(() => recipientOfLax(frame), Error, frame);
  }
});

test('browser WASM matches the routing corpus and explicit strict-parser differences', async () => {
  const corpus = JSON.parse(await readFile(new URL('../../test-vectors/frame-rooms.json', import.meta.url), 'utf8'));
  for (const row of corpus.rows) {
    const expected = 'parserRoom' in row ? row.parserRoom : row.room;
    if (expected === null) {
      assert.throws(() => recipientOfLax(row.frame), row.parserErrorContains ? new RegExp(row.parserErrorContains) : Error, row.name);
    } else assert.equal(recipientOfLax(row.frame), expected, row.name);
  }
});
