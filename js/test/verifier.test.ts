import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { ready, isReady, read, parse, parseMessage, messageHash, wireAddress, dialectHash, verifyDialect, verifyShape, verifyStateShape, verifyProtocol, compileContract, defineText, describeDialect, readAct, parseSexpr, kwargs, asText, readValue } from '../src/index.ts';

const dialects = new URL('../../dialects/', import.meta.url);
const LUNCH = await readFile(new URL('lunch-vote.cbcl', dialects), 'utf8');

test('the verifier initialises synchronously under node', async () => {
  assert.equal(isReady(), true);
  await ready();
});

test('read is the parser: comments, escapes, and malformed input', () => {
  assert.deepEqual(read('; c\n(tell @bo "a)b\\"" :n -3 :ok #t)'), ['tell', '@bo', { str: 'a)b"' }, ':n', '-3', ':ok', '#t']);
  assert.deepEqual(parseSexpr('"a\\qb"'), null);
  assert.deepEqual(parseSexpr('(unclosed'), null);
  assert.throws(() => read('(unclosed'), /parse error/);
  const ast = parseSexpr('(lang budget (ask @room "how much?" :from @mira :thread "t"))');
  assert.ok(Array.isArray(ast));
  const inner = (ast as unknown[])[2];
  assert.equal(asText(kwargs(inner as never).from), '@mira');
  assert.deepEqual(readValue(['#t', '-4', { str: 's' }]), [true, -4, 's']);
  const define = defineText(`; served by the room\n(meta (teach ${LUNCH}))`);
  assert.ok(define.startsWith('(define lunch-vote (cbcl) @anuna'));
  assert.equal(defineText(define), define);
  assert.throws(() => defineText('(tell @a "x")'));
  const info = describeDialect(LUNCH);
  assert.equal(info.opener, 'propose');
  assert.deepEqual(info.state.tally, ['histogram', 'ballots']);
  assert.deepEqual(info.domains, [{ verb: 'vote', key: 'choice', field: 'options' }]);
  assert.equal(info.bounds['max-string'], 280);
  const act = readAct('(lang lunch-vote (vote @lunch :choice "x" :n 3 :caused-by begin :thread "v" :from @b))');
  assert.deepEqual([act.dialect, act.verb, act.recipients, act.fields, act.thread, act.from, act.causedBy], ['lunch-vote', 'vote', ['@lunch'], { choice: 'x', n: 3 }, 'v', '@b', 'begin']);
  assert.equal(act.address, wireAddress('(lang lunch-vote (vote @lunch :choice "x" :n 3 :caused-by begin :thread "v" :from @b))'));
});

test('canonical form, addresses, and the self-address', () => {
  const message = '(tell @bo "hi" :from @a)';
  assert.equal(parse(message), parseMessage(message));
  assert.match(messageHash(message), /^sha256:[0-9a-f]{64}$/);
  assert.equal(wireAddress(message), messageHash(message).replace('sha256:', 'sha256-'));
  assert.match(dialectHash(LUNCH), /^sha256-[0-9a-f]{64}$/);
  assert.doesNotThrow(() => verifyDialect(LUNCH));
  assert.throws(() => verifyDialect(LUNCH.replace('(then propose vote)', '(then missing vote)')), /verification failed/);
});

test('shape, state shape, and protocol verdicts are cbcl-rs blame', () => {
  assert.deepEqual(verifyShape(LUNCH, 'vote', '(vote @lunch :choice "x")'), { ok: true });
  const bad = verifyShape(LUNCH, 'vote', '(vote @lunch :choice 1)');
  assert.equal(bad.ok, false); assert.match((bad as { reason: string }).reason, /choice/);
  assert.equal(verifyStateShape(LUNCH, '(lang lunch-vote (vote @lunch :choice "x" :extra 1 :caused-by begin :thread "v" :from @b))').ok, false);
  const opener = '(lang lunch-vote (propose @lunch :question "Q" :options ("a") :caused-by begin :thread "v" :from @a))';
  assert.equal(verifyProtocol(LUNCH, 'v', opener), 'Valid');
  // verify-protocol predates the state layer: it keys history by the canonical
  // `sha256:` hash, quoted in :caused-by because the lexer reads `:` as a keyword.
  const vote = `(lang lunch-vote (vote @lunch :choice "a" :caused-by ${JSON.stringify(messageHash(opener))} :thread "v" :from @b))`;
  assert.equal(verifyProtocol(LUNCH, 'v', vote, [[messageHash(opener), opener]]), 'Valid');
  assert.equal(verifyProtocol(LUNCH, 'v', vote), 'Unknown');
  assert.equal(verifyProtocol(LUNCH, 'v', `(lang lunch-vote (vote @lunch :choice "a" :caused-by begin :thread "v" :from @b))`), 'Violation');
});

test('SPEC-087 TEST-001: the contract compile is cbcl-rs and names the authored dialects', async () => {
  const checklist = {
    version: 3, kind: 'contract', name: 'checklist', author: '@anuna',
    roles: { owner: 'singleton', member: 'indexed' },
    verbs: {
      open: { after: ['begin'], fields: { title: 'string' }, from: 'owner', to: ['owner', 'member'] },
      check: { after: ['open'], fields: { item: 'string', done: 'bool' }, from: 'member', to: ['owner', 'member'] },
      drop: { after: ['open'], fields: { item: 'string' }, from: 'owner', to: ['owner', 'member'] },
    },
    state: { title: ['last', 'open', 'title'], items: ['registerPerKey', 'check', 'item', 'done', 'drop'] },
  };
  const out = compileContract(JSON.stringify(checklist));
  assert.equal(out.name, dialectHash(await readFile(new URL('checklist.cbcl', dialects), 'utf8')));
  assert.equal(out.label, 'checklist');
  assert.ok(out.dialect.startsWith(`(define ${out.name} (cbcl) @anuna`));
  assert.throws(() => compileContract('{"version":2}'), /contract:/);
});

test('a refusal is thrown as an Error carrying cbcl-rs\'s reason', () => {
  assert.throws(() => readAct('(open'), (error: unknown) => error instanceof Error && /unexpected|unterminated|EOF|end/i.test(error.message));
  assert.throws(() => compileContract('{"version":3,"kind":"contract","name":"x","verbs":{"open":{"after":["begin"],"fields":{}},"a":{"after":["a"],"fields":{}}},"state":{"n":["count","open"]}}'),
    (error: unknown) => error instanceof Error && /R5.*cycle/.test(error.message));
});
