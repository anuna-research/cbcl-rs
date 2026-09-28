import test from 'node:test';
import assert from 'node:assert/strict';
import { defineContract, importObject, c, enumOf, readAct, actRecord, isSDKDialect, keywordText, ThreadStore, type CbclObject, type Msg } from '../src/object/index.ts';
import { verifyDialect, dialectHash, wireAddress } from '../src/index.ts';

const checklist = {
  name: 'agent-checklist',
  verbs: {
    open: { after: ['begin'], fields: { title: 'string' } },
    check: { after: ['open'], fields: { item: 'string', done: 'bool' } },
    drop: { after: ['open'], fields: { item: 'string' } },
  },
  state: { title: c.last('open', 'title'), items: c.registerPerKey('check', 'item', 'done', 'drop'), all: c.valuesPerKey('check', 'item', 'done', 'drop'), checks: c.count('check'), any: c.exists('check') },
};
const lunchVote = {
  name: 'lunch-vote', author: '@anuna',
  requirements: { maxDepth: 12, maxExpansionSize: 2048, verificationTime: 200 },
  bounds: { maxString: 280, maxList: 24 },
  verbs: { propose: { after: ['begin'], fields: { question: 'string', options: 'list' as const } }, vote: { after: ['propose'], fields: { choice: enumOf('options') } } },
  state: { question: c.last('propose', 'question'), options: c.last('propose', 'options'), ballots: c.latestPerSigner('vote', 'choice'), tally: c.histogram('ballots') },
};
const collections = {
  name: 'collections',
  verbs: {
    open: { after: ['begin'], fields: { title: 'string' } }, add: { after: ['open'], fields: { tag: 'string', op: 'string' } }, remove: { after: ['open'], fields: { tag: 'string' } },
    credit: { after: ['open'], fields: { amount: 'number' as const, op: 'string' } }, debit: { after: ['open'], fields: { amount: 'number' as const, op: 'string' } }, write: { after: ['open'], fields: { text: 'string' } },
  },
  state: { tags: c.observedSet('add', 'remove', 'tag'), seen: c.setUnion('add', 'tag'), adds: c.count('add'), credits: c.events('credit', 'amount'), total: c.sum('credits'), balance: c.counter('credit', 'debit', 'amount'), choices: c.values('write', 'text'), ops: c.latestPerKey('add', 'tag', 'op') },
};

function host(me: string, store = new ThreadStore()) {
  const sent: string[] = [];
  return { store, sent, me: () => me, send: async (text: string) => { sent.push(text); return true; } };
}
function opened(object: CbclObject, thread = 'demo', fields: Record<string, never> | Record<string, unknown> = { title: 'Launch' }) {
  const store = new ThreadStore();
  const root = actRecord(object.open({ room: '@general', thread, from: '@agent', fields: fields as never }), '@agent');
  store.append(root);
  return { store, root };
}
/** A peer's act that saw no current write (`:replaces ()`): concurrent by construction. */
const remote = (object: CbclObject, root: Msg, verb: string, kw: Record<string, never> | Record<string, unknown>, signer: string, thread = 'demo') =>
  actRecord(`(lang ${object.name} (${verb} @general ${keywordText(kw as never)} :replaces () :caused-by ${root.cid} :thread ${JSON.stringify(thread)} :from ${signer}))`, signer);

test('a contract compiles to a self-addressed dialect the verifier accepts', async () => {
  const object = await defineContract(checklist);
  assert.ok(isSDKDialect(object.name));
  assert.equal(object.label, 'agent-checklist');
  assert.equal(dialectHash(object.dialect), object.name);
  assert.doesNotThrow(() => verifyDialect(object.dialect));
  assert.equal((await importObject(object.serialized)).name, object.name);
  assert.equal(object.info.opener, 'open');
  assert.deepEqual(Object.keys(object.info.verbs.check.fields), ['item', 'done']);
  await assert.rejects(defineContract({ ...checklist, verbs: { ...checklist.verbs, check: { ...checklist.verbs.check, after: ['open', 'check'] } } }), /R5/);
  await assert.rejects(defineContract({ ...checklist, view: [] } as never), /host package/);
  for (const field of ['from', 'replaces', 'key']) {
    const spec = structuredClone(checklist) as never as typeof checklist;
    (spec.verbs.check.fields as Record<string, string>)[field] = 'string';
    await assert.rejects(defineContract(spec), /invalid field name/);
  }
});

test('the opener is verified; the fold is order-independent and duplicate-insensitive', async () => {
  const object = await defineContract(checklist);
  const { store, root } = opened(object);
  assert.match(root.canonical, new RegExp(`^\\(lang ${object.name} \\(open @general :title "Launch" :caused-by begin :thread "demo" :from @agent\\)\\)$`));
  assert.throws(() => object.open({ room: '@general', thread: 't', from: '@a', fields: { title: 7 } }), /invalid opener fields/);
  assert.throws(() => object.open({ room: '@general', thread: 't', from: '@a', fields: {} }), /exactly title/);
  const agent = object.agent(host('@human', store));
  assert.equal((await agent.act('demo', 'check', { item: 'Ship', done: true })).ok, true);
  const messages = store.messages('demo');
  assert.deepEqual(object.read(messages), { title: 'Launch', items: { Ship: true }, all: { Ship: [true] }, checks: 1, any: true });
  assert.deepEqual(object.read(messages.slice().reverse()), object.read(messages));
  assert.deepEqual(object.read([...messages, ...messages]), object.read(messages));
});

test('the broker refuses core performatives, unknown verbs, the opener, and forged routing', async () => {
  const object = await defineContract(checklist);
  const { store } = opened(object);
  const h = host('@agent', store);
  const agent = object.agent(h);
  assert.equal((await agent.act('demo', 'hello', {})).ok, false);
  assert.equal((await agent.act('demo', 'nope', {})).ok, false);
  assert.equal((await agent.act('demo', 'open', { title: 'again' })).ok, false);
  for (const forged of [{ from: '@mira' }, { thread: 'other' }, { dialect: 'x' }, { 'caused-by': 'begin' }, { replaces: [] }]) {
    assert.equal((await agent.act('demo', 'check', { item: 'x', done: true, ...forged })).ok, false, JSON.stringify(forged));
  }
  assert.equal((await agent.act('demo', 'check', { item: 'x', done: true, from: '@agent' })).ok, true); // an echoed binding is stripped
  assert.equal(h.sent.length, 1);
  assert.deepEqual(agent.maySend('demo'), ['check', 'drop']);
});

test('domains: the binder refuses an out-of-opener choice; a received one contributes nothing', async () => {
  const object = await defineContract(lunchVote);
  const { store, root } = opened(object, 'v1', { question: 'Lunch?', options: ['yes', 'no'] });
  const h = host('@agent', store);
  const agent = object.agent(h);
  const outside = await agent.act('v1', 'vote', { choice: 'outside' });
  assert.equal(outside.ok, false); assert.match((outside as { reason: string }).reason, /domain/); assert.equal(h.sent.length, 0);
  assert.equal((await agent.act('v1', 'vote', { choice: 'yes' })).ok, true);
  const stray = actRecord(`(lang ${object.name} (vote @general :choice "elsewhere" :caused-by ${root.cid} :thread "v1" :from @stranger))`, '@stranger');
  store.append(stray);
  assert.equal(object.verdicts(store.messages('v1'), 'v1').get(stray.cid), 'accepted');
  assert.deepEqual(agent.read('v1').tally, { yes: 1 });
  assert.equal((await agent.act('v1', 'vote', { choice: '😀'.repeat(80) })).ok, false); // max-string 280
});

test('registers: replacements bind to the intent key, a peer write is concurrent, delete names current writes', async () => {
  const object = await defineContract(checklist);
  const { store, root } = opened(object, 't');
  const agent = object.agent(host('@a', store));
  const milk = await agent.act('t', 'check', { item: 'milk', done: false });
  const eggs = await agent.act('t', 'check', { item: 'eggs', done: false });
  assert.ok(milk.ok && eggs.ok);
  assert.deepEqual(readAct(eggs.canonical).fields.replaces, []);
  const ticked = await agent.act('t', 'check', { item: 'milk', done: true });
  assert.ok(ticked.ok);
  assert.deepEqual(readAct(ticked.canonical).fields.replaces, [milk.cid]);
  const peer = remote(object, root, 'check', { item: 'milk', done: false }, '@b', 't'); store.append(peer);
  assert.deepEqual(agent.read('t').all, { eggs: [false], milk: [false, true] });
  const dropped = await agent.act('t', 'drop', { item: 'milk' });
  assert.ok(dropped.ok);
  assert.deepEqual(readAct(dropped.canonical).fields.replaces, [ticked.cid, peer.cid].sort());
  assert.deepEqual(agent.read('t').items, { eggs: false });
  const again = await agent.act('t', 'drop', { item: 'milk' });
  assert.equal(again.ok, false); assert.match((again as { reason: string }).reason, /nothing-to-delete/);
  const readd = await agent.act('t', 'check', { item: 'milk', done: false });
  assert.ok(readd.ok);
  assert.deepEqual(readAct(readd.canonical).fields.replaces, [dropped.cid]);
  const [x, y] = await Promise.all([agent.act('t', 'check', { item: 'eggs', done: true }), agent.act('t', 'check', { item: 'eggs', done: false })]);
  assert.ok(x.ok && y.ok);
  assert.match(y.canonical, new RegExp(`:replaces \\(${x.cid}\\)`)); // rapid intents serialise
});

test('every rule head folds; sums move once per address; observed removals name live additions', async () => {
  const object = await defineContract(collections);
  const { store, root } = opened(object, 't', { title: 'C' });
  const a = object.agent(host('@a', store)), b = object.agent(host('@b', store));
  for (const [agent, verb, fields] of [[a, 'credit', { amount: 2, op: '1' }], [a, 'credit', { amount: 3, op: '2' }], [b, 'credit', { amount: 7, op: '3' }], [a, 'debit', { amount: 1, op: '4' }], [a, 'add', { tag: 'one', op: '5' }], [a, 'write', { text: 'a' }]] as const) {
    assert.equal((await agent.act('t', verb, fields)).ok, true, verb);
  }
  store.append(remote(object, root, 'write', { text: 'b' }, '@b', 't'));
  const state = object.read(store.messages('t'));
  const { credits, ...rest } = state;
  assert.deepEqual(rest, { tags: ['one'], seen: ['one'], adds: 1, total: 12, balance: 11, choices: ['a', 'b'], ops: { one: '5' } });
  assert.equal(Object.keys(credits as object).length, 3);
  assert.equal((await a.act('t', 'credit', { amount: 2, op: '1' })).ok, true); // the identical act is the same act
  assert.equal(object.read(store.messages('t')).balance, 11);
  assert.equal((await a.act('t', 'credit', { amount: 1.5, op: 'x' })).ok, false);
  const removed = await a.act('t', 'remove', { tag: 'one' });
  assert.ok(removed.ok);
  assert.deepEqual(object.read(store.messages('t')).tags, []);
  assert.equal((await a.act('t', 'remove', { tag: 'none' })).ok, false);
});

test('cbcl-rs judges every received act; unknown predecessors wait', async () => {
  const object = await defineContract(checklist);
  const { store, root } = opened(object);
  const check = (kw: string, causedBy = root.cid) => actRecord(`(lang ${object.name} (check @general ${kw} :caused-by ${causedBy} :thread "demo" :from @human))`, '@human');
  const verdict = (m: Msg) => object.verdicts([...store.messages('demo'), m], 'demo').get(m.cid);
  assert.equal(verdict(check(':item "Ship" :done #t :replaces ()')), 'accepted');
  assert.equal(verdict(check(':item "Ship" :done "yes" :replaces ()')), 'rejected');
  assert.equal(verdict(check(':item "Ship" :done #t :note "x" :replaces ()')), 'rejected');
  assert.equal(verdict(check(':item "Ship" :done #t :replaces ()', 'sha256-' + 'f'.repeat(64))), 'pending');
  assert.equal(wireAddress(root.canonical), root.cid);
});
