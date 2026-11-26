import test from 'node:test';
import assert from 'node:assert/strict';
import { defineContract, importObject, makeBroker, c, t, enumOf, literal, readActExact, readAct, actRecord, isSDKDialect, keywordText, ThreadStore, type CbclObject, type Msg } from '../src/object/index.ts';
import { verifyDialect, dialectHash, wireAddress } from '../src/index.ts';

const checklist = {
  name: 'agent-checklist',
  verbs: {
    open: { after: ['begin'], fields: { title: 'string' } },
    check: { after: ['open'], fields: { item: 'string', done: 'bool', clock: "hlc" } },
    drop: { after: ['open'], fields: { item: 'string' } },
  },
  state: { title: c.initial('open', 'title'), items: c.lwwMap('check',  'item',  'done', 'clock',  'drop'), all: c.valuesPerKey('check', 'item', 'done', 'drop'), checks: c.count('check'), any: c.exists('check') },
};
const lunchVote = {
  name: 'lunch-vote', author: '@anuna',
  requirements: { maxDepth: 12, maxExpansionSize: 2048, verificationTime: 200 },
  bounds: { maxString: 280, maxList: 24 },
  verbs: { propose: { after: ['begin'], fields: { question: 'string', options: 'list' as const } }, vote: { after: ['propose'], fields: { choice: enumOf('options'), clock: "hlc" } } },
  state: { question: c.initial('propose', 'question'), options: c.initial('propose', 'options'), ballots: c.lwwPerSigner('vote', 'choice', 'clock'), tally: c.histogram('ballots') },
};
const collections = {
  name: 'collections',
  verbs: {
    open: { after: ['begin'], fields: { title: 'string' } }, add: { after: ['open'], fields: { tag: 'string', op: 'string', clock: "hlc" } }, remove: { after: ['open'], fields: { tag: 'string' } },
    credit: { after: ['open'], fields: { amount: 'integer' as const, op: 'string' } }, debit: { after: ['open'], fields: { amount: 'integer' as const, op: 'string' } }, write: { after: ['open'], fields: { text: 'string' } },
  },
  state: { tags: c.observedSet('add', 'remove', 'tag'), seen: c.setUnion('add', 'tag'), adds: c.count('add'), credits: c.events('credit', 'amount'), total: c.sum('credits'), balance: c.counter('credit', 'debit', 'amount'), choices: c.values('write', 'text'), ops: c.lwwMap('add', 'tag', 'op', 'clock') },
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
  actRecord(`(lang ${object.name} (${verb} @general ${keywordText(((["check", "vote", "add"].includes(verb)) ? { ...kw, clock: "hlc-0000000000000000-00000000" } : kw) as never)} :replaces () :caused-by ${root.cid} :thread ${JSON.stringify(thread)} :from ${signer}))`, signer);

test('a contract compiles to a self-addressed dialect the verifier accepts', async () => {
  const object = await defineContract(checklist);
  assert.ok(isSDKDialect(object.name));
  assert.equal(object.label, 'agent-checklist');
  assert.equal(dialectHash(object.dialect), object.name);
  assert.doesNotThrow(() => verifyDialect(object.dialect));
  assert.equal((await importObject(object.serialized)).name, object.name);
  assert.equal(object.info.opener, 'open');
  assert.deepEqual(Object.keys(object.info.verbs.check.fields), ['clock', 'done', 'item']);
  await assert.rejects(defineContract({ ...checklist, verbs: { ...checklist.verbs, check: { ...checklist.verbs.check, after: ['open', 'check'] } } }), /R5/);
  await assert.rejects(defineContract({ ...checklist, view: [] } as never), /host package/);
  for (const field of ['from', 'replaces', 'key']) {
    const spec = structuredClone(checklist) as never as typeof checklist;
    (spec.verbs.check.fields as Record<string, string>)[field] = 'string';
    await assert.rejects(defineContract(spec), /invalid field name/);
  }
});

test('named and inline type expressions survive object authoring and constrain the opener', async () => {
  const types = { price: '(decimal (>= 0))', label: '(or (one-of "free") (string (matches "[A-Z]+")))' };
  const definition = {
    name: 'prices', types,
    verbs: { open: { after: ['begin'], fields: { amount: 'price', label: 'label', qty: '(integer (> 0))' } } },
    state: { amount: c.initial('open', 'amount') },
  };
  const object = await defineContract(definition);
  assert.deepEqual(JSON.parse(object.serialized).types, types);
  assert.deepEqual(object.info.types.price.representations, ['decimal']);
  assert.equal((await importObject(object.serialized)).dialect, object.dialect);
  const args = { room: '@r', thread: 't', from: '@a' };
  const fields = { amount: { decimal: '1.25' }, label: 'free', qty: 1 };
  assert.doesNotThrow(() => object.open({ ...args, fields }));
  for (const invalid of [{ amount: { decimal: '-1' } }, { label: 'other' }, { qty: 0 }]) {
    assert.throws(() => object.open({ ...args, fields: { ...fields, ...invalid } }), /invalid opener fields/);
  }
  await assert.rejects(defineContract({ ...definition, types: { ...types, price: 'missing-type' } }));
});

test('JS type builders compile to the same dialect as CBCL source expressions', async () => {
  const types = {
    price: t.decimal({ gte: 0 }),
    label: t.or(t.oneOf('free', 'a"b'), t.string({ matches: '[A-Z]+' })),
    quantity: t.and(t.integer({ gt: 0n }), t.number({ lte: { decimal: '100.25' } })),
    options: t.list({ length: { gte: 1, lt: 4 } }),
  };
  const source = {
    price: '(decimal (>= 0))',
    label: '(or (one-of "free" "a\\"b") (string (matches "[A-Z]+")))',
    quantity: '(and (integer (> 0)) (number (<= 100.25m)))',
    options: '(list (length (>= 1) (< 4)))',
  };
  assert.deepEqual(types, source);
  const definition = { ...checklist, types };
  assert.equal((await defineContract(definition)).name, (await defineContract({ ...definition, types: source })).name);
  assert.equal(t.oneOf({ keyword: 'red' }, { symbol: 'blue' }, { float: 2 }, true), '(one-of :red blue 2.0 #t)');
});

test('ordered refinements and every scalar representation survive open, bind, and exact read-back', async () => {
  const fields = {
    tag: t.oneOf({ keyword: '2fa' }), who: t.oneOf({ symbol: '@team/red' }),
    size: t.integer([['>=', -(1n << 63n)], ['<=', (1n << 63n) - 1n]]),
    ratio: t.float([['>=', { float: 2 }], ['>=', 1]]),
    note: t.string([['matches', 'a.*'], ['length', ['>=', 1]], ['matches', '.*b']]),
    items: t.list([['length', ['>=', 1]], ['length', ['<=', 10]]]),
  };
  assert.equal(fields.ratio, '(float (>= 2.0) (>= 1))');
  assert.equal(fields.note, '(string (matches "a.*") (length (>= 1)) (matches ".*b"))');
  const object = await defineContract({ name: 'atoms',
    verbs: { open: { after: ['begin'], fields }, update: { after: ['open'], fields } },
    state: { updates: c.count('update') },
  });
  const values = {
    tag: { keyword: '2fa' }, who: { symbol: '@team/red' }, size: (1n << 63n) - 1n,
    ratio: { float: 2 }, note: 'ab', items: [[{ symbol: '?' }, ':tag', { decimal: '1.25' }, false, -(1n << 63n)]],
  };
  const root = object.open({ room: '@general', thread: 't', from: '@a', fields: values });
  const exact = readActExact(root).fields;
  assert.deepEqual(exact, { ...values, size: { integer: String(values.size) },
    items: [[{ symbol: '?' }, ':tag', { decimal: '1.25' }, false, { integer: '-9223372036854775808' }]] });
  const h = host('@a');
  h.store.append(actRecord(root, '@a'));
  const result = await object.agent(h).act('t', 'update', exact);
  assert.ok(result.ok, JSON.stringify(result));
  assert.deepEqual(readActExact(result.canonical).fields, exact);
  assert.throws(() => literal(1n << 63n));
  assert.throws(() => literal({ symbol: '-12' }));
  assert.throws(() => literal({ keyword: 'x) (tell' }));
  assert.throws(() => literal({ float: Infinity }));
});

test('the opener is verified; the fold is order-independent and duplicate-insensitive', async () => {
  const object = await defineContract(checklist);
  const { store, root } = opened(object);
  assert.match(root.canonical, new RegExp(`^\\(lang ${object.name} \\(open @general :title "Launch" :caused-by begin :thread "demo" :from @agent\\)\\)$`));
  assert.throws(() => object.open({ room: '@general', thread: 't', from: '@a', fields: { title: 7 } }), /invalid opener fields/);
  assert.throws(() => object.open({ room: '@general', thread: 't', from: '@a', fields: {} }), /exactly title/);
  const agent = object.agent(host('@human', store));
  assert.equal((await agent.act('demo', 'check', { item: 'Ship', done: true , clock: 'hlc-0000000000000000-00000000'})).ok, true);
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
    assert.equal((await agent.act('demo', 'check', { item: 'x', done: true, ...forged , clock: 'hlc-0000000000000000-00000000'})).ok, false, JSON.stringify(forged));
  }
  assert.equal((await agent.act('demo', 'check', { item: 'x', done: true, from: '@agent' , clock: 'hlc-0000000000000000-00000000'})).ok, true); // an echoed binding is stripped
  assert.equal(h.sent.length, 1);
  assert.deepEqual(agent.maySend('demo'), ['check', 'drop']);
});

test('domains: the binder refuses an out-of-opener choice; a received one contributes nothing', async () => {
  const object = await defineContract(lunchVote);
  const { store, root } = opened(object, 'v1', { question: 'Lunch?', options: ['yes', 'no'] });
  const h = host('@agent', store);
  const agent = object.agent(h);
  const outside = await agent.act('v1', 'vote', { choice: 'outside' , clock: 'hlc-0000000000000000-00000000'});
  assert.equal(outside.ok, false); assert.match((outside as { reason: string }).reason, /domain/); assert.equal(h.sent.length, 0);
  assert.equal((await agent.act('v1', 'vote', { choice: 'yes' , clock: 'hlc-0000000000000000-00000000'})).ok, true);
  const stray = actRecord(`(lang ${object.name} (vote @general :choice "elsewhere" :clock "hlc-0000000000000000-00000000" :replaces () :caused-by ${root.cid} :thread "v1" :from @stranger))`, '@stranger');
  store.append(stray);
  assert.equal(object.verdicts(store.messages('v1'), 'v1').get(stray.cid), 'accepted');
  assert.deepEqual(agent.read('v1').tally, { yes: 1 });
  assert.equal((await agent.act('v1', 'vote', { choice: '😀'.repeat(80) , clock: 'hlc-0000000000000000-00000000'})).ok, false); // max-string 280
});

test('registers: replacements bind to the intent key, a peer write is concurrent, delete names current writes', async () => {
  const object = await defineContract(checklist);
  const { store, root } = opened(object, 't');
  const agent = object.agent(host('@a', store));
  const milk = await agent.act('t', 'check', { item: 'milk', done: false , clock: 'hlc-0000000000000000-00000000'});
  const eggs = await agent.act('t', 'check', { item: 'eggs', done: false , clock: 'hlc-0000000000000000-00000000'});
  assert.ok(milk.ok && eggs.ok);
  assert.deepEqual(readAct(eggs.canonical).fields.replaces, []);
  const ticked = await agent.act('t', 'check', { item: 'milk', done: true , clock: 'hlc-0000000000000000-00000000'});
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
  const readd = await agent.act('t', 'check', { item: 'milk', done: false , clock: 'hlc-0000000000000000-00000000'});
  assert.ok(readd.ok);
  assert.deepEqual(readAct(readd.canonical).fields.replaces, [dropped.cid]);
  const [x, y] = await Promise.all([agent.act('t', 'check', { item: 'eggs', done: true , clock: 'hlc-0000000000000000-00000000'}), agent.act('t', 'check', { item: 'eggs', done: false , clock: 'hlc-0000000000000000-00000000'})]);
  assert.ok(x.ok && y.ok);
  assert.match(y.canonical, new RegExp(`:replaces \\(${x.cid}\\)`)); // rapid intents serialise
});

test('every rule head folds; sums move once per address; observed removals name live additions', async () => {
  const object = await defineContract(collections);
  const { store, root } = opened(object, 't', { title: 'C' });
  const a = object.agent(host('@a', store)), b = object.agent(host('@b', store));
  for (const [agent, verb, fields] of [[a, 'credit', { amount: 2, op: '1' }], [a, 'credit', { amount: 3, op: '2' }], [b, 'credit', { amount: 7, op: '3' }], [a, 'debit', { amount: 1, op: '4' }], [a, 'add', { tag: 'one', op: '5', clock: 'hlc-0000000000000000-00000000' }], [a, 'write', { text: 'a' }]] as const) {
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
  const check = (kw: string, causedBy = root.cid) => actRecord(`(lang ${object.name} (check @general ${kw} :clock "hlc-0000000000000000-00000000" :caused-by ${causedBy} :thread "demo" :from @human))`, '@human');
  const verdict = (m: Msg) => object.verdicts([...store.messages('demo'), m], 'demo').get(m.cid);
  assert.equal(verdict(check(':item "Ship" :done #t :replaces ()')), 'accepted');
  assert.equal(verdict(check(':item "Ship" :done "yes" :replaces ()')), 'rejected');
  assert.equal(verdict(check(':item "Ship" :done #t :note "x" :replaces ()')), 'rejected');
  assert.equal(verdict(check(':item "Ship" :done #t :replaces ()', 'f1220' + 'f'.repeat(64))), 'pending');
  assert.equal(wireAddress(root.canonical), root.cid);
});


// SPEC-019 TEST-1951/1952: binder and fold agree on signer replacement.
test('lwwPerSigner edits replace observed own votes and preserve other signers', async () => {
  const object = await defineContract(lunchVote);
  const { store, root } = opened(object, 'v1', { question: 'Lunch?', options: ['yes', 'no', 'maybe'] });
  const a = object.agent(host('@a', store));
  const b = object.agent(host('@b', store));
  const first = await a.act('v1', 'vote', { choice: 'yes' , clock: 'hlc-0000000000000000-00000000'});
  const peer = await b.act('v1', 'vote', { choice: 'yes' , clock: 'hlc-0000000000000000-00000000'});
  assert.ok(first.ok && peer.ok);
  assert.deepEqual(readAct(peer.canonical).fields.replaces, []);
  const second = await a.act('v1', 'vote', { choice: 'no' , clock: 'hlc-0000000000000000-00000000'});
  assert.ok(second.ok);
  assert.deepEqual(readAct(second.canonical).fields.replaces, [first.cid]);
  assert.deepEqual(a.read('v1').ballots, { '@a': 'no', '@b': 'yes' });
  const hostile = actRecord(`(lang ${object.name} (vote @general :choice "no" :clock "hlc-0000000000000000-00000000" :replaces (${peer.cid}) :caused-by ${root.cid} :thread "v1" :from @c))`, '@c');
  store.append(hostile);
  assert.deepEqual(a.read('v1').ballots, { '@a': 'no', '@b': 'yes', '@c': 'no' });
  const concurrent = remote(object, root, 'vote', { choice: 'maybe' }, '@a', 'v1');
  store.append(concurrent);
  const merged = await a.act('v1', 'vote', { choice: 'no' , clock: 'hlc-0000000000000000-00000000'});
  assert.ok(merged.ok);
  assert.deepEqual(readAct(merged.canonical).fields.replaces, [second.cid, concurrent.cid].sort());
  const messages = store.messages('v1');
  assert.deepEqual(object.read(messages.slice().reverse()), object.read(messages));
  assert.deepEqual(object.read([...messages, ...messages]), object.read(messages));
});

test('admission rechecks snapshots from earlier and independent histories', async () => {
  const object = await defineContract(checklist);
  const { store, root } = opened(object);
  const act = remote(object, root, 'check', { item: 'venue', done: true }, '@bo');
  // A captured store snapshot must keep its original verdict even if re-read later.
  const peer = new ThreadStore();
  peer.append(act);
  const before = peer.messages('demo');
  peer.append(root);
  store.append(act);
  const verdict = (records: Msg[]) => object.runtime.verdicts('demo', records).get(act.cid);
  assert.equal(verdict(store.messages('demo')), 'accepted');
  assert.equal(verdict(peer.messages('demo')), 'accepted');
  assert.equal(verdict(before), 'pending');
  assert.equal(verdict([act]), 'pending');
  assert.equal(verdict(store.messages('demo')), 'accepted');
});

test('delivery results survive local recording and observer failures', async () => {
  const object = await defineContract(checklist);
  const { store } = opened(object);
  let sends = 0;
  const fail = () => { throw Error('local failure'); };
  const host = { store, me: () => '@b', getRuntime: () => object.runtime,
    send() { sends++; }, onState: fail, report: fail };
  const act = (broker: ReturnType<typeof makeBroker>) => broker.applyIntent('demo', object.name, 'check', { item: 'venue', done: true, clock: 'hlc-0000000000000000-00000000' });
  assert.ok((await act(makeBroker(host))).ok);
  const delivered = await act(makeBroker({ ...host, store: { messages: id => store.messages(id), append: fail } }));
  assert.ok(delivered.ok);
  assert.equal(delivered.recordError, 'local failure');
  assert.equal(delivered.cid, actRecord(delivered.canonical, '@b').cid);
  assert.equal((await act(makeBroker({ ...host, prepare: () => '(' }))).ok, false);
  assert.equal(sends, 2);
  const uncertain = await act(makeBroker({ ...host, send: fail }));
  assert.ok(!uncertain.ok && uncertain.delivery === 'unknown');
  assert.equal(uncertain.cid, actRecord(uncertain.canonical, '@b').cid);
  assert.equal(uncertain.reason, 'local failure');
  assert.ok((await act(makeBroker({ ...host, onState: async () => fail(), report: async () => fail() }))).ok);
});
