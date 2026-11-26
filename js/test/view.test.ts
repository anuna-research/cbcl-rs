// View conformance cases adapted from cbcl-bus, Apache-2.0.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { c, enumOf, defineContract, readDialect, makeBroker, ThreadStore, actRecord, createHostClock, makeHlc } from '../src/object/index.ts';
import { exportBundle, defaultPresentation, defineView, html, importBundle, importView, validateView, defineOperation, mountView, createRequestBroker, loadViewResources, type ViewPorts, VIEW_VERSION } from '../src/view/index.js';

const lunchVote = {
  name: 'lunch-vote', author: '@anuna',
  requirements: { maxDepth: 12, maxExpansionSize: 2048, verificationTime: 200 },
  bounds: { maxString: 280, maxList: 24 },
  verbs: {
    propose: { after: ['begin'], fields: { question: 'string', options: 'list' } },
    vote: { after: ['propose'], fields: { choice: enumOf('options'), clock: 'hlc' } },
  },
  state: {
    question: c.initial('propose', 'question'), options: c.initial('propose', 'options'),
    ballots: c.lwwPerSigner('vote', 'choice', 'clock'), tally: c.histogram('ballots'),
  },
};

/** A role-free checklist, as a chat room without a cast runs one. */
const plainChecklist = {
  name: 'agent-checklist',
  verbs: {
    open: { after: ['begin'], fields: { title: 'string' } },
    check: { after: ['open'], fields: { item: 'string', done: 'bool', clock: 'hlc' } },
    drop: { after: ['open'], fields: { item: 'string' } },
  },
  state: {
    title: c.initial('open', 'title'),
    items: c.lwwMap('check', 'item', 'done', 'clock', 'drop'),
    all: c.valuesPerKey('check', 'item', 'done', 'drop'),
    checks: c.count('check'),
    any: c.exists('check'),
  },
};

const components = [
  { type: 'text', text: 'Agent-created checklist' },
  { type: 'value', field: 'title', label: 'Project' },
  { type: 'value', field: 'items', label: 'Items' },
  { type: 'form', verb: 'check', label: 'Save item', fields: { item: 'Item', done: 'Done' } },
  { type: 'form', verb: 'drop', label: 'Remove item', fields: { item: 'Item' } },
];

test('a view is bound to the contract it is for and hashed on its own bytes', async () => {
  const contract = await defineContract(plainChecklist);
  const view = await defineView({ contract, view: components });
  assert.equal(view.contract, contract.name);
  assert.equal(view.id, 'view-' + createHash('sha256').update(view.serialized).digest('hex'));
  assert.deepEqual(JSON.parse(view.serialized), { version: VIEW_VERSION, kind: 'view', contract: contract.name, view: components });
  assert.equal(view.external, false);
  assert.match(view.body(), /<div id="object-root">/);
  assert.ok(!view.body().includes('<img'));
  const again = await importView(view.serialized, contract.dialect);
  assert.equal(again.id, view.id);
  const other = await defineContract({ ...plainChecklist, state: { title: c.initial('open', 'title') } });
  await assert.rejects(importView(view.serialized, other.dialect), /digest mismatch/);
  await assert.rejects(defineView({ contract, view: [{ type: 'value', field: 'missing', label: 'Bad' }] }), /unknown view field/);
});

test('layout metadata is optional, bounded and changes only the view digest', async () => {
  const contract = await defineContract(plainChecklist);
  const plain = await defineView({ contract, view: components });
  const layout = { width: 'wide', minHeight: 160, maxHeight: 600, aspectRatio: 16 / 9, overflow: 'scroll' };
  const sized = await defineView({ contract, view: components, layout });
  assert.notEqual(sized.id, plain.id);
  assert.deepEqual(sized.layout, layout);
  for (const invalid of [{ width: 'giant' }, { minHeight: 0 }, { maxHeight: 1201 }, { minHeight: 400, maxHeight: 200 }, { aspectRatio: 0 }, { aspectRatio: '16/9' }, { overflow: 'hidden' }, { position: 'fixed' }, null]) {
    await assert.rejects(defineView({ contract, view: components, layout: invalid }), /layout|aspect|overflow/);
  }
});

test('resource requests accept only image/style HTTPS file URLs and require custom views', async () => {
  const contract = await defineContract(plainChecklist);
  const resources = { images: ['https://assets.example/image.png'], styles: ['https://assets.example/view.css'] };
  const custom = await defineView({ contract, view: { html: '<p>custom</p>' }, resources });
  assert.deepEqual(custom.resources, resources);
  assert.equal(custom.external, true);
  assert.equal(custom.body(), '<p>custom</p>');
  for (const invalid of [{ scripts: ['https://assets.example/code.js'] }, { images: ['http://assets.example/a.png'] }, { styles: ['https://assets.example/'] }, { images: ['https://assets.example/a.png?secret=x'] }, { images: ['https://assets.example/a.png; connect-src *'] }, { images: ['https://user:pass@assets.example/a.png'] }, { images: ['https://assets.example/a.png#x'] }, { images: ['https://assets.example/a.png', 'https://assets.example/a.png'] }]) {
    await assert.rejects(defineView({ contract, view: { html: '<p>x</p>' }, resources: invalid }), /resource|Resource|HTTPS|URL/);
  }
  await assert.rejects(defineView({ contract, view: components, resources }), /custom view/);
});

test('declarative forms name declared scalar fields only; the compiler-owned :replaces is never a field', async () => {
  const contract = await defineContract(plainChecklist);
  const info = readDialect(contract.dialect);
  // The dialect declares the host clock beside the two authored fields; a form may name only the authored ones.
  assert.deepEqual(info.verbs.check.fields, { item: 'string', done: 'bool', clock: 'hlc' });
  validateView({ view: [{ type: 'form', verb: 'check', label: 'x', fields: { item: 'Item', done: 'Done' } }] }, info);
  // The host-owned HLC is never a form field: a view that could choose its timestamp could win every register.
  assert.throws(() => validateView({ view: [{ type: 'form', verb: 'check', label: 'x', fields: { item: 'Item', done: 'Done', clock: 'Clock' } }] }, info), /unknown record field/);
  assert.throws(() => validateView({ view: [{ type: 'form', verb: 'check', label: 'x', fields: { item: 'Item', done: 'Done', replaces: 'R' } }] }, info), /unknown record field/);
  assert.throws(() => validateView({ view: [{ type: 'form', verb: 'open', label: 'x', fields: { title: 'T' } }] }, info), /cannot open/);
  assert.throws(() => validateView({ view: [{ type: 'html', text: '<script>' }] }, info));
  assert.throws(() => validateView({ view: [{ type: 'text', text: 'x'.repeat(3000) }] }, info), /label/);
  const lunch = await defineContract(lunchVote);
  assert.throws(() => validateView({ view: [{ type: 'form', verb: 'propose', label: 'x', fields: { question: 'Q', options: 'O' } }] }, readDialect(lunch.dialect)), /cannot open/);
});

test('custom render views serialise the function and escape interpolations; html is a tagged template', async () => {
  const contract = await defineContract(lunchVote);
  const view = await defineView({ contract, view: (state, { emit }) => html`<h2>${state.question}</h2>` });
  assert.equal(view.external, true);
  assert.match(view.body(), /const html=/);
  assert.match(view.body(), /window\.onProjection/);
  assert.ok(!view.body().includes('</script>const'));
  await assert.rejects(defineView({ contract, view: { render: 'x'.repeat(60001) } }), /source/);
  await assert.rejects(defineView({ contract, view: { html: 7 } }), /source/);
  assert.deepEqual(html`a${1}b`, { strings: ['a', 'b'], values: [1] });
});

test('default presentation exposes every state field read-only', async () => {
  const contract = await defineContract(plainChecklist);
  const preset = await defaultPresentation(contract.dialect);
  assert.deepEqual(preset.view.map(v => v.field), Object.keys(contract.info.state));
  assert.ok(preset.view.every(v => v.type === 'value'));
});

test('a bundle carries a contract and its view in one record and imports to both, bound', async () => {
  const contract = await defineContract(plainChecklist);
  const view = await defineView({ contract, view: components });
  const text = exportBundle(view);
  const raw = await importView(view.serialized, contract.dialect);
  assert.throws(() => exportBundle(raw), /needs the cbcl\/object contract/);
  assert.equal(exportBundle(contract, raw), text);
  assert.equal(exportBundle(await importView(view.serialized, contract)), text);
  assert.equal(JSON.parse(exportBundle(await defaultPresentation(contract))).contract.name, contract.label);
  assert.deepEqual(JSON.parse(text), { version: VIEW_VERSION, kind: 'bundle', contract: JSON.parse(contract.serialized), view: JSON.parse(view.serialized) });
  const bundle = await importBundle(text);
  assert.equal(bundle.object.name, contract.name);
  assert.equal(bundle.object.serialized, contract.serialized);
  assert.equal(bundle.presentation.id, view.id);
  assert.equal(bundle.presentation.serialized, view.serialized);
  const other = await defineContract({ ...plainChecklist, state: { title: c.initial('open', 'title') } });
  assert.throws(() => exportBundle(other, raw), /digest mismatch/);
  await assert.rejects(importBundle(JSON.stringify({ version: VIEW_VERSION, kind: 'view', contract: {}, view: {} })), /invalid bundle record/);
  await assert.rejects(importBundle(JSON.stringify({ version: VIEW_VERSION, kind: 'bundle', contract: JSON.parse(contract.serialized), view: JSON.parse(view.serialized), extra: 1 })), /unknown record field/);
});

test('custom view capability declarations survive import and require explicit valid operations', async () => {
  const contract = await defineContract(plainChecklist);
  const view = { html: '<p>Preview</p>' };
  const request = { id: 'weather', url: 'https://example.org/weather', response: 'json' as const, parameters: ['city'] };
  const capabilities = { requests: [request], sound: true, media: { accept: ['image' as const] } };
  const presentation = await defineView({ contract, view, capabilities });
  assert.deepEqual((await importView(presentation.serialized, contract)).capabilities, capabilities);
  await assert.rejects(defineView({ contract, view: components, capabilities }), /custom view/);
  await assert.rejects(defineView({ contract, view, capabilities: { requests: [request, request] } }), /operation id/);
});

test('a version 3 cbcl-bus bundle keeps its original contract and view identities', async () => {
  // Generated with cbcl-bus 43c13eb7. Property order contributes to the view ID.
  const contract = { version: 3, kind: 'contract', name: 'labels',
    verbs: { open: { after: ['begin'], fields: { name: 'string' } } }, state: { name: ['initial', 'open', 'name'] } };
  const view = { version: 3, kind: 'view', contract: 'f12209f0597c91cb667fb6d20d542c2c0218e033912c05075eaf8ddb5847a0d8b45d4',
    view: [{ type: 'value', label: 'Name', field: 'name' }], composer: { title: 'name' } };
  const serialized = JSON.stringify({ version: 3, kind: 'bundle', contract, view });
  const restored = await importBundle(serialized);
  assert.equal(restored.object.name, view.contract);
  assert.equal(restored.presentation.id, 'view-e77027f43096989bf78f77dabf7f99ff1bcbd3fcb33a167a146d4dc4e42804ac');
  assert.equal(exportBundle(restored.presentation), serialized);
  assert.equal('composer' in restored.presentation, false);
  await assert.rejects(defineView({ contract: restored.object, view: view.view, composer: {} }), /unknown record field/);
});

test('a view emits into the existing object broker with the host thread, clock and signer', async () => {
  const object = await defineContract(lunchVote);
  const presentation = await defaultPresentation(object);
  const thread = 'lunch';
  const store = new ThreadStore();
  store.append(actRecord(object.open({ room: '@room', thread, from: '@alice',
    fields: { question: 'Lunch?', options: ['Soup'] } }), '@alice'));
  const sent: string[] = [];
  const broker = makeBroker({ getRuntime: name => name === object.name ? object.runtime : null,
    store, me: () => '@bob', send: text => { sent.push(text); } });
  const emit = presentation.bindIntent(thread, broker, () => makeHlc({ nowMs: 1 }));
  assert.equal((await emit('propose')).ok, false);
  assert.equal((await emit('vote', { choice: 'Soup', thread: 'other' })).ok, false);
  assert.equal((await emit('vote', { choice: 'Soup', clock: makeHlc() })).ok, false);
  assert.equal((await emit('vote', { choice: 'Pizza' })).ok, false);
  const fields = { choice: 'Soup' };
  const result = emit('vote', fields);
  fields.choice = 'Pizza';
  assert.equal((await result).ok, true);
  assert.equal(sent.length, 1);
  assert.deepEqual(object.read(store.messages(thread)).tally, { Soup: 1 });
});

test('replacing a binding revokes preparing and queued intents while preserving the shared queue', async () => {
  const object = await defineContract(lunchVote);
  const view = await defaultPresentation(object);
  const thread = 'lunch';
  const store = new ThreadStore();
  store.append(actRecord(object.open({ room: '@room', thread, from: '@alice',
    fields: { question: 'Lunch?', options: ['Soup'] } }), '@alice'));
  const started = Promise.withResolvers<void>();
  const resume = Promise.withResolvers<void>();
  let prepared = 0;
  let sent = 0;
  const broker = makeBroker({ getRuntime: () => object.runtime, store, me: () => '@bob',
    async prepare(text) {
      prepared++;
      started.resolve();
      await resume.promise;
      return text;
    },
    send() { sent++; },
  });
  const controller = new AbortController();
  const nextClock = () => makeHlc({ nowMs: 1 });
  const emit = view.bindIntent(thread, broker, { signal: controller.signal, nextClock });
  const fields = { choice: 'Soup' };
  const pending = Array.from({ length: 8 }, () => emit('vote', fields));
  await started.promise;
  assert.deepEqual(await emit('vote', fields), { ok: false, reason: 'Too many pending intents' });
  controller.abort();
  const revoked = { ok: false, reason: 'Intent binding revoked' };
  assert.deepEqual(await emit('vote', fields), revoked);
  const replacement = view.bindIntent(thread, broker, { nextClock })('vote', fields);
  await Promise.resolve();
  assert.equal(prepared, 1);
  resume.resolve();
  for (const result of await Promise.all(pending)) assert.deepEqual(result, revoked);
  assert.equal((await replacement).ok, true);
  assert.equal(prepared, 2);
  assert.equal(sent, 1);
});

test('a mounted executor observes peer and local folds, grants and host cancellation', async () => {
  const object = await defineContract(lunchVote);
  const store = new ThreadStore();
  const thread = 'room-lunch';
  const open = actRecord(object.open({ thread, room: '@room', from: '@alice',
    fields: { question: 'Lunch?', options: ['Soup'] } }), '@alice');
  store.append(open);
  const presentation = await defineView({ contract: object, view: { html: '<p>Lunch</p>' },
    capabilities: { operations: ['clipboard.writeText', 'host.info', 'location.read'] } });
  const parent = new AbortController();
  const signals: (AbortSignal | undefined)[] = [];
  let persisted: string | null = null;
  const persistence = { now: () => 1, load: () => persisted, save: (value: string) => { persisted = value; } };
  const clock = createHostClock(persistence);
  const broker = makeBroker({ store, me: () => '@bob', getRuntime: () => object.runtime, clock,
    prepare(text, signal) { signals.push(signal); return text; }, send(_text, signal) { signals.push(signal); } });
  let ports!: ViewPorts;
  let disposed = 0;
  const tallies: unknown[] = [];
  const delayed = Promise.withResolvers<string>();
  const dispose = await mountView(presentation, { object, thread, store, broker, signal: parent.signal,
    grants: { operations: {
      'clipboard.writeText': (input, scope) => {
        assert.equal(scope.contract, object.name);
        assert.equal(scope.view, presentation.id);
        assert.equal(scope.thread, thread);
        if (typeof input !== 'string') throw Error('Expected text');
        return delayed.promise;
      },
      'host.info': input => input,
    } }, onError: assert.fail,
    executor: { mount(input) {
      ports = input.ports;
      return { project: state => tallies.push(state.tally), dispose: () => { disposed++; } };
    } } });
  assert.equal(tallies.length, 1);
  const info = { version: 1 };
  const result = ports.invoke('host.info', info);
  assert.deepEqual(result, info);
  assert.notEqual(result, info);
  assert.throws(() => ports.invoke('clipboard.writeText', 42), /Expected text/);
  assert.throws(() => ports.invoke('location.read'), /denied/);
  assert.throws(() => ports.invoke('toString'), /denied/);
  assert.throws(() => ports.invoke('host.info', new Date() as never), /record/);
  const pendingCall = ports.invoke('clipboard.writeText', 'hello');
  const remote = makeHlc({ nowMs: 5000 });
  const vote = object.runtime.intend(thread, [open], '@alice', 'vote', { choice: 'Soup', clock: remote });
  assert.ok(vote.ok);
  store.append(actRecord(vote.canonical, '@alice'));
  await Promise.resolve();
  assert.deepEqual(tallies.at(-1), { Soup: 1 });
  const local = await ports.emit('vote', { choice: 'Soup' });
  assert.ok(local.ok);
  assert.equal(actRecord(local.canonical, '@bob').kw.clock, makeHlc({ received: remote, nowMs: 1 }));
  const beforeRestart = persisted!;
  assert.equal(createHostClock(persistence).next(), makeHlc({ previous: beforeRestart, nowMs: 1 }));
  assert.deepEqual(tallies.at(-1), { Soup: 2 });
  assert.equal(signals.length, 2);
  assert.ok(signals[0] && signals[0] === signals[1]);
  parent.abort();
  dispose();
  assert.equal(disposed, 1);
  assert.ok(signals[0].aborted);
  assert.equal((await ports.emit('vote', { choice: 'Soup' })).ok, false);
  delayed.resolve('copied');
  await assert.rejects(Promise.resolve(pendingCall), { name: 'AbortError' });
  assert.throws(() => ports.invoke('host.info'), { name: 'AbortError' });
});

test('only declared and granted requests and resources reach the fetch adapter', async () => {
  const url = 'https://example.org/weather';
  const manifest = { requests: [{ id: 'weather', url, response: 'json' as const, parameters: ['city'] }] };
  const calls: string[] = [];
  const fetcher = async (input: RequestInfo | URL) => {
    calls.push(String(input));
    return Response.json({ ok: true });
  };
  assert.throws(() => createRequestBroker(manifest, ['other']), /grant/);
  const broker = createRequestBroker(manifest, ['weather'], { fetch: fetcher });
  await assert.rejects(broker.request('other'), /denied/);
  await assert.rejects(broker.request('weather', { path: 'here' }), /invalid/);
  assert.deepEqual(await broker.request('weather', { city: 'A B' }), { ok: true });
  broker.destroy();
  await assert.rejects(broker.request('weather'), /revoked/);
  const signal = new AbortController().signal;
  await assert.rejects(loadViewResources({}, { styles: [url] }, signal, fetcher), /grant/);
  assert.deepEqual(calls, [url + '?city=A+B']);
  const css = { styles: [url] };
  const loaded = await loadViewResources(css, css, signal, async () =>
    new Response('p { color: green }', { headers: { 'Content-Type': 'text/css' } }));
  assert.deepEqual(loaded.styles, ['p { color: green }']);
});

test('aborting during executor startup revokes ports and disposes the late execution', async () => {
  const object = await defineContract(plainChecklist);
  const presentation = await defaultPresentation(object);
  const parent = new AbortController();
  const started = Promise.withResolvers<ViewPorts>();
  const resume = Promise.withResolvers<void>();
  let disposed = 0;
  const pending = mountView(presentation, { object, thread: 't', store: new ThreadStore(),
    broker: { applyIntent: assert.fail }, signal: parent.signal, onError: assert.fail,
    executor: { async mount({ ports }) {
      started.resolve(ports);
      await resume.promise;
      return { project: assert.fail, dispose: () => { disposed++; } };
    } } });
  const ports = await started.promise;
  assert.throws(() => ports.invoke('clipboard.writeText'), /denied/);
  parent.abort();
  await assert.rejects(ports.request('weather'), /revoked/);
  assert.equal((await ports.emit('vote')).ok, false);
  resume.resolve();
  await assert.rejects(pending, { name: 'AbortError' });
  assert.equal(disposed, 1);
});

test('browser grants must match the operations in the verified view record', async () => {
  const object = await defineContract(plainChecklist);
  const spec = { contract: object, view: { html: '<p>Copy</p>' } };
  await assert.rejects(defineView({ ...spec, capabilities: { operations: ['clipboard.read', 'clipboard.read'] } }), /operation name/);
  const view = await defineView({ ...spec, capabilities: { operations: ['clipboard.writeText'] } });
  const restored = await importView(view.serialized, object);
  assert.equal(restored.id, view.id);
  // Mutating the presentation's convenience metadata cannot expand its declaration.
  assert.throws(() => restored.capabilities!.operations!.push('clipboard.read'), TypeError);
  await assert.rejects(mountView(restored, {
    object, thread: 't', store: new ThreadStore(), broker: { applyIntent: assert.fail }, onError: assert.fail,
    grants: { operations: { 'clipboard.read': assert.fail } }, executor: { mount: assert.fail },
  }), /Invalid capability grant/);
});

test('mount quotas narrow declarations and host grants independently for each view instance', async () => {
  const object = await defineContract(plainChecklist);
  const view = await defineView({ contract: object, view: { html: '<p>Pick</p>' }, capabilities: { operations: [
    { id: 'pick', limits: { maxCalls: 2, maxInputBytes: 12, maxResultBytes: 4 } },
  ] } });
  assert.throws(() => { (view.view as {html: string}).html = ''; }, TypeError);
  const handles: string[] = [];
  const closed: string[] = [];
  const pending = Promise.withResolvers<string>();
  const grant = defineOperation({
    limits: { maxCalls: 3, maxConcurrent: 1, maxInputBytes: 4 },
    parse(value) {
      if (typeof value !== 'string') throw Error('Expected string');
      return value;
    },
    run(value, scope) {
      handles.push(scope.thread);
      if (value === 'x') return pending.promise.then(result => {
        scope.onDispose(() => closed.push(scope.thread));
        return result;
      });
      scope.onDispose(() => closed.push(scope.thread));
      return 'large';
    },
  });
  const ports = new Map<string, ViewPorts>();
  const mount = (thread: string, presentation = view) => mountView(presentation, { object, thread, store: new ThreadStore(),
    broker: { applyIntent: assert.fail }, grants: { operations: { pick: grant } }, onError: assert.fail,
    executor: { mount({ ports: mounted }) {
      ports.set(thread, mounted);
      return { project() {}, dispose() {} };
    } } });
  await assert.rejects(mount('forged', { ...view }), /verified presentation/);
  const stopA = await mount('a'), stopB = await mount('b');
  const a = ports.get('a')!, b = ports.get('b')!;
  assert.throws(() => a.invoke('pick', '猫'), /byte limit/);
  const result = a.invoke('pick', 'x');
  assert.throws(() => a.invoke('pick', 'x'), /call limit/);
  assert.throws(() => b.invoke('pick', 'b'), /byte limit/);
  assert.throws(() => b.invoke('pick', 0), /Expected string/);
  assert.throws(() => b.invoke('pick', 'b'), /call limit/);
  assert.deepEqual(handles, ['a', 'b']);
  stopA();
  pending.resolve('ok');
  await assert.rejects(Promise.resolve(result), { name: 'AbortError' });
  assert.deepEqual(closed, ['a']);
  stopB();
  assert.deepEqual(closed, ['a', 'b']);
});
