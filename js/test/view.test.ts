// View conformance cases adapted from cbcl-bus, Apache-2.0.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { c, enumOf, defineContract, readDialect } from '../src/object/index.ts';
import { bundleText, defaultPresentation, defineView, html, importBundle, importView, validateView, VIEW_VERSION } from '../src/view/index.js';

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
  const text = bundleText(contract, view);
  assert.deepEqual(JSON.parse(text), { version: VIEW_VERSION, kind: 'bundle', contract: JSON.parse(contract.serialized), view: JSON.parse(view.serialized) });
  const bundle = await importBundle(text);
  assert.equal(bundle.object.name, contract.name);
  assert.equal(bundle.object.serialized, contract.serialized);
  assert.equal(bundle.presentation.id, view.id);
  assert.equal(bundle.presentation.serialized, view.serialized);
  const other = await defineContract({ ...plainChecklist, state: { title: c.initial('open', 'title') } });
  await assert.rejects(importBundle(bundleText(other, view)), /digest mismatch/);
  await assert.rejects(importBundle(JSON.stringify({ version: VIEW_VERSION, kind: 'view', contract: {}, view: {} })), /invalid bundle record/);
  await assert.rejects(importBundle(JSON.stringify({ version: VIEW_VERSION, kind: 'bundle', contract: JSON.parse(contract.serialized), view: JSON.parse(view.serialized), extra: 1 })), /unknown record field/);
});

// ---------- SPEC-087 REQ-008 / CON-002: the composer block (SPEC-100 increment 7)
const lunchComposer = () => ({
  label: 'Lunch poll', icon: 'bar-chart', send: 'Ask the table', order: ['options'],
  fields: { question: { placeholder: 'Where shall we eat?' } },
  then: [{ verb: 'vote' }],
});
async function lunchWith(composer) {
  const contract = await defineContract(lunchVote);
  const record = { version: VIEW_VERSION, kind: 'view', contract: contract.name, view: [{ type: 'value', field: 'question', label: 'Question' }], composer };
  return { contract, text: JSON.stringify(record) };
}

test('SPEC-087 TEST-003 · REQ-008: a lunch-vote view with a composer block imports, and its block reads back as written', async () => {
  const { contract, text } = await lunchWith(lunchComposer());
  const view = await importView(text, contract.dialect);
  assert.deepEqual(view.composer, lunchComposer(), 'the block reads back as written');
  assert.equal(view.composerDiscarded, undefined);
  assert.deepEqual(view.composerDropped, []);
  assert.equal(view.serialized, text, 'the record bytes are kept exactly');
  // defineView accepts the block too, and a bundle carries it
  const defined = await defineView({ contract, view: [{ type: 'value', field: 'question', label: 'Question' }], composer: lunchComposer() });
  assert.deepEqual(defined.composer, lunchComposer());
  const bundle = await importBundle(bundleText(contract, defined));
  assert.deepEqual(bundle.presentation.composer, lunchComposer());
  // a view without a block has none
  const plain = await defineView({ contract, view: [{ type: 'value', field: 'question', label: 'Question' }] });
  assert.equal(plain.composer, null);
});

test('SPEC-087 TEST-003 · negative input: a structural failure discards the block alone; the record still imports', async () => {
  const cases = {
    'fields key the opener lacks': { ...lunchComposer(), fields: { due: { label: 'Due' } } },
    'then verb is the opener': { ...lunchComposer(), then: [{ verb: 'propose' }] },
    'unknown key': { ...lunchComposer(), script: 'alert(1)' },
    'then with 5 entries': { ...lunchComposer(), then: Array.from({ length: 5 }, () => ({ verb: 'vote' })) },
    'order names options twice': { ...lunchComposer(), order: ['options', 'options'] },
    'order names a field the opener lacks': { ...lunchComposer(), order: ['due'] },
    'fields given as an array': { ...lunchComposer(), fields: [] },
    'then not an array': { ...lunchComposer(), then: { verb: 'vote' } },
    'a follow without verb': { ...lunchComposer(), then: [{ label: 'Vote' }] },
    'a then verb that does not exist': { ...lunchComposer(), then: [{ verb: 'nosuch' }] },
    'a core performative': { ...lunchComposer(), then: [{ verb: 'tell' }] },
    'a follow field the verb lacks': { ...lunchComposer(), then: [{ verb: 'vote', fields: { question: { label: 'Q' } } }] },
    'an unknown hint key': { ...lunchComposer(), fields: { question: { style: 'color:red' } } },
    'composer not an object': 'Lunch poll',
    'composer null': null,
  };
  for (const [why, composer] of Object.entries(cases)) {
    const { contract, text } = await lunchWith(composer);
    const view = await importView(text, contract.dialect);
    assert.equal(view.composer, null, `${why}: the whole block is discarded`);
    assert.equal(typeof view.composerDiscarded, 'string', `${why}: says why`);
    assert.equal(view.view.length, 1, `${why}: the rest of the record imports`);
  }
});

test('SPEC-087 TEST-003 · negative input: a value failure drops that value alone', async () => {
  const cases = [
    ['label', { label: 'x'.repeat(49) }, 'a 49-byte label'],
    ['label', { label: 'Lunch ‮ poll' }, 'a label holding U+202E'],
    ['label', { label: 'Lunch\npoll' }, 'a label holding a newline'],
    ['label', { label: '' }, 'an empty label'],
    ['icon', { icon: '<svg/>' }, 'icon <svg/>'],
    ['icon', { icon: 'https://x/i.png' }, 'icon URL'],
    ['icon', { icon: 'data:image/png;base64,AA' }, 'icon data URI'],
    ['tint', { tint: '#ff0000' }, 'tint #ff0000'],
    ['send', { send: 'y'.repeat(25) }, 'a 25-byte send label'],
    ['fields.question.multiline', { fields: { question: { multiline: 'yes', placeholder: 'Where?' } } }, 'multiline "yes"'],
    ['fields.question.help', { fields: { question: { help: 'h'.repeat(161), placeholder: 'Where?' } } }, 'a 161-byte help'],
    ['then.0.label', { then: [{ verb: 'vote', label: 7 }] }, 'a follow label that is not a string'],
    // SPEC-087 0.3.0: `title` names an opener `string` field; anything else is
    // a value failure, not a structural one (SPEC-100 owner decision 12)
    ['title', { title: 'due' }, 'a title naming a field the opener lacks'],
    ['title', { title: 'options' }, 'a title naming a list field'],
    ['title', { title: ['question'] }, 'a title that is not a string'],
  ];
  for (const [path, part, why] of cases) {
    const block = { ...lunchComposer(), ...part };
    const { contract, text } = await lunchWith(block);
    const view = await importView(text, contract.dialect);
    assert.ok(view.composer, `${why}: the block is kept`);
    assert.deepEqual(view.composerDropped, [path], `${why}: only ${path} is dropped`);
    const [head, ...rest] = path.split('.');
    let at = view.composer;
    for (const step of [head, ...rest].slice(0, -1)) at = at[step];
    assert.equal(Object.hasOwn(at, path.split('.').pop()), false, `${why}: the value is gone`);
    if (head !== 'label' && part.label === undefined) assert.equal(view.composer.label, 'Lunch poll', `${why}: other values apply`);
    if (head !== 'icon') assert.equal(view.composer.icon, 'bar-chart');
  }
  // every icon on the host list and every tint token passes
  for (const icon of ['box', 'layers', 'bar-chart', 'bookmark', 'pin', 'check', 'star', 'clock', 'pencil', 'activity', 'archive', 'hash', 'globe', 'link']) {
    const { contract, text } = await lunchWith({ icon });
    assert.equal((await importView(text, contract.dialect)).composer.icon, icon);
  }
  for (const tint of ['moss', 'stone', 'sage', 'olive', 'fern', 'ochre']) {
    const { contract, text } = await lunchWith({ tint });
    assert.equal((await importView(text, contract.dialect)).composer.tint, tint);
  }
  // a title naming an opener string field reads back as written
  {
    const { contract, text } = await lunchWith({ ...lunchComposer(), title: 'question' });
    const view = await importView(text, contract.dialect);
    assert.deepEqual([view.composer.title, view.composerDropped], ['question', []]);
  }
  // a 48-byte label of multi-byte characters passes; 49 bytes does not
  const { contract, text } = await lunchWith({ label: 'é'.repeat(24) });
  assert.equal((await importView(text, contract.dialect)).composer.label, 'é'.repeat(24));
});

test('SPEC-087 TEST-003 · negative output: a contract with a composer key is refused; the self-address is the same with and without any view', async () => {
  await assert.rejects(defineContract({ ...lunchVote, composer: lunchComposer() }));
  const plain = await defineContract(lunchVote);
  const defined = await defineView({ contract: plain, view: [{ type: 'value', field: 'question', label: 'Question' }], composer: lunchComposer() });
  const bundle = await importBundle(bundleText(plain, defined));
  assert.equal(bundle.object.name, plain.name, 'the dialect is the same with a composer block');
  assert.equal(bundle.object.dialect, plain.dialect);
  assert.equal(defined.contract, plain.name);
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
  assert.equal(bundleText(restored.object, restored.presentation), serialized);
});
