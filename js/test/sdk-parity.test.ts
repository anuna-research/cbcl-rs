import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { readAct, openCheckpoint, encodeMultikey, inspectMultikey, multikeyIdentity, publicKeyCodecs } from '../src/index.ts';
import { actRecord, c, createRuntime, defineContract, optional, stateEntry } from '../src/object/index.ts';

async function vector(path: string) {
  return JSON.parse(await readFile(new URL('../../test-vectors/' + path, import.meta.url), 'utf8'));
}

test('typed object shapes permit omitted fields and validate nested values and defaults', async () => {
  const fields = { details: { type: 'list', children: { title: 'string', shade: optional('string') } }, shade: optional('string', 'blue') };
  const definition = { name: 'nested', verbs: { open: { after: ['begin'], fields }, paint: { after: ['open'], fields } },
    state: { paints: c.count('paint') } };
  const object = await defineContract(definition);
  const args = { room: '@r', thread: 't', from: '@a' };
  const data = { details: [{ keyword: 'title' }, 'test'] };
  const root = actRecord(object.open({ ...args, fields: data }), '@a');
  assert.deepEqual(object.info.verbs.open.contracts.details.children.map(rule => 'keyword' in rule && rule.keyword).sort(), ['shade', 'title']);
  assert.equal(object.info.verbs.open.contracts.shade.default, '"blue"');
  assert.equal(object.runtime.intend('t', [root], '@a', 'paint', data).ok, true);
  assert.throws(() => object.open({ ...args, fields: { details: [{ keyword: 'title' }, 3] } }));
  await assert.rejects(defineContract({ ...definition, verbs: { ...definition.verbs,
    open: { after: ['begin'], fields: { shade: optional('string', 2) } } } }));
});

test('native ordered state entries compile and expose threshold, freeze and lattice metadata', async () => {
  const object = await defineContract({ name: 'stages', roles: { owner: 'singleton' },
    verbs: { open: { after: ['begin'], from: 'owner', to: ['owner'] },
      mark: { after: ['open'], fields: { phase: 'string' }, from: 'owner', to: ['owner'] },
      close: { after: ['open'], from: 'owner', to: ['owner'] } },
    stateEntries: [
      stateEntry('lattice', 'rank', ['elements', 'lo', 'hi'], ['bottom', 'lo'], ['top', 'hi'],
        ['join', ['lo', 'lo', 'lo'], ['lo', 'hi', 'hi'], ['hi', 'lo', 'hi'], ['hi', 'hi', 'hi']]),
      stateEntry('phase', ['lift', 'mark', ['into', 'rank'], ['contribute', [':phase', { str: 'hi' }, 'hi']]]),
      stateEntry('threshold', 'ready', 'phase', { str: 'lo' }),
      stateEntry('freeze', 'phase', 'close', 'fault'),
    ] });
  assert.equal(object.info.lattices.length, 1);
  assert.deepEqual(object.info.thresholds, [{ name: 'ready', field: 'phase', elements: ['lo'] }]);
  assert.equal(object.info.freezes[0].verb, 'close');
  assert.equal(object.info.state.phase[0], 'lift');
});

test('public Multikey codecs round-trip bytes and restrict identity conversion to Ed25519', () => {
  for (const codec of Object.values(publicKeyCodecs)) {
    const bytes = new Uint8Array(codec === publicKeyCodecs.P384 ? 49 : codec === publicKeyCodecs.P256 ? 33 : 32);
    bytes[0] = 2;
    const key = encodeMultikey(codec, bytes);
    assert.deepEqual(inspectMultikey(key), { codec, bytes });
    if (codec === publicKeyCodecs.Ed25519) assert.equal(multikeyIdentity(key), '@ed25519:' + key);
    else assert.throws(() => multikeyIdentity(key));
  }
});

test('boundedCounter builder uses the Rust counter rules', async () => {
  const to = ['issuer', 'holder'];
  const object = await defineContract({ name: 'coins', roles: { issuer: 'singleton', holder: 'indexed' },
    verbs: {
      open: { after: ['begin'], fields: { allocations: 'list' }, from: 'issuer', to },
      mint: { after: ['open'], fields: { amount: 'integer' }, from: 'issuer', to },
      burn: { after: ['open'], fields: { amount: 'integer' }, from: 'holder', to },
      pay: { after: ['open'], fields: { recipient: 'symbol', amount: 'integer' }, from: 'holder', to },
    },
    state: { coins: c.boundedCounter([['floor', 0], ['initial-rights', 'open', ':allocations'],
      ['issuers', 'issuer'], ['increment', 'mint', ':amount'], ['decrement', 'burn', ':amount'],
      ['transfer', 'pay', ':recipient', ':amount']]) },
  });
  assert.equal(object.info.state.coins[0], 'boundedCounter');
});

test('resource check verifies a candidate against the accepted prefix', async () => {
  const v = await vector('state/bounded-coin.json');
  const records = v.messages.map((m: { canonical: string; signer: string }) => actRecord(m.canonical, m.signer));
  const runtime = createRuntime(v.contract);
  assert.equal(runtime.resourceCheck(v.thread, records.slice(0, 2), records[2]).status, 'ready');
});

test('certified checkpoint resumes from a native certificate and refuses altered evidence atomically', async () => {
  const v = await vector('checkpoints/sdk.json');
  const bytes = Buffer.from(v.certificate, 'hex');
  const client = openCheckpoint(v.context, bytes);
  try {
    const before = client.read();
    assert.equal(before.title, 'Drawing');
    const proofs = v.step.ancestry.map(([message, proof]: [string, unknown]) =>
      [readAct(message).address, proof]).filter(([id]: [string, unknown]) => client.frontier().includes(id));
    client.replace(bytes, proofs);
    const damaged = structuredClone(v.step);
    damaged.identity.siblings[0][0] ^= 1;
    assert.throws(() => client.apply(damaged));
    assert.deepEqual(client.read(), before);
    client.apply(v.step);
    assert.deepEqual(client.read().items, { shape: 'after' });
    assert.throws(() => client.replace(bytes, proofs));
    assert.deepEqual(client.read().items, { shape: 'after' });
  } finally { client.close(); }
  const wrongKeys = { ...v.context.publicKeys, '@init': encodeMultikey(publicKeyCodecs.Ed25519, new Uint8Array(32)) };
  assert.throws(() => openCheckpoint({ ...v.context, publicKeys: wrongKeys }, bytes));
  bytes[0] ^= 1;
  assert.throws(() => openCheckpoint(v.context, bytes));
});
