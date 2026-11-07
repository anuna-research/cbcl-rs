import test from 'node:test';
import assert from 'node:assert/strict';
import { defineContract, c, createRuntime, actRecord, enumOf, readAct } from '../src/object/index.ts';

const source = {
  name: 'hlc-registers', author: '@a',
  verbs: {
    open: { after: ['begin'], fields: { title: 'string' } },
    write: { after: ['open'], fields: { item: 'string', value: 'string', clock: "hlc" } },
    drop: { after: ['open'], fields: { item: 'string' } },
  },
  state: {
    last: c.lwwRegister('write', 'value', 'clock'),
    own: c.lwwPerSigner('write', 'value', 'clock'),
    map: c.lwwMap('write', 'item', 'value', 'clock', 'drop'),
    values: c.multiValueRegister('write', 'value'),
    all: c.multiValueMap('write', 'item', 'value'),
  },
};

test('new authoring names use the shared HLC fold and explicit clock input', async () => {
  const object = await defineContract(source);
  const root = actRecord(object.open({room:'@a',thread:'t',from:'@a',fields:{title:'demo'}}),'@a');
  const runtime = createRuntime(object.dialect);
  const old = runtime.intend('t',[root],'@alice','write',{item:'x',value:'old',clock:'hlc-0000000000000001-00000000'});
  const newer = runtime.intend('t',[root],'@bob','write',{item:'x',value:'new',clock:'hlc-0000000000000002-00000000'});
  assert.equal(old.ok,true); assert.equal(newer.ok,true);
  if (!old.ok || !newer.ok) return;
  const a=actRecord(old.canonical,'@alice'), b=actRecord(newer.canonical,'@bob');
  const records=[root,a,b];
  const expected={last:'new',own:{'@alice':'old','@bob':'new'},map:{x:'new'},values:['new','old'],all:{x:['new','old']}};
  assert.deepEqual(runtime.read('t',records),expected);
  assert.deepEqual(createRuntime(object.dialect).read('t',records.slice().reverse()),expected);
  assert.deepEqual(createRuntime(object.dialect).read('t',[...records,...records]),expected);
  const missing=runtime.intend('t',records,'@alice','write',{item:'x',value:'bad'});
  const malformed=runtime.intend('t',records,'@alice','write',{item:'x',value:'bad',clock:'future'});
  assert.equal(missing.ok,false); assert.equal(malformed.ok,false);
});


test('domain-excluded same-key writes cannot corrupt deletion bookkeeping', async () => {
  const object=await defineContract({...source,verbs:{...source.verbs,
    open:{after:['begin'],fields:{title:'string',options:'list' as const}},
    write:{after:['open'],fields:{item:'string',value:enumOf('options'),clock:"hlc"}}},
    state:{options:c.initial('open','options'),...source.state}});
  const root=actRecord(object.open({room:'@a',thread:'t',from:'@a',fields:{title:'demo',options:['allowed']}}),'@a');
  const runtime=createRuntime(object.dialect);
  const first=runtime.intend('t',[root],'@alice','write',{item:'x',value:'allowed',clock:'hlc-0000000000000001-00000000'});
  assert.equal(first.ok,true); if (!first.ok) return;
  const a=actRecord(first.canonical,'@alice');
  const bad=actRecord(`(lang ${object.name} (write @a :item "x" :value "excluded" :clock "hlc-ffffffffffffffff-ffffffff" :replaces (${a.cid}) :from @alice :thread "t" :caused-by ${root.cid}))`,'@alice');
  const records=[root,a,bad];
  assert.equal((runtime.read('t',records) as {map:Record<string,string>}).map.x,'allowed');
  const deletion=runtime.intend('t',records,'@alice','drop',{item:'x'});
  assert.equal(deletion.ok,true); if (!deletion.ok) return;
  assert.deepEqual(readAct(deletion.canonical).fields.replaces,[a.cid]);
});


test('declared hlc fields validate without an LWW rule and retain their type', async () => {
  const object = await defineContract({name:'typed-clock', verbs:{
    open:{after:['begin'], fields:{when:'hlc' as const}}},
    state:{when:c.initial('open','when')}});
  assert.equal(object.info.verbs.open.fields.when,'hlc');
  assert.throws(()=>object.open({room:'@a',thread:'t',from:'@a',fields:{when:'invalid'}}),/hlc/);
  const valid='hlc-000001a3185c5000-00000000';
  const root=actRecord(object.open({room:'@a',thread:'t',from:'@a',fields:{when:valid}}),'@a');
  assert.equal(object.runtime.read('t',[root]).when,valid);
});
