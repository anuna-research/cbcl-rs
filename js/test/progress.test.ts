// Fixture identities; admission, binding and folding run in the actual WASM.
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { c, createRuntime, actRecord, ThreadStore } from '../src/object/index.ts';
const dialect=await readFile(new URL('../../dialects/count-to-one-hundred.cbcl',import.meta.url),'utf8');
const thread='progress-demo';

test('three agents converge at 100 despite competing final ticks',()=>{
 const agents=['@a','@b','@c'].map(signer=>({signer,store:new ThreadStore(),runtime:createRuntime(dialect)}));
 const deliver=(message:ReturnType<typeof actRecord>)=>{
  for(const agent of agents){
   assert.equal(agent.runtime.admit(thread,agent.store.messages(thread),message).verdict,'accepted');
   agent.store.append(message);
  }
 };
 const bind=(agent:typeof agents[number])=>{
  const bound=agent.runtime.intend(thread,agent.store.messages(thread),agent.signer,'tick',{});
  assert.equal(bound.ok,true,JSON.stringify(bound));
  if(!bound.ok)throw new Error(bound.reason);
  const message=actRecord(bound.canonical,agent.signer);
  assert.match(message.canonical,/:caused-by f1220/);
  return message;
 };
 deliver(actRecord('(lang count-to-one-hundred (tick @all :caused-by begin :thread "progress-demo" :from @a))','@a'));
 for(let position=2;position<=99;position++)deliver(bind(agents[(position-1)%3]));
 for(const agent of agents)assert.equal(agent.runtime.read(thread,agent.store.messages(thread)).number,99);
 // Both agents bind against position 99 before either message is delivered.
 const b=bind(agents[1]),cTick=bind(agents[2]);
 assert.notEqual(b.cid,cTick.cid);assert.equal(b.causedBy,cTick.causedBy);
 deliver(b);deliver(cTick);
 for(const agent of agents){
  assert.equal(agent.store.messages(thread).length,101);
  assert.equal(agent.runtime.read(thread,agent.store.messages(thread)).number,100);
  assert.equal(agent.store.append(b),false);
  assert.equal(agent.runtime.read(thread,agent.store.messages(thread).toReversed(),{fresh:true}).number,100);
  assert.equal(agent.runtime.intend(thread,agent.store.messages(thread),agent.signer,'tick',{}).ok,false);
 }
});

test('progress authoring uses the native rule head',()=>{
 assert.deepEqual(c.progress('tick'),['progress','tick']);
});
