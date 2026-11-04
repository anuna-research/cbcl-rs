// Real SDK-generated test inputs only; never contacts a running drawing app.
import assert from 'node:assert/strict';
import {writeFileSync,mkdirSync,readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
const root=resolve(process.env.CBCL_BUS_REPO||'../../../cbcl-bus');
const sdk=await import(pathToFileURL(root+'/apps/cbcl_chat/priv/web/cbcl/object/index.js'));
const {drawing}=await import(pathToFileURL(root+'/examples/object-sdk/drawing.mjs'));
const {defineContract,c,actRecord}=sdk;
const board=await defineContract({dialect:'checkpoint-status-board',verbs:{open:{causedBy:'begin',fields:{title:'string'}},put:{causedBy:'open',fields:{value:'string'}}},state:{title:c.last('open','title'),heads:c.latestPerSigner('put','value'),count:c.count('put')}});
mkdirSync('fixtures',{recursive:true});
for (const [name,object,verb,values] of [
 ['drawing',drawing,'chunk',Array.from({length:8},(_,i)=>({'chunk-id':`stroke:${i}`,data:['stroke','#203e36',6,i,i,i+1,i+1]}))],
 ['status',board,'put',Array.from({length:8},(_,i)=>({value:`state${i%3}`}))]
]) {
 for(const count of [0,1,8]) {
  const thread='checkpoint-'+name, records=[actRecord(object.open({room:'@benchmark',thread,from:'@owner',fields:{title:'Checkpoint benchmark'}}),'@owner')];
  for(let i=0;i<count;i++) {
   const signer='@writer'+i%2;
   const result=object.runtime.intend(thread,records,signer,verb,values[i]);assert.equal(result.ok,true);
   records.push(actRecord(result.canonical,signer));
  }
  const input={dialect:object.dialect,thread,messages:records.map(({signer,canonical})=>({signer,canonical}))};
  writeFileSync(`fixtures/${name}-${count}.json`,JSON.stringify(input,null,2)+'\n');
  writeFileSync(`fixtures/${name}-${count}-state.json`,JSON.stringify(object.runtime.read(thread,records,{fresh:true})));
 }
}
const sources={};for(const path of ['apps/cbcl_chat/priv/web/cbcl/cbcl_wasm_bg.wasm','apps/cbcl_chat/priv/web/object-starters/drawing.mjs','apps/cbcl_chat/priv/web/cbcl/object/compile.js'])sources[path]=createHash('sha256').update(readFileSync(root+'/'+path)).digest('hex');
writeFileSync('evidence/fixture-provenance.json',JSON.stringify({synthetic:true,sources},null,2)+'\n');
