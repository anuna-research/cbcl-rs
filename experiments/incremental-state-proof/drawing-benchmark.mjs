// Offline synthetic drawing workload through cbcl-bus's actual contract and WASM.
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
import {performance} from 'node:perf_hooks';
import {gzipSync,gunzipSync,brotliCompressSync,brotliDecompressSync,constants} from 'node:zlib';
const root=resolve(process.env.CBCL_BUS_REPO || '../../../cbcl-bus');
const {drawing}=await import(pathToFileURL(root+'/examples/object-sdk/drawing.mjs'));
const {actRecord}=await import(pathToFileURL(root+'/apps/cbcl_chat/priv/web/hypermedia/object-sdk.js'));
const n=Number(process.argv[2]||128), points=Number(process.argv[3]||4);
assert([128,1024,4096].includes(n)); assert([4,30].includes(points));
const thread='drawing-benchmark', title='Generated drawing benchmark';
const records=[actRecord(drawing.open({room:'@benchmark',thread,from:'@owner',fields:{title}}),'@owner')];
const expected={title,chunks:{},erased:{}};
const start=performance.now();
for(let i=0;i<n;i++) {
 const strokeNumber=Math.floor(i/8), part=i%8;
 const stroke=createHash('sha256').update('cbcl-drawing-v1:'+strokeNumber).digest('hex').slice(0,32).replace(/(.{8})(.{4})(.{4})(.{4})(.{12})/,'$1-$2-$3-$4-$5');
 const signer='@artist'+strokeNumber%4;
 let verb,fields;
 if(part===7 && strokeNumber%5===0) {verb='erase';fields={stroke};expected.erased[stroke]=stroke;}
 else {
  const data=[stroke,['#203e36','#bd5532','#355ca8','#222222'][strokeNumber%4],[3,6,14][strokeNumber%3]];
  for(let j=0;j<points;j++) {const k=part*(points-1)+j;data.push((strokeNumber*37+k*3)%1201,(strokeNumber*23+Math.round(18*Math.sin(k/7))+k)%721);}
  const key=stroke+':'+String(part).padStart(6,'0');
  verb='chunk';fields={'chunk-id':key,data}; expected.chunks[key]=data;
 }
 const result=drawing.runtime.intend(thread,[records[0]],signer,verb,fields);
 assert.equal(result.ok,true);records.push(actRecord(result.canonical,signer));
}
const generationMs=performance.now()-start;
console.log(JSON.stringify({stage:'generated',n,points,generationMs}));
const replayStart=performance.now();
const state=drawing.runtime.read(thread,records,{fresh:true});
const replayMs=performance.now()-replayStart;
assert.deepEqual(state,expected);
const visibleChunks=Object.fromEntries(Object.entries(state.chunks).filter(([,v])=>!Object.hasOwn(state.erased,v[0])));
const encodings={
 replay:JSON.stringify(records.map(({signer,canonical})=>({signer,canonical}))),
 nativeState:JSON.stringify(state),
 visiblePreview:JSON.stringify({title:state.title,chunks:visibleChunks})
};
const sizes={};
for(const [name,text] of Object.entries(encodings)) {
 const raw=Buffer.from(text),t=performance.now(); const gz=gzipSync(raw,{level:9});const gzipMs=performance.now()-t;
 const b=performance.now();const br=brotliCompressSync(raw,{params:{[constants.BROTLI_PARAM_QUALITY]:5}});const brotliMs=performance.now()-b;
 const d=performance.now();assert.deepEqual(gunzipSync(gz),raw);const gunzipMs=performance.now()-d;
 const e=performance.now();assert.deepEqual(brotliDecompressSync(br),raw);const unbrotliMs=performance.now()-e;
 const p=performance.now();assert.deepEqual(JSON.parse(text),JSON.parse(raw.toString()));const parseMs=performance.now()-p;
 sizes[name]={raw:raw.length,gzip9:gz.length,brotli5:br.length,gzipMs,brotliMs,gunzipAndValidateMs:gunzipMs,unbrotliAndValidateMs:unbrotliMs,parseRoundTripAndValidateMs:parseMs};
}
const sources={};for(const file of ['apps/cbcl_chat/priv/web/object-starters/drawing.mjs','apps/cbcl_chat/priv/web/cbcl/object/runtime.js','apps/cbcl_chat/priv/web/cbcl/verifier.js','apps/cbcl_chat/priv/web/cbcl/cbcl_wasm.js','apps/cbcl_chat/priv/web/cbcl/cbcl_wasm_bg.wasm','apps/cbcl_chat/priv/web/cbcl/object/compile.js','apps/cbcl_chat/priv/web/cbcl/object/index.js'])sources[file]=createHash('sha256').update(readFileSync(resolve(root,file))).digest('hex');
const result={dataset:'synthetic-app-contract-v1',messages:n+1,operations:n,pointsPerChunk:points,writers:4,chunks:Object.keys(state.chunks).length,erasedStrokes:Object.keys(state.erased).length,visibleChunks:Object.keys(visibleChunks).length,generationMs,freshNativeAdmissionAndFoldMs:replayMs,stateEqualsIndependentExpected:true,sizes,sources,node:process.version,platform:process.platform,arch:process.arch,proofCoverage:false,notes:['Authenticated signer labels assumed; signatures absent.','nativeState is the current full fold output, not a resumable/authenticated checkpoint.','visiblePreview omits erased data and cannot replace native state.','No drawing proof exists in this experiment.']};
mkdirSync('evidence/benchmark',{recursive:true});writeFileSync(`evidence/benchmark/drawing-${n}-${points}.json`,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result));
