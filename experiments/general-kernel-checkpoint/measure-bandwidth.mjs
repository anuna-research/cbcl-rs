// Measure transport with preinstalled verifier and independently pinned expectations.
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,existsSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {gzipSync,gunzipSync,brotliCompressSync,brotliDecompressSync,constants} from 'node:zlib';
function commitment(domain,parts) {
 const h=createHash('sha256');
 for(const p of [Buffer.from(domain),...parts]) {const n=Buffer.alloc(8);n.writeBigUInt64LE(BigInt(p.length));h.update(n);h.update(p);}
 return [...h.digest()];
}
function sizes(value) {
 const raw=Buffer.from(JSON.stringify(value)),gzip=gzipSync(raw,{level:9}),br=brotliCompressSync(raw,{params:{[constants.BROTLI_PARAM_QUALITY]:5}});
 assert.deepEqual(gunzipSync(gzip),raw);assert.deepEqual(brotliDecompressSync(br),raw);
 return {raw:raw.length,gzip9:gzip.length,brotli5:br.length};
}
const result={cases:{},firstDownloadHostBinaryBytes:readFileSync('target/release/checkpoint-host').length,notes:[
 'Host binary includes execution/proving; it is not a minimal browser verifier.',
 'Assumes a preinstalled verifier and independently authenticated expected commitments; acquiring/authenticating them is excluded and unmeasured.',
 'The snapshot/receipt bundle includes image ID and full dialect closure. No end-to-end first-sync or smaller-than-history claim is made.'
]};
let firstImage;
for(const [name,proofDir,proofLabel,compressedDir,compressedLabel] of [
 ['drawing-1','proved-drawing-1-tuned','prove-drawing-1-tuned','succinct-drawing-1','compress-drawing-1'],
 ['status-8','proved-status-8','prove-status-8','succinct-status-8','compress-status-8']
]) {
 const input=JSON.parse(readFileSync(`fixtures/${name}.json`));
 const expected=JSON.parse(readFileSync(`evidence/independent-${name}/expected.json`));
 const state=readFileSync(`evidence/independent-${name}/state.json`,'utf8');
 const imageId=JSON.parse(readFileSync(`evidence/independent-${name}/image-id.json`));
 if(firstImage)assert.deepEqual(imageId,firstImage);else firstImage=imageId;
 assert.deepEqual(commitment('cbcl-checkpoint-dialect-source-closure-v1',[Buffer.from(input.dialect)]),expected.dialect_sources_hash);
 assert.deepEqual(commitment('cbcl-checkpoint-state-v1',[Buffer.from(state)]),expected.state_hash);
 const row={messages:input.messages.length,replay:sizes(input),snapshotOnly:sizes({dialectSources:input.dialect,thread:input.thread,state}),bundles:{}};
 for(const [kind,dir,label] of [['composite',proofDir,proofLabel],['succinct',compressedDir,compressedLabel]]) {
  const path=`evidence/${dir}/receipt.bin`,ledger=`evidence/${label}-run.json`;
  if(!existsSync(path)||!existsSync(ledger))continue;
  const run=JSON.parse(readFileSync(ledger));if(run.exit_code!==0||run.limit_reason!==null)continue;
  const receipt=readFileSync(path);
  const bundle={format:'cbcl-zkvm-checkpoint-experiment-v1',imageId,dialectSources:input.dialect,state,receipt:receipt.toString('base64')};
  writeFileSync(`.artifacts/${name}-${kind}-bundle.json`,JSON.stringify(bundle));
  row.bundles[kind]={receiptBinaryBytes:receipt.length,...sizes(bundle)};
 }
 result.cases[name]=row;
}
writeFileSync('evidence/bandwidth.json',JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result));
