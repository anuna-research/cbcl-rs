#!/usr/bin/env python3
"""Real-proof mutation control for omitted predecessor verification.

Compiles an isolated source variant with Cache.None, proves from a cryptographically
invalid and unreachable parent, and requires the negative assertion to go red.
No production/primary experiment sources or caches are mutated.
"""
import json,os,shutil,signal,subprocess,sys,tempfile,time
from pathlib import Path
root=Path(__file__).resolve().parent; evidence=root/'evidence/recursive'
source=(root/'recursive-program.ts').read_text()
assert source.count('  previous.verify();')==1
source=source.replace('  previous.verify();','  // MUTATION: predecessor verification omitted.')
source=source.replace("from './program.js'", "from '../program.js'")
source=source.replace("cbcl-recursive-register-paths-b8-v1", "cbcl-recursive-register-paths-b8-no-parent-verification-mutant")
driver=r'''
import assert from 'node:assert/strict';
import { readFile, writeFile } from 'node:fs/promises';
import { Cache, setNumberOfWorkers, verify } from 'o1js';
import { Checkpoint } from '../program.js';
import { objectId, trace } from '../helpers.js';
import { baseContext, unreachablePrefix } from '../recursive-helpers.js';
import { historyProgram, HistoryProof } from './program.js';
setNumberOfWorkers(1);
console.log(JSON.stringify({stage:'compile-real-verification-mutant'}));
const { verificationKey } = await historyProgram.compile({ cache: Cache.None });
const object = objectId(trace(0));
const base = (await historyProgram.base(baseContext(object))).proof;
const forged = unreachablePrefix(), json = base.toJSON();
json.publicOutput = Checkpoint.toFields(forged.checkpoint).map(x => x.toString());
const parent = await HistoryProof.fromJSON(json);
assert.equal(await verify(parent, verificationKey.data), false, 'forged parent must really be invalid');
console.log(JSON.stringify({stage:'prove-from-invalid-parent'}));
const child = (await historyProgram.batch(forged.next.context, parent, forged.next.updates)).proof;
const valid = await verify(child, verificationKey.data);
const honestKey = JSON.parse(await readFile('evidence/recursive/verification-key.json', 'utf8'));
const honestKeyRejectsChild = !(await verify(child, honestKey.data));
assert.equal(honestKeyRejectsChild, true, 'unsafe-variant proof must not verify under the honest key');
await writeFile('evidence/recursive/proof-verification-mutant-artifact.json', JSON.stringify({
  unsafeVariant: true, verificationKey: { hash: verificationKey.hash.toString(), data: verificationKey.data },
  forgedParent: parent.toJSON(), child: child.toJSON(), honestKeyRejectsChild,
}, null, 2) + '\n');
console.log(JSON.stringify({ invalidParentRejected: true, mutantChildVerified: valid, honestKeyRejectsChild, finalCount: child.publicOutput.count.toString() }));
assert.equal(valid, false, 'forged predecessor accepted after removing verification');
'''
def rss(pid):
 data=[tuple(map(int,line.split())) for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines() if len(line.split())==3]
 ids={pid}
 while True:
  more=ids|{p for p,parent,_ in data if parent in ids}
  if more==ids:break
  ids=more
 return sum(k*1024 for p,_,k in data if p in ids)
started=time.monotonic(); peak=0; minimum=shutil.disk_usage(root).free; reason=None
with tempfile.TemporaryDirectory(prefix='.recursion-mutant-',dir=root) as tmp:
 path=Path(tmp);(path/'program.ts').write_text(source);(path/'driver.ts').write_text(driver)
 command=['node','--import','tsx',str(path/'driver.ts')]
 with (evidence/'proof-verification-mutation.log').open('w') as output:
  child=subprocess.Popen(command,cwd=root,env=os.environ,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
  try:
   while child.poll() is None:
    time.sleep(2);peak=max(peak,rss(child.pid));minimum=min(minimum,shutil.disk_usage(root).free)
    if peak>4*1024**3:reason='4 GiB sampled RSS cap'
    elif minimum<1024**3:reason='1 GiB disk reserve'
    elif time.monotonic()-started>15*60:reason='15 minute mutation control cap'
    if reason:
     os.killpg(child.pid,signal.SIGTERM)
     try:child.wait(timeout=10)
     except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL)
     break
  finally:
   if child.poll() is None:os.killpg(child.pid,signal.SIGTERM)
   code=child.wait()
 text=(evidence/'proof-verification-mutation.log').read_text()
 killed=reason is None and code!=0 and '"mutantChildVerified":true' in text and 'forged predecessor accepted after removing verification' in text
 result={'name':'omitted-parent-proof-verification','exit_code':code,'killed':killed,'limit_reason':reason,'seconds':round(time.monotonic()-started,2),'peak_sampled_tree_rss_bytes':peak,'minimum_free_bytes':minimum,'cache':'Cache.None','source_variant':'temporary copy; original sources untouched','assertion':'forged predecessor accepted after removing verification'}
 (evidence/'proof-verification-mutation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
sys.exit(0 if killed else 1)
