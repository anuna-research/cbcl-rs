#!/usr/bin/env python3
"""Exercise durable milestone recovery and fail-closed artifact verification.

Run after the managed 128-write proof run. Restores manifest corruption probes.
The repaired harness resumes a real, already verified whole-history proof.
"""
import json,os,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent; evidence=root/'evidence/recursive'; progress=evidence/'progress.json'
initial=json.loads(progress.read_text())
assert initial['status']=='passed' and initial['target']==128
assert initial['latestCompleteWrites']==128
assert [r['history'] for r in initial['proofs']]==[0,1,8,32,128]
for name in ['real-proof-run.log','run-status.json','progress.json']:
 (evidence/('initial-'+name)).write_bytes((evidence/name).read_bytes())
# Reproduce an interrupted current milestone: latest complete proof exists,
# but the corresponding report row is missing. The fixed resume must recover it.
incomplete={**initial,'proofs':[r for r in initial['proofs'] if r['history']!=128]}
progress.write_text(json.dumps(incomplete,indent=2)+'\n')
command=['python3','run-recursive-proof.py','--resume','--target=128']
with (evidence/'recovery-run.log').open('w') as output:
 run=subprocess.run(command,cwd=root,env=os.environ,stdout=output,stderr=subprocess.STDOUT,timeout=1850)
assert run.returncode==0,'managed recovery failed; retain its evidence'
complete=progress.read_bytes(); current=json.loads(complete)
assert current['status']=='passed'
assert [r['history'] for r in current['proofs']]==[0,1,8,32,128]
assert all('canonicalMessageJsonBytes' in r for r in current['proofs'])
rows=[{'case':'recover-current-milestone','command':command,'exit_code':run.returncode,'recovered':True}]
try:
 for name,badrows in [('empty-manifest',[]),('missing-prior-milestone',[r for r in current['proofs'] if r['history']!=8])]:
  progress.write_text(json.dumps({**current,'proofs':badrows}))
  cmd=['node','--import','tsx','recursive-verify.ts','--history=128']
  result=subprocess.run(cmd,cwd=root,env=os.environ,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
  (evidence/(name+'.log')).write_text(result.stdout.rstrip()+'\n')
  assert result.returncode!=0 and 'all promised complete histories must exist' in result.stdout
  rows.append({'case':name,'command':cmd,'exit_code':result.returncode,'rejected':True})
 # A missing OLD milestone cannot be reconstructed from the latest proof alone.
 # It must prevent the producer's passed status, rather than silently claiming it.
 progress.write_text(json.dumps({**current,'proofs':[r for r in current['proofs'] if r['history']!=8]}))
 cmd=['node','--import','tsx','recursive-prove.ts','--resume','--target=128']
 result=subprocess.run(cmd,cwd=root,env=os.environ,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
 (evidence/'resume-missing-prior-milestone.log').write_text(result.stdout.rstrip()+'\n')
 assert result.returncode!=0 and 'all promised complete-history milestones must be durable' in result.stdout
 assert json.loads(progress.read_text())['status']=='failed'
 rows.append({'case':'producer-withholds-passed-for-missing-old-milestone','command':cmd,'exit_code':result.returncode,'rejected':True})
finally: progress.write_bytes(complete)
(evidence/'recovery-checks.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
