#!/usr/bin/env python3
"""Run one local compile/proof process under recorded sampled aggregate caps."""
import json,os,signal,subprocess,sys,time,shutil
from pathlib import Path
root=Path(__file__).resolve().parent
label=sys.argv[1];command=sys.argv[2:]
assert label.replace('-','').isalnum() and command
out=root/'evidence';out.mkdir(exist_ok=True)
(out/f'{label}-run.json').unlink(missing_ok=True)
def handle_term(_sig,_frame):
 raise KeyboardInterrupt('supervisor received SIGTERM')
signal.signal(signal.SIGTERM,handle_term)
threads=int(os.environ.get('CBCL_RAYON_THREADS','4'));assert 1<=threads<=4
started=time.monotonic();peak=0;minimum=shutil.disk_usage(root).free;reason=None;code=None
session=root/'.session';session.mkdir(exist_ok=True)
epoch=session/'epoch.json'
if not epoch.exists():
 info=(root.parents[1]/'.git').stat()
 epoch.write_text(json.dumps({'start':getattr(info,'st_birthtime',info.st_mtime)}))
experiment_start=json.loads(epoch.read_text())['start']
(out/'session-start.json').write_text(epoch.read_text())
if time.time()-experiment_start>5400 or minimum<1024**3:
 reason='preflight experiment time budget or disk reserve exhausted'
 result={'command':command,'exit_code':None,'limit_reason':reason,'spawned':False}
 (out/f'{label}-run.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result));sys.exit(1)
def kill_group(pid,sig):
 try:os.killpg(pid,sig)
 except ProcessLookupError:pass
with (out/f'{label}.log').open('w') as log:
 child=subprocess.Popen(command,cwd=root,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,env={**os.environ,'CARGO_BUILD_JOBS':'1','RAYON_NUM_THREADS':str(threads),'RUSTUP_TOOLCHAIN':'1.95.0'})
 try:
  while child.poll() is None:
   rows=subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines()
   processes=[tuple(map(int,r.split())) for r in rows if len(r.split())==3]
   ids={child.pid}
   while True:
    expanded=ids|{p for p,parent,_ in processes if parent in ids}
    if expanded==ids:break
    ids=expanded
   rss=sum(r*1024 for p,_,r in processes if p in ids);peak=max(peak,rss)
   minimum=min(minimum,shutil.disk_usage(root).free)
   if rss>4*1024**3:reason='aggregate process-tree RSS exceeded 4 GiB'
   elif minimum<1024**3:reason='disk reserve below 1 GiB'
   elif time.monotonic()-started>1800:reason='process exceeded 30 minutes'
   elif time.time()-experiment_start>5400:reason='experiment exceeded 90-minute wall envelope'
   if reason:break
   time.sleep(2)
 except BaseException as error:
  reason=f'monitor interrupted or failed: {error}'
 finally:
  if child.poll() is None or reason:
   kill_group(child.pid,signal.SIGTERM)
   # Grace is for the entire process group, not just its leader.
   time.sleep(2)
  kill_group(child.pid,signal.SIGKILL)
  code=child.wait()
result={'command':command,'exit_code':code,'seconds':time.monotonic()-started,'peak_observed_tree_rss_bytes':peak,'rss_sample_interval_seconds':2,'minimum_free_bytes':minimum,'limit_reason':reason,'mock_proofs':False,'rayon_threads':threads}
(out/f'{label}-run.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
sys.exit(0 if code==0 and reason is None else 1)
