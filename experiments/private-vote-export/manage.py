"""Run local experiment commands with sampled aggregate limits and durable results."""
import argparse,json,os,pathlib,shutil,signal,subprocess,time
p=argparse.ArgumentParser();p.add_argument('label');p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
assert a.label.replace('-','').isalnum() and a.command
root=pathlib.Path(__file__).resolve().parents[2]
out=pathlib.Path(os.environ.get('CBCL_VOTE_OUTPUT',root/'outputs/private-vote-export'));out.mkdir(parents=True,exist_ok=True)
assert not (out/(a.label+'-run.json')).exists(),'unique run label required'
volumes=(root,out,pathlib.Path(os.environ.get('CBCL_JOLT_TARGET','/Users/anuna-02/Code/cbcl-rs-jolt-akita/experiments/jolt-akita-checkpoint/target')))
start=time.monotonic();peak=0;minimum=min(shutil.disk_usage(p).free for p in volumes);reason=None;code=None
if minimum < 1024**3: raise SystemExit('preflight disk reserve below 1 GiB')
with (out/(a.label+'.log')).open('w') as log:
 child=subprocess.Popen(a.command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,env={**os.environ,'RAYON_NUM_THREADS':'4','CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0','RUSTUP_TOOLCHAIN':'1.95.0'})
 try:
  while child.poll() is None:
   rows=subprocess.check_output(['ps','-axo','pid=,ppid=,pgid=,rss='],text=True).splitlines()
   rows=[tuple(map(int,r.split())) for r in rows if len(r.split())==4];ids={child.pid}|{pid for pid,_,pgid,_ in rows if pgid==child.pid}
   while True:
    expanded=ids|{pid for pid,ppid,_,_ in rows if ppid in ids}
    if expanded==ids:break
    ids=expanded
   rss=sum(rss*1024 for pid,_,_,rss in rows if pid in ids);peak=max(peak,rss)
   minimum=min(minimum,*(shutil.disk_usage(p).free for p in (root,out,pathlib.Path(os.environ.get('CBCL_JOLT_TARGET','/Users/anuna-02/Code/cbcl-rs-jolt-akita/experiments/jolt-akita-checkpoint/target')))))
   if rss>4*1024**3:reason='sampled process tree RSS exceeded 4 GiB'
   elif minimum<1024**3:reason='disk reserve below 1 GiB'
   elif time.monotonic()-start>1800:reason='30-minute process limit'
   if reason:break
   time.sleep(2)
 except BaseException as e:reason=f'monitor interrupted: {e}'
 finally:
  # The dedicated process group includes orphaned grandchildren as well.
  try: os.killpg(child.pid,signal.SIGTERM)
  except ProcessLookupError: pass
  except PermissionError:
   if child.poll() is None: raise
  try: child.wait(timeout=3)
  except subprocess.TimeoutExpired: pass
  try: os.killpg(child.pid,signal.SIGKILL)
  except ProcessLookupError: pass
  except PermissionError:
   if child.poll() is None: raise
  code=child.wait()
result={'command':a.command,'exit_code':code,'seconds':time.monotonic()-start,'peak_observed_tree_rss_bytes':peak,'rss_sampling_seconds':2,'minimum_free_bytes':minimum,'limit_reason':reason,'rayon_threads':4,'mock_proofs':False}
(out/(a.label+'-run.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
raise SystemExit(0 if code==0 and reason is None else 1)
