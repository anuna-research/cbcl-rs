"""Independent receiver checks: only public artifacts, no history argument."""
import json,os,pathlib,subprocess,sys,time
root=pathlib.Path(__file__).resolve().parents[2];exp=pathlib.Path(__file__).resolve().parent
out=pathlib.Path(os.environ.get('CBCL_VOTE_OUTPUT',root/'outputs/private-vote-export')).resolve()
mode=sys.argv[1];proofdir=out/(mode+'-proof');pins=out/'operator-pins'/mode
case_dir=out/(mode+'-receiver-cases');case_dir.mkdir(exist_ok=True)
expected=json.loads((pins/'expected.json').read_text());records=[]
def check(name,accept,reason=None,setup=None,proof=None,io=None,expect=None,pin=None):
 args=['python3',str(exp/'run-host.py'),mode,'verify',str(setup or proofdir/'setup.bin'),str(proof or proofdir/'proof.bin'),str(io or proofdir/'io.bin'),str(expect or pins/'expected.json'),str(pin or pins/'trusted.json'),'no-history']
 t=time.monotonic();r=subprocess.run(args,capture_output=True,text=True,timeout=120)
 records.append({'case':name,'accepted':r.returncode==0,'expected_accepted':accept,'wall_seconds':time.monotonic()-t,'exit_code':r.returncode,'output':r.stdout+r.stderr})
 (case_dir/'results.json').write_text(json.dumps(records,indent=2)+'\n')
 records[-1]['rejection_stage']=('recognition' if 'OtherString("the input buffer contained invalid data")' in r.stderr else 'verification' if 'verification:' in r.stderr else 'policy' if not accept else None)
 assert (r.returncode==0)==accept,records[-1]
 if not accept:
  assert reason and any(x in r.stderr for x in (reason if isinstance(reason,tuple) else (reason,))),records[-1]
  assert 'panicked at' not in r.stderr and 'host thread panic' not in r.stderr,records[-1]
def changed(name,field,value):
 v=json.loads(json.dumps(expected));v[field]=value
 p=case_dir/(name+'.json');p.write_text(json.dumps(v));return p
check('honest',True)
for name,field,value in [('wrong-thread','thread','other'),('wrong-tally','tally',{'yes':2}),('wrong-count','covered_count',99),('wrong-closure','covered_set_commitment',[0]*32),('wrong-roster','participants',list(reversed(expected['participants']))),('wrong-semantics','semantics','obsolete')]:
 check(name,False,reason="expected statement differs",expect=changed(name,field,value))
p=changed('coherent-tally','tally',{'yes':2});io=case_dir/'changed-io.bin'
subprocess.run(['python3',str(exp/'run-host.py'),mode,'tamper-io',str(proofdir/'io.bin'),str(p),str(io)],check=True)
check('coherent-tally-tamper',False,reason='verification:',io=io,expect=p)
for name,filename in [('corrupt-proof','proof.bin'),('corrupt-setup','setup.bin')]:
 data=bytearray((proofdir/filename).read_bytes());data[len(data)//2]^=1
 p=case_dir/filename;p.write_bytes(data)
 check(name,False,reason=(('verification:', 'OtherString("the input buffer contained invalid data")') if filename=='proof.bin' else 'untrusted setup'),**({'proof':p} if filename=='proof.bin' else {'setup':p}))
trust=json.loads((pins/'trusted.json').read_text());trust['zk']=not trust['zk'];p=case_dir/'wrong-mode-pin.json';p.write_text(json.dumps(trust));check('wrong-mode-pin',False,reason='wrong backend/mode pin',pin=p)
other=out/('clear-proof' if mode=='zk' else 'zk-proof')
assert (other/'proof.bin').exists(), 'both modes required for cross-mode evidence'
check('cross-mode-proof',False,reason='wrong proof protocol',proof=other/'proof.bin')
trust=json.loads((pins/'trusted.json').read_text());trust['setup_sha256']=[0]*32
p=case_dir/'wrong-setup-pin.json';p.write_text(json.dumps(trust));check('wrong-setup-pin',False,reason='untrusted setup',pin=p)
io=case_dir/'advice-io.bin'
subprocess.run(['python3',str(exp/'run-host.py'),'zk','tamper-advice',str(proofdir/'io.bin'),str(io)],check=True)
check('nonempty-advice',False,reason='advice leaked',io=io)
(case_dir/'results.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))
