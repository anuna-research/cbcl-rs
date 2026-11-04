"""Exercise a serialized Akita receiver against independent context and tampering."""
import json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent
case=sys.argv[1] if len(sys.argv)>1 else 'drawing-1'
out=root/'evidence'/case
pins=root/'evidence'/f'independent-{case}'
tmp=root/'.artifacts'/'negative'/case;tmp.mkdir(parents=True,exist_ok=True)
setup=out/'verifier-setup.bin';proof=out/'proof.bin';io=out/'io.bin'
expected=pins/'expected.json';state=pins/'state.json';trusted=pins/'trusted.json'
results=[]
def check(name,s=setup,p=proof,i=io,e=expected,st=state,t=trusted,accepted=False):
 args=[sys.executable,str(root/'run-from-jolt.py'),'verify',*[str(x) for x in [s,p,i,e,st,t]],'no-history']
 run=subprocess.run(args,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 ok=run.returncode==0
 results.append({'case':name,'accepted':ok,'expected_accepted':accepted,'output':run.stdout})
 assert ok==accepted,(name,run.stdout)
check('honest',accepted=True)
base=json.loads(expected.read_text())
for key,value in [('thread','wrong'),('dialect','sha256-'+'0'*64),('messages_hash',[0]*32),('dialect_sources_hash',[0]*32),('count',999)]:
 path=tmp/f'{key}.json';path.write_text(json.dumps({**base,key:value}));check('wrong-'+key,e=path)
path=tmp/'state.json';path.write_text('{}');check('tampered-state',st=path)
for name,original,argument in [('proof',proof,'p'),('setup',setup,'s'),('io',io,'i')]:
 data=bytearray(original.read_bytes());data[len(data)//2]^=1
 path=tmp/f'{name}.bin';path.write_bytes(data);check('corrupt-'+name,**{argument:path})
# Change the public output and receiver expectation coherently: only proof
# binding, not the local expected-journal comparison, should reject this.
old=base['thread'];new=('X' if old[0]!='X' else 'Y')+old[1:]
raw=io.read_bytes();assert raw.count(old.encode())==1
changed_io=tmp/'coherent-io.bin';changed_io.write_bytes(raw.replace(old.encode(),new.encode()))
changed_expected=tmp/'coherent-expected.json';changed_expected.write_text(json.dumps({**base,'thread':new}))
check('coherent-public-output-tamper',i=changed_io,e=changed_expected)
assert 'verification:' in results[-1]['output'],results[-1]
path=tmp/'wrong-trust.json';pin=json.loads(trusted.read_text());pin['setup_sha256']=[0]*32;path.write_text(json.dumps(pin));check('wrong-program-pin',t=path)
(root/'evidence'/f'receiver-negative-{case}.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps([{'case':r['case'],'accepted':r['accepted']} for r in results]))
