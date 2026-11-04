"""Check a real receipt against independent expected commitments and corruptions."""
import json,os,subprocess,sys
from pathlib import Path
host=Path('target/release/checkpoint-host')
case=sys.argv[1] if len(sys.argv)>1 else 'drawing-1'
kind=sys.argv[2] if len(sys.argv)>2 else 'composite'
directories={('drawing-1','composite'):'proved-drawing-1-tuned',('drawing-1','succinct'):'succinct-drawing-1',('status-8','composite'):'proved-status-8',('status-8','succinct'):'succinct-status-8'}
receipt=Path('evidence')/directories[(case,kind)]/'receipt.bin'
expected=Path(f'evidence/independent-{case}/expected.json')
state=Path(f'evidence/independent-{case}/state.json')
base=json.loads(expected.read_text());directory=Path(f'.artifacts/negative/{case}-{kind}');directory.mkdir(parents=True,exist_ok=True)
results=[]
def check(name,r,e,s,accepted=False,dev='0'):
 run=subprocess.run([str(host),'verify',str(r),str(e),str(s)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env={**os.environ,'RISC0_DEV_MODE':dev})
 assert (run.returncode==0)==accepted,(name,run.stdout)
 results.append({'case':name,'accepted':run.returncode==0,'expected_accepted':accepted,'output':run.stdout})
check('honest',receipt,expected,state,True)
for key,value in [('thread','wrong'),('dialect','sha256-'+'0'*64),('messages_hash',[0]*32),('dialect_sources_hash',[0]*32)]:
 changed={**base,key:value};path=directory/f'{key}.json';path.write_text(json.dumps(changed));check('wrong-'+key,receipt,path,state)
wrong_state=directory/'wrong-state.json';wrong_state.write_text('{}');check('tampered-state',receipt,expected,wrong_state)
corrupt=bytearray(receipt.read_bytes());corrupt[len(corrupt)//2]^=1;path=directory/'corrupt.bin';path.write_bytes(corrupt);check('corrupt-receipt',path,expected,state)
fake=directory/'fake.bin';subprocess.run(['target/release/make-fake',str(receipt),str(fake)],check=True)
check('fake-even-with-dev-enabled',fake,expected,state,dev='true')
assert 'fake receipt forbidden' in results[-1]['output']
Path(f'evidence/receipt-negative-{case}-{kind}-results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps([{'case':r['case'],'accepted':r['accepted']} for r in results]))
