#!/usr/bin/env python3
"""Exercise the synthetic oracle's declared bounded JSON recognition."""
import json,os,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent
binary=os.environ.get('CBCL_INCREMENTAL_ORACLE',str(root.parent.parent/'target/debug/examples/incremental_oracle'))
def execute(data): return subprocess.run([binary],input=data,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
good={'records':[{'signer':0,'seq':0,'value':3,'replaces':None}]}
rows=[]
r=execute(json.dumps(good).encode()); assert r.returncode==0,r.stderr
assert json.loads(r.stdout)['state']['entries']=={'@writer0':'3'}
rows.append({'case':'valid-native-first-write','result':'pass'})
cases={
 'top-array':b'[[]]',
 'record-array':b'{"records":[[0,0,3,null]]}',
 'unknown-input-member':b'{"records":[],"extra":0}',
 'duplicate-input-member':b'{"records":[],"records":[]}',
 'unknown-record-member':b'{"records":[{"signer":0,"seq":0,"value":3,"extra":0}]}',
 'duplicate-record-member':b'{"records":[{"signer":0,"seq":0,"value":3,"value":4}]}',
 'signer-capacity':b'{"records":[{"signer":65536,"seq":0,"value":3}]}',
 'negative-u32':b'{"records":[{"signer":0,"seq":-1,"value":3}]}',
 'record-capacity':json.dumps({'records':[{'signer':0,'seq':0,'value':3}]*4097}).encode(),
 'byte-capacity':b' '*(1_048_576+1),
 'trailing-input':b'{"records":[]}x',
}
for name,data in cases.items():
 r=execute(data);assert r.returncode!=0,name
 rows.append({'case':name,'result':'rejected','exit_code':r.returncode})
(root/'evidence/oracle-checks.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
