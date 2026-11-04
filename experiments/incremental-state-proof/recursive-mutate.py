#!/usr/bin/env python3
"""Assertion-backed recursive composition mutations; restore sources on every path."""
import json,os,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent; path=root/'recursive-program.ts'; original=path.read_text()
mutants=[
 ('unbound-genesis-state','forged-genesis-state',"        context.before.state.assertEquals(EMPTY_ROOT, 'genesis state');"),
 ('unbound-parent-output','wrong-parent-output',"  sameCheckpoint(previous.publicOutput, context.before, 'predecessor checkpoint');"),
 ('unbound-parent-object','wrong-parent-object',"  previous.publicInput.object.assertEquals(context.object, 'predecessor object');"),
 ('unbound-batch-digest','wrong-batch-digest',"        batchDigest(context.object, updates.operations).assertEquals(context.operation, 'batch operation digest');"),
]
rows=[]
try:
 for name,test,line in mutants:
  assert original.count(line)==1,name
  path.write_text(original.replace(line,'// MUTATION: constraint removed.'))
  try:
   command=['node','--import','tsx','recursive-test.ts','--only='+test]
   run=subprocess.run(command,cwd=root,env=os.environ,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
  finally: path.write_text(original)
  (root/'evidence/recursive'/('mutant-'+name+'.log')).write_text(run.stdout.rstrip()+'\n')
  killed=run.returncode!=0 and 'Missing expected rejection' in run.stdout and 'recursive-test.ts' in run.stdout
  row=dict(name=name,test=test,command=command,exit_code=run.returncode,killed=killed);rows.append(row);print(json.dumps(row),flush=True)
finally:path.write_text(original)
(root/'evidence/recursive/mutations.json').write_text(json.dumps(rows,indent=2)+'\n')
sys.exit(0 if len(rows)==len(mutants) and all(x['killed'] for x in rows) else 1)
