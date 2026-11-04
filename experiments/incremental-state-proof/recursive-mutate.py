#!/usr/bin/env python3
"""Assertion-backed composition/kernel mutations with unconditional restoration."""
import json,os,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent
mutants=[
 ('unbound-genesis-state','forged-genesis-state','recursive-program.ts',["        context.before.state.assertEquals(EMPTY_ROOT, 'genesis state');"]),
 ('unbound-parent-output','wrong-parent-output','recursive-program.ts',["  sameCheckpoint(previous.publicOutput, context.before, 'predecessor checkpoint');"]),
 ('unbound-parent-object','wrong-parent-object','recursive-program.ts',["  previous.publicInput.object.assertEquals(context.object, 'predecessor object');"]),
 ('unbound-batch-digest','wrong-batch-digest','recursive-program.ts',["        batchDigest(context.object, updates.operations).assertEquals(context.operation, 'batch operation digest');"]),
 ('batch-unbound-replacement','wrong-operation-inside-batch','program.ts',["        operation.previousLo.assertEquals(head.lo, 'replacement low');", "        operation.previousHi.assertEquals(head.hi, 'replacement high');"]),
]
originals={file:(root/file).read_text() for _,_,file,_ in mutants};rows=[]
try:
 for name,test,file,lines in mutants:
  source=originals[file]
  for line in lines:
   assert source.count(line)==1,name
   source=source.replace(line,'// MUTATION: constraint removed.')
  (root/file).write_text(source)
  try:
   command=['node','--import','tsx','recursive-test.ts','--only='+test]
   run=subprocess.run(command,cwd=root,env=os.environ,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
  finally:(root/file).write_text(originals[file])
  (root/'evidence/recursive'/('mutant-'+name+'.log')).write_text(run.stdout.rstrip()+'\n')
  killed=run.returncode!=0 and 'Missing expected rejection' in run.stdout and 'recursive-test.ts' in run.stdout
  row=dict(name=name,test=test,file=file,command=command,exit_code=run.returncode,killed=killed);rows.append(row);print(json.dumps(row),flush=True)
finally:
 for file,text in originals.items():(root/file).write_text(text)
(root/'evidence/recursive/mutations.json').write_text(json.dumps(rows,indent=2)+'\n')
sys.exit(0 if len(rows)==len(mutants) and all(x['killed'] for x in rows) else 1)
