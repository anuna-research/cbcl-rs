#!/usr/bin/env python3
"""Targeted experiment mutations; named assertions must run; always restore sources."""
import json, os, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent
path=root/'program.ts'; original=path.read_text()
mutants=[
 ('unbound-signer-index', 'wrong-signer-index', ["        statePath.calculateIndex().assertEquals(operation.signer.value, 'signer index');"]),
 ('unbound-append-index', 'wrong-append-index', ["        historyPath.calculateIndex().assertEquals(context.before.count.value, 'append index');"]),
 ('unbound-state-path', 'wrong-old-value', ["        statePath.calculateRoot(oldLeaf).assertEquals(context.before.state, 'old state root');"]),
 ('unbound-replacement', 'wrong-replacement', ["        operation.previousLo.assertEquals(head.lo, 'replacement low');", "        operation.previousHi.assertEquals(head.hi, 'replacement high');"]),
]
results=[]
try:
 for name,test,lines in mutants:
  source=original
  for line in lines:
   assert source.count(line)==1, (name,line)
   source=source.replace(line,'        // MUTATION: constraint removed.')
  path.write_text(source)
  try:
   command=['node','--import','tsx','experiment.ts','--only='+test]
   run=subprocess.run(command,cwd=root,env=os.environ,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
  finally: path.write_text(original)
  (root/'evidence'/('mutant-'+name+'.log')).write_text(run.stdout)
  killed=run.returncode!=0 and 'Missing expected rejection' in run.stdout and 'experiment.ts' in run.stdout
  row=dict(name=name,test=test,command=command,exit_code=run.returncode,killed=killed)
  results.append(row); print(json.dumps(row),flush=True)
finally: path.write_text(original)
(root/'evidence/mutations.json').write_text(json.dumps(results,indent=2)+'\n')
sys.exit(0 if len(results)==len(mutants) and all(r['killed'] for r in results) else 1)
