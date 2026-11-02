#!/usr/bin/env python3
"""Kernel-check model counterexamples and negative controls; no runtime proof."""
from pathlib import Path
import json,hashlib,subprocess,tempfile,re
p=Path(__file__).resolve().parent;root=p.parents[1]
b=json.loads((p/'baseline.json').read_text())
for f,h in b['files'].items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h,f
cases=[('ResidualBalanceAudit.lean','cost := fun _ _ => 1','cost := fun _ _ => 0'),('CancellationRaceAudit.lean','.effect 0 0, .fence 0 1, .fence 0 2','.effect 0 0, .effect 0 1, .effect 0 2')]
results=[]
for name,old,new in cases:
 source=p/name;raw=source.read_text();assert old in raw
 passed=subprocess.run(['lake','env','lean',str(source)],cwd=root/'lean-cbcl',capture_output=True,text=True,timeout=60)
 output=passed.stdout+passed.stderr;(p/(name+'.log')).write_text(output)
 assert passed.returncode==0,output
 assert 'sorryAx' not in output and not re.search(r'\bsorry\b|\badmit\b',raw),name
 assert 'depends on axioms' in output,name
 fd=tempfile.NamedTemporaryFile(mode='w',suffix='.lean',prefix='cbcl-liveness-mutant-',delete=False)
 try:
  mutant=Path(fd.name);fd.write(raw.replace(old,new,1));fd.close()
  failed=subprocess.run(['lake','env','lean',str(mutant)],cwd=root/'lean-cbcl',capture_output=True,text=True,timeout=60)
  rejected=failed.stdout+failed.stderr;(p/(name+'.mutant.log')).write_text(rejected)
  assert failed.returncode!=0 and 'error:' in rejected,rejected
  assert 'unknown module' not in rejected.lower() and 'no such file' not in rejected.lower(),rejected
 finally:mutant.unlink(missing_ok=True)
 results.append({'audit':name,'kernel_passed':True,'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'negative_control':{'replacement':new,'rejected':True,'scope':'Changed cost or removed cancellation split; proof must no longer typecheck.'}})
report={'passed':True,'audits':results,'limitations':'Ideal current-model counterexamples; no replacement protocol implemented, no universal Rust/network refinement, no general impossibility theorem.'}
(p/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
