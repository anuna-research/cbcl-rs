import json,subprocess
from pathlib import Path
host=Path('target/release/checkpoint-host')
for name in ['drawing-0','drawing-1','drawing-8','status-0','status-1','status-8','checklist-role','ancestor-status']:
 out=Path('evidence/matrix')/name
 for mode in ['native','execute']:
  result=subprocess.run([str(host),mode,f'fixtures/{name}.json',str(out)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  print(json.dumps({'case':name,'mode':mode,'exit_code':result.returncode,'output':result.stdout}),flush=True)
  if result.returncode:raise SystemExit(result.returncode)
