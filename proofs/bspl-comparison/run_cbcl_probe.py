#!/usr/bin/env python3
"""Run after cargo build -p cbcl-parser; links newest emitted local artifacts."""
from pathlib import Path
import subprocess,json,hashlib
root=Path(__file__).resolve().parents[2];ev=Path(__file__).resolve().parent
core=max((root/'target/debug/deps').glob('libcbcl_core*.rlib'),key=lambda x:x.stat().st_mtime)
parser=root/'target/debug/libcbcl_parser.rlib'
cmd=['rustc','--edition=2021',str(ev/'probe_cbcl.rs'),'-L',f'dependency={root}/target/debug/deps','--extern',f'cbcl_core={core}','--extern',f'cbcl_parser={parser}','-o','/private/tmp/cbcl-bspl-probe']
build=subprocess.run(cmd,capture_output=True,text=True)
record={'command':cmd,'exit':build.returncode,'stderr':build.stderr,'artifact_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [core,parser]}}
(ev/'cbcl-probe-build.json').write_text(json.dumps(record,indent=2)+'\n');build.check_returncode()
run=subprocess.run(['/private/tmp/cbcl-bspl-probe'],capture_output=True,text=True);run.check_returncode();(ev/'cbcl-probe-results.txt').write_text(run.stdout)
assert 'changed_price_missing_quote=Unknown' in run.stdout
assert 'changed_price_with_quote=Valid' in run.stdout
assert 'changed_price_shape_ok=true' in run.stdout
assert 'NotCausallyLocal' in run.stdout
print(run.stdout)
