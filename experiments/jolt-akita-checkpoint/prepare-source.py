"""Stage only owned overlay packages into the pinned Jolt workspace."""
import json,shutil,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent
jolt=Path(sys.argv[1]).resolve();cbcl=root.parents[1]
expected='beebf45d829f5aecc5d330f78879cd914e47541e'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=jolt,text=True).strip()==expected
for package in ['common','guest','host']:
 src=root/package
 if not src.exists():continue
 dest=jolt/'.cbcl-overlay'/package
 if dest.exists():shutil.rmtree(dest)
 shutil.copytree(src,dest,ignore=shutil.ignore_patterns('target','__pycache__'))
 if package=='common':
  p=dest/'Cargo.toml';s=p.read_text().replace('../../../crates/cbcl-core',str(cbcl/'crates/cbcl-core')).replace('../../../crates/cbcl-parser',str(cbcl/'crates/cbcl-parser'));p.write_text(s)
fixture_src=cbcl/'experiments/general-kernel-checkpoint/fixtures'
fixture_dest=jolt/'.cbcl-overlay/fixtures'
if fixture_dest.exists():shutil.rmtree(fixture_dest)
shutil.copytree(fixture_src,fixture_dest)
p=jolt/'Cargo.toml';text=p.read_text()
for package in ['common','guest','host']:
 name=f'.cbcl-overlay/{package}'
 if (root/package).exists() and f'"{name}"' not in text:
  text=text.replace('members = [','members = [\n  "'+name+'",',1)
p.write_text(text)
(root/'evidence/jolt-source.json').write_text(json.dumps({'commit':expected,'checkout':str(jolt),'overlayPackages':[p for p in ['common','guest','host'] if (root/p).exists()]},indent=2)+'\n')
