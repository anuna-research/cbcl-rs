"""Reversible output-artifact regression checks; never generates proofs."""
import subprocess,json,shutil
from pathlib import Path
root=Path('.artifacts/artifact-check');root.mkdir(parents=True,exist_ok=True)
receipt=Path('evidence/proved-drawing-1-tuned/receipt.bin');out=root/'in-place';out.mkdir(exist_ok=True)
copy=out/'receipt.bin';shutil.copyfile(receipt,copy);before=copy.read_bytes()
run=subprocess.run(['target/release/checkpoint-host','compress',str(copy),str(out)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
assert run.returncode and 'use a distinct receipt output path' in run.stdout,run.stdout
assert copy.read_bytes()==before,'in-place check deleted or changed source'
results={'inPlaceCompressionRefusedBeforeDeletion':True}
for mode,filename in [('prove','bad.json'),('compress','bad.bin')]:
 input_path=root/filename;input_path.write_text('{bad')
 out=root/mode;out.mkdir(exist_ok=True)
 for name in ['receipt.bin',f'{mode}-metrics.json']:(out/name).write_text('stale')
 run=subprocess.run(['target/release/checkpoint-host',mode,str(input_path),str(out)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 assert run.returncode,'invalid input unexpectedly succeeded'
 assert not (out/'receipt.bin').exists(),'stale receipt survived'
 assert not (out/f'{mode}-metrics.json').exists(),'stale success metrics survived'
 results[f'{mode}FailureClearsOldArtifacts']=True
Path('evidence/cli-artifact-check.json').write_text(json.dumps(results,indent=2)+'\n')
