import hashlib,json,platform,subprocess
from pathlib import Path
source={}
for base in ['../../crates/cbcl-core','../../crates/cbcl-parser','common','methods','host']:
 for p in sorted(Path(base).rglob('*.rs')):
  if 'target' not in p.parts:source[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
for p in [Path('Cargo.lock'),Path('methods/guest/Cargo.lock')]:
 source[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
image=Path('target/riscv-guest/checkpoint-methods/checkpoint_guest/riscv32im-risc0-zkvm-elf/release/checkpoint_guest.bin')
metadata={'kernelRevision':subprocess.check_output(['git','rev-parse','c45b468^{commit}'],text=True).strip(),'sourceFiles':source,'guestImageSha256':hashlib.sha256(image.read_bytes()).hexdigest(),'machine':subprocess.check_output(['sysctl','-n','machdep.cpu.brand_string'],text=True).strip(),'memoryBytes':int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True)),'os':platform.platform(),'sdk':'3.0.6','toolchain':subprocess.check_output(['/Users/anuna-02/.risc0/bin/rzup','show'],text=True),'timingConditions':'Shared workstation. Small fixture compilation and execution checks overlapped proving. Initial Rayon setting1; tuned setting4; internal backend threads and GPU behavior not independently characterized. No dedicated-machine performance guarantee.'}
Path('evidence/environment.json').write_text(json.dumps(metadata,indent=2)+'\n')
