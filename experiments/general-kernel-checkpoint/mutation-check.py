"""Isolated native mutants: never changes the guest's source or proving image."""
import json,os,shutil,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent
base=(root/'common/src/lib.rs').read_text()
mutants={
 'context':('context(&message, &dialect.name, &identity)?;', '/* omitted dialect check */'),
 'thread':('if simple.thread() != Some(input.thread.as_str()) {','if false {'),
 'admission':('Admission::Rejected(reason) => return Err(format!("rejected: {reason}")),','Admission::Rejected(_reason) => accepted.push(act),'),
 'source-commitment':('&[input.dialect.as_bytes()]','&[b"omitted"]'),
 'snapshot-commitment':('state.as_bytes()', 'b"omitted"'),
}
targets={'context':'nested_dialect_mismatch_rejected','thread':'mixed_thread_rejected','admission':'invalid_shape_rejected','source-commitment':'source_closure_and_message_set_bound','snapshot-commitment':'source_closure_and_message_set_bound'}
baseline=subprocess.run(['cargo','test','--release','-p','checkpoint-common','--test','checkpoint'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env={**os.environ,'CARGO_BUILD_JOBS':'1'})
(root/'evidence/mutation-baseline.log').write_text(baseline.stdout)
assert baseline.returncode==0,'mutation baseline must pass before mutants are meaningful'
results=[]
for name,(before,after) in mutants.items():
 assert base.count(before)==1,(name,'mutation must target exactly one original clause')
 directory=root/'.mutation-runs'/name
 if directory.exists():shutil.rmtree(directory)
 shutil.copytree(root/'common',directory/'common')
 shutil.copytree(root/'fixtures',directory/'fixtures')
 source=directory/'common/src/lib.rs';source.write_text(base.replace(before,after))
 manifest=directory/'common/Cargo.toml';text=manifest.read_text()
 text=text.replace('../../../crates/cbcl-core',str(root.parents[1]/'crates/cbcl-core')).replace('../../../crates/cbcl-parser',str(root.parents[1]/'crates/cbcl-parser'))
 manifest.write_text(text+'\n[workspace]\n')
 result=subprocess.run(['cargo','test','--release','--manifest-path',str(manifest),'--test','checkpoint',targets[name],'--','--exact'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env={**os.environ,'CARGO_BUILD_JOBS':'1','CARGO_TARGET_DIR':str(root/'target')})
 (root/f'evidence/mutant-{name}.log').write_text(result.stdout)
 killed=result.returncode!=0 and 'test result: FAILED' in result.stdout
 results.append({'mutant':name,'killed_by_executed_test':killed,'exit_code':result.returncode,'target_test':targets[name]})
 if not killed:raise SystemExit(f'mutant not killed by an executed assertion: {name}')
(root/'evidence/mutation-results.json').write_text(json.dumps(results,indent=2)+'\n')

assert (root/'common/src/lib.rs').read_text()==base,'original guest source changed'
