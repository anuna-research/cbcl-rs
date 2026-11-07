"""Mutate only the staged consumer; require named tests to fail, then restore."""
import json,os,pathlib,subprocess
exp=pathlib.Path(__file__).resolve().parent;root=exp.parents[1]
out=pathlib.Path(os.environ.get('CBCL_VOTE_OUTPUT',root/'outputs/private-vote-export')).resolve()
jolt=pathlib.Path(os.environ.get('CBCL_JOLT_SOURCE','/tmp/cbcl-jolt-akita-source'))
cache=os.environ.get('CBCL_JOLT_TARGET','/Users/anuna-02/Code/cbcl-rs-jolt-akita/experiments/jolt-akita-checkpoint/target')
assert json.loads((out/'native-tests-2-run.json').read_text())['exit_code']==0, 'passing native baseline required'
p=jolt/'.vote-overlay/common/src/lib.rs';original=p.read_text();results=[]
mutations=[('message-signature','verify(&p.key, message_digest(&i, r)?, &r.signature)?;','// mutation: omit message authentication','invalid_message_signature'),('closure-unanimity','if i.closure_signatures.len() != i.participants.len() {','if false && i.closure_signatures.len() != i.participants.len() {','missing_closure_signer')]
try:
 for name,old,new,test in mutations:
  assert original.count(old)==1,(name,'mutation target')
  p.write_text(original.replace(old,new))
  command=['cargo','nextest','run','--manifest-path',str(jolt/'Cargo.toml'),'--cargo-profile','build-fast','-p','private-vote-common','--target-dir',cache,'-E','test('+test+')','--offline']
  run=subprocess.run(command,capture_output=True,text=True,timeout=180)
  text=run.stdout+run.stderr;(out/(name+'-mutant.log')).write_text(text)
  killed=run.returncode!=0 and 'panicked at' in text and test in text and 'FAIL' in text
  results.append({'name':name,'test':test,'exit_code':run.returncode,'killed':killed})
  p.write_text(original)
finally:p.write_text(original)
(out/'mutations.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results));assert len(results)==2 and all(r['killed'] for r in results)
