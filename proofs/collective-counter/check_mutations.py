#!/usr/bin/env python3
"""SPEC-027: isolated behavioral guard mutations, including legacy guards."""
import importlib.util, json, os, pathlib, shutil, subprocess, tempfile
ROOT=pathlib.Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('old_mutations',ROOT/'proofs/rust-quorum/check_mutations.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
ENGINE='crates/cbcl-core/src/quorum/engine.rs'
CONTEXT='crates/cbcl-core/src/quorum/context.rs'
mutations=[(name,ENGINE,a,b,test) for name,a,b,test in old.MUTATIONS]+[
 ('actor-budget',ENGINE,'if op.epoch == epoch {','if op.epoch == epoch && op.act.signer == self.op(extra.as_str())?.act.signer {','collective_sellers_share_one_validator_budget'),
 ('cancel-actor',ENGINE,'VoteKind::CancelRequest, &v.payload, &op.act.signer, auth','VoteKind::CancelRequest, &v.payload, &v.signer, auth','collective_cancellation_uses_original_actor_and_refunds_shared_pool'),
 ('checkpoint-role',CONTEXT,'let Ok(inst) = Instance::new(&self.dialect, self.thread.clone(), &self.genesis) else {','return true;\n        let Ok(inst) = Instance::new(&self.dialect, self.thread.clone(), &self.genesis) else {','collective_ceiling_issuer_and_checkpoint_authorization'),
 ('reserved-scope',CONTEXT,'if cast_keys.contains(COLLECTIVE_POOL) {','if false && cast_keys.contains(COLLECTIVE_POOL) {','collective_reserved_resource_scope_cannot_be_an_authenticated_actor'),
]
def main():
 results=[];outputs=ROOT/'outputs'
 with tempfile.TemporaryDirectory(prefix='cbcl-collective-mutants-') as directory:
  tmp=pathlib.Path(directory)
  for name in ['crates','dialects','test-vectors']:shutil.copytree(ROOT/name,tmp/name)
  for name in ['Cargo.toml','Cargo.lock']:shutil.copy2(ROOT/name,tmp/name)
  originals={name:(tmp/name).read_text() for name in [ENGINE,CONTEXT]}
  env=dict(os.environ,CARGO_TARGET_DIR=str(ROOT/'target/collective-mutations'))
  for label,path,a,b,test in [('baseline',ENGINE,'','','')]+mutations:
   for name,source in originals.items():(tmp/name).write_text(source)
   if a:
    if originals[path].count(a)!=1:raise RuntimeError(f'{label}: ambiguous mutation site')
    (tmp/path).write_text(originals[path].replace(a,b,1))
   cmd=['cargo','test','--offline','-p','cbcl-parser','--test','quorum_runtime','--quiet']
   if test:cmd += [test,'--','--exact']
   run=subprocess.run(cmd,cwd=tmp,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   logfile=f'collective-mutation-{label}.log';(outputs/logfile).write_text(run.stdout)
   passed=run.returncode==0 if label=='baseline' else run.returncode!=0 and 'test result: FAILED' in run.stdout and 'running 1 test' in run.stdout
   results.append(dict(name=label,exit_code=run.returncode,accepted=passed,log=logfile))
   print(label, 'pass' if passed else 'FAIL',flush=True)
   if not passed:print(run.stdout[-2500:],flush=True)
 (outputs/'collective-mutations.json').write_text(json.dumps(results,indent=2)+'\n')
 return 0 if all(r['accepted'] for r in results) else 1
if __name__=='__main__':raise SystemExit(main())
