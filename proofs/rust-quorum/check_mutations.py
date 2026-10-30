#!/usr/bin/env python3
"""SPEC-026 TEST-2602: run real Rust tests against isolated guard mutations."""
import json, os, pathlib, shutil, subprocess, tempfile
ROOT = pathlib.Path(__file__).resolve().parents[2]
ENGINE = pathlib.Path('crates/cbcl-core/src/quorum/engine.rs')
MUTATIONS = [
    ('quorum', 'c.votes.len() < committee.quorum', 'c.votes.len() < 1', 'signed_domains_distinct_members_and_no_early_effects'),
    ('budget', 'let q = self.context.committee.quorum as i128;', 'let q = 1i128;', 'local_budget_triangle_and_durable_cas'),
    ('fence', 'self.state.fences.contains(id) || !self.has(VoteKind::Operation, id)', 'false || !self.has(VoteKind::Operation, id)', 'cancellation_reclaims_once_and_survives_late_delivery'),
    ('seal', 'self.state.sealed.contains_key(&op.epoch)', 'false', 'nonce_forgery_seals_successor_choice_and_limits'),
    ('successor', 'if chosen != id {', 'if false && chosen != id {', 'nonce_forgery_seals_successor_choice_and_limits'),
    ('release', '!self.state.signed.contains(id) || !self.has(VoteKind::Cancel, id)', '!self.state.signed.contains(id)', 'cancellation_reclaims_once_and_survives_late_delivery'),
    ('coverage', 'self.op(id)?.epoch != m.parent || !m.held.contains(id)', 'self.op(id)?.epoch != m.parent', 'nonce_forgery_seals_successor_choice_and_limits'),
    ('durability', 'if let Err(e) = journal.append(', 'if let Err(e) = Ok::<(),String>(()) { self.state=old; return Err(e); }\n        if let Err(e) = journal.append(', None),
]
# Durability mutation separately replaces actual append with a successful no-op.
MUTATIONS[-1] = ('durability', '''if let Err(e) = journal.append(
            &self.context.id,
            &self.validator,
            Some(self.sequence),
            &event,
        )''', '''if let Err(e) = Ok::<(),String>(())''', 'local_budget_triangle_and_durable_cas')

def main():
    outputs=ROOT/'outputs'; outputs.mkdir(exist_ok=True)
    results=[]
    with tempfile.TemporaryDirectory(prefix='cbcl-rust-quorum-') as name:
        tmp=pathlib.Path(name)
        for directory in ['crates','dialects','test-vectors']:
            shutil.copytree(ROOT/directory,tmp/directory)
        for filename in ['Cargo.toml','Cargo.lock']:
            shutil.copy2(ROOT/filename,tmp/filename)
        env=dict(os.environ,CARGO_TARGET_DIR=str(ROOT/'target/rust-quorum-mutations'))
        source=(tmp/ENGINE).read_text()
        for label,old,new,test in [('baseline','','','')]+MUTATIONS:
            if old and source.count(old)!=1:
                raise RuntimeError(f'{label}: expected one mutation location, got {source.count(old)}')
            (tmp/ENGINE).write_text(source.replace(old,new,1) if old else source)
            cmd=['cargo','test','--offline','-p','cbcl-parser','--test','quorum_runtime','--quiet']
            if test: cmd += [test,'--','--exact']
            run=subprocess.run(cmd,cwd=tmp,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            (outputs/f'rust-quorum-mutation-{label}.log').write_text(run.stdout)
            # A compiler error is NOT a killed behavioral mutant.
            expected=(run.returncode==0) if label=='baseline' else (run.returncode!=0 and 'test result: FAILED' in run.stdout and 'running 1 test' in run.stdout)
            results.append(dict(name=label,exit_code=run.returncode,accepted=expected,log=f'rust-quorum-mutation-{label}.log'))
            print(f'{label}: {"pass" if expected else "FAIL"}',flush=True)
            if not expected: print(run.stdout[-3000:],flush=True)
    (outputs/'rust-quorum-mutations.json').write_text(json.dumps(results,indent=2)+'\n')
    return 0 if all(x['accepted'] for x in results) else 1
if __name__=='__main__': raise SystemExit(main())
