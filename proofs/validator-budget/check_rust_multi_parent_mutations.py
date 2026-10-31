#!/usr/bin/env python3
"""SPEC-030: exercise real Rust guard mutants in an isolated archived checkout.

Every case has a separate Cargo target directory. No working source is mutated.
A kill requires a running test assertion failure; compiler/import failures fail
this checker rather than counting as success.
"""
import io
import hashlib
import json
import os
import shutil
from pathlib import Path
import subprocess
import tarfile
import tempfile

ROOT=Path(__file__).resolve().parents[2]
ENGINE='crates/cbcl-core/src/quorum/engine.rs'
CONTEXT='crates/cbcl-core/src/quorum/context.rs'
FILES=[ENGINE,CONTEXT,'crates/cbcl-core/src/quorum/types.rs',
       'crates/cbcl-parser/tests/quorum_runtime.rs',
       'crates/cbcl-parser/tests/quorum_runtime/multi_parent.rs',
       'test-vectors/quorum/multi-parent-lean.json']
original={name:(ROOT/name).read_text() for name in FILES}
engine=original[ENGINE]
budget_start=engine.index('        if used.rights.checked_mul(q)')
budget_end=engine.index('            return Err("local validator budget exceeded"',budget_start)
budget_guard=engine[budget_start:budget_end]
cases=[('control',ENGINE,'',''),
       ('parent-scope',ENGINE,'parent.account != m.account','false'),
       ('held-scope',ENGINE,'if op.account != m.account','if false'),
       ('scope-history',ENGINE,'self.op(signed)?.account == m.account && !m.held.contains(signed)',
        '!m.held.contains(signed)'),
       ('history',ENGINE,'if self.op(signed)?.account == m.account && !m.held.contains(signed)', 'if false'),
       ('books',ENGINE,'if self.allocation(m)? != m.allocation','if false'),
       ('parent',ENGINE,'if !m.parents.contains(current)','if false'),
       ('release',ENGINE,'if !self.state.signed.contains(id) || !self.has(VoteKind::Cancel, id)',
        'if !self.state.signed.contains(id)'),
       ('budget',ENGINE,budget_guard,'        if false {\n'),
       ('domain',CONTEXT,'text("cbcl/quorum-context/multi-parent/v1")',
        'text("cbcl/quorum-context/v1")'),
       ('durability',ENGINE,'        if self.sequence >= self.limits.events {',
        '        if matches!(event, Event::AdoptVersion(_)) { return Ok(()); }\n        if self.sequence >= self.limits.events {')]
results=[]
archive=subprocess.run(['git','archive','HEAD'],cwd=ROOT,check=True,capture_output=True).stdout
with tempfile.TemporaryDirectory(prefix='cbcl-rust-dag-mutations-') as temp:
    base=Path(temp); checkout=base/'source'; checkout.mkdir()
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        # Input is this repository's own git archive, never an external tarball.
        tar.extractall(checkout)
    for name,body in original.items():
        (checkout/name).parent.mkdir(parents=True,exist_ok=True)
        (checkout/name).write_text(body)
    for name,file,before,after in cases:
        for changed in [ENGINE,CONTEXT]: (checkout/changed).write_text(original[changed])
        if before:
            if original[file].count(before)!=1: raise SystemExit(f'{name}: ambiguous mutation marker')
            (checkout/file).write_text(original[file].replace(before,after,1))
        env=dict(os.environ,CARGO_TARGET_DIR=str(base/f'target-{name}'),CARGO_BUILD_JOBS='4',
                 CARGO_PROFILE_TEST_DEBUG='0',CARGO_INCREMENTAL='0')
        run=subprocess.run(['cargo','test','-p','cbcl-parser','--test','quorum_runtime','multi_parent','--','--nocapture'],
                           cwd=checkout,env=env,capture_output=True,text=True,timeout=300)
        output=run.stdout+run.stderr
        test_failure='test result: FAILED' in output and 'panicked at' in output
        passed=run.returncode==0 if name=='control' else run.returncode!=0 and test_failure
        if not passed:
            print(output,file=__import__('sys').stderr)
        results.append({'mutation':name,'exit_code':run.returncode,'actual_assertion_failure':test_failure,
                        'expected_result':passed,'output_sha256':hashlib.sha256(output.encode()).hexdigest(),
                        'test_results':[line for line in output.splitlines() if line.startswith('test result:')]})
        print(f'{name}: {"expected" if passed else "UNEXPECTED"}',file=__import__('sys').stderr,flush=True)
        shutil.rmtree(base/f'target-{name}')
report={'passed':all(r['expected_result'] for r in results),'results':results}
print(json.dumps(report,indent=2))
raise SystemExit(0 if report['passed'] else 1)
