#!/usr/bin/env python3
"""Two legacy policy-fault parity checks using exact cached native libraries.

Never runs Cargo or edits production sources. Lean receives no Rust outcomes.
This is not an account/quorum verifier, admission, extraction or byte-proof check.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean-cbcl'
ORACLE = LEAN / 'CheckpointResourcePolicyOracle.lean'
RUST = r'''
use checkpoint::summary::Summary;
use cbcl_core::{message::{Message,Performative,CorePerformative},sexpr::{Atom,SExpr},state::{self,Act,Entry,Rule,StateClause}};
use serde_json::{json,Value};
use std::collections::BTreeSet;
fn act(n: usize)->Act {
 Act::from_message(Message::Simple {performative:Performative::Core(CorePerformative::Tell),recipient:None,
 content:SExpr::Atom(Atom::Str(format!("typed-{n}"))),params:vec![],thread:None,sender:Some("@typed".into()),caused_by:None},"@typed").unwrap()
}
fn main(){
 let mut rows=Vec::new();
 for (policy,source) in [("collective",include_str!(concat!(env!("POLICY_REPO_ROOT"),"/dialects/example-collective-tickets.cbcl"))),
 ("quorum",include_str!(concat!(env!("POLICY_REPO_ROOT"),"/dialects/example-quorum-coin.cbcl")))] {
  let sx=cbcl_parser::parse(source).unwrap();
  let registry=cbcl_parser::parse_and_install_dialect(&sx).unwrap();
  let dialect=registry.iter().last().unwrap();
  let resource=dialect.state.as_ref().unwrap().fields().find_map(|(_,r)|match r{Rule::BoundedCounter(c)=>Some(c.clone()),_=>None}).unwrap();
  assert_eq!(resource.ownership==cbcl_core::escrow::Ownership::Collective,policy=="collective");
  if policy=="quorum" {assert!(resource.certification.is_quorum());}
  let clause=StateClause{entries:vec![Entry::Field{name:"resource".into(),rule:Rule::BoundedCounter(resource)}]};
  let history=vec![act(1),act(2),act(1)];
  for prefix in 0..=history.len(){
   let h=&history[..prefix];
   let native=state::fold(&clause,None,h).remove(0).1;
   let native_json:Value=serde_json::from_str(&native.render()).unwrap();
   for cut in 0..=prefix{
    let mut summary=Summary::new(&clause,None).unwrap();let mut coverage=BTreeSet::new();
    for a in &h[..cut]{summary.apply(a,|id|coverage.contains(id)).unwrap();coverage.insert(a.address.clone());}
    let bytes=summary.encode();
    let mut resumed=Summary::decode_for(&bytes,&clause,None).unwrap();
    for a in &h[cut..]{resumed.apply(a,|id|coverage.contains(id)).unwrap();coverage.insert(a.address.clone());}
    let checkpoint=resumed.render().remove(0).1;
    assert_eq!(native,checkpoint,"policy={policy},prefix={prefix},cut={cut}");
    rows.push(json!({"policy":policy,"prefix":prefix,"cut":cut,"observation":native_json,
     "checkpoint_observation":serde_json::from_str::<Value>(&checkpoint.render()).unwrap()}));
   }
  }
 }
 println!("{}",serde_json::to_string(&rows).unwrap());
}
'''

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def graph(profile):
    deps = ROOT / 'target' / profile / 'deps'
    fingerprints = deps.parent / '.fingerprint'
    candidates = []
    for path in fingerprints.glob('cbcl-checkpoint-*/lib-cbcl_checkpoint.json'):
        lib = deps / ('libcbcl_checkpoint-' + path.parent.name.rsplit('-', 1)[1] + '.rlib')
        data = json.loads(path.read_text())
        if lib.is_file() and {'cbcl_core', 'cbcl_parser', 'serde_json'} <= {d[1] for d in data['deps']}:
            candidates.append((path, lib, data))
    if not candidates:
        raise ValueError('No complete native cached graph; parent must build the current crate first')
    metadata, library, data = max(candidates, key=lambda c: c[1].stat().st_mtime_ns)
    libraries = {'checkpoint': library}
    for _, name, _, expected in data['deps']:
        if name not in {'cbcl_core', 'cbcl_parser', 'serde_json'}:
            continue
        found = []
        for fp in fingerprints.glob('*/lib-' + name):
            if int.from_bytes(bytes.fromhex(fp.read_text().strip()), 'little') == expected:
                lib = deps / ('lib' + name + '-' + fp.parent.name.rsplit('-', 1)[1] + '.rlib')
                if lib.is_file():
                    found.append(lib)
        if len(found) != 1:
            raise ValueError('Exact cached dependency resolution failed: ' + name)
        libraries[name] = found[0]
    return deps, metadata, libraries


def run(cmd, cwd, timeout, env=None):
    p = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)
    return {'command': [str(c) for c in cmd], 'cwd': str(cwd), 'exit_code': p.returncode,
            'stdout': p.stdout, 'stderr': p.stderr}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-profile', choices=['debug', 'release'], default='debug')
    parser.add_argument('--output', type=Path, default=ROOT / 'proofs/cached-checkpoints/all16-resource-policy-parity.json')
    parser.add_argument('--timeout', type=float, default=60)
    args = parser.parse_args()
    report = {'schema_version': 1, 'recorded_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'passed': False, 'scope': 'Two legacy configuration-policy constants only; not the general account/quorum verifier, extraction, admission or cryptography.',
              'lean_receives_rust_outputs': False, 'cargo_invoked': False,
              'input_contract': 'Identity-consistent typed dummy acts; no admission or signature claim for these irrelevant-to-policy histories.',
              'runs': []}
    tracked = [Path(__file__), ORACLE, ROOT / 'crates/cbcl-checkpoint/src/summary.rs',
               ROOT / 'crates/cbcl-checkpoint/src/resource_resume.rs', ROOT / 'crates/cbcl-core/src/escrow.rs',
               ROOT / 'dialects/example-collective-tickets.cbcl', ROOT / 'dialects/example-quorum-coin.cbcl',
               LEAN / 'LeanCbcl/CheckpointEvidence.lean']
    try:
        deps, metadata, libraries = graph(args.dependency_profile)
        tracked += [metadata, *libraries.values()]
        tracked += list((LEAN / '.lake/build/lib/lean/LeanCbcl').glob('*.olean'))
        initial = {str(p.relative_to(ROOT)): sha(p) for p in tracked}
        report['source_and_cached_graph_sha256'] = initial
        report['cached_dependency_fingerprint'] = str(metadata.relative_to(ROOT))
        with tempfile.TemporaryDirectory(prefix='cbcl-resource-policy-ports-') as tmp:
            source = Path(tmp) / 'policy.rs'
            binary = Path(tmp) / 'policy'
            source.write_text(RUST)
            externs = []
            for name, library in libraries.items():
                externs += ['--extern', f'{name}={library}']
            build = run(['rustc', '--edition=2021', '-C', 'debuginfo=0', '-L', f'dependency={deps}',
                         *externs, str(source), '-o', str(binary)], ROOT, args.timeout,
                        dict(os.environ, POLICY_REPO_ROOT=str(ROOT)))
            report['runs'].append(build)
            if build['exit_code']:
                raise ValueError('Native cached driver compilation failed')
            native = run([str(binary)], ROOT, args.timeout)
            report['runs'].append(native)
            if native['exit_code']:
                raise ValueError('Native full-fold/checkpoint comparison failed')
            lean = run(['lake', 'env', 'lean', '--run', str(ORACLE)], LEAN, args.timeout)
            report['runs'].append(lean)
            if lean['exit_code']:
                raise ValueError('Independent Lean policy port failed')
            native_rows = json.loads(native['stdout'])
            lean_rows = json.loads(lean['stdout'])
            expected = {(p,n,c) for p in ['collective','quorum'] for n in range(4) for c in range(n+1)}
            def indexed(rows):
                out = {}
                for row in rows:
                    key = (row['policy'],row['prefix'],row['cut'])
                    if key in out: raise ValueError('Duplicate parity query')
                    out[key] = row['observation']
                if set(out) != expected: raise ValueError('Incomplete or extraneous policy/prefix/cut inventory')
                return out
            if indexed(native_rows) != indexed(lean_rows):
                raise ValueError('Rust/Lean legacy policy port mismatch')
            report.update(native_rows=native_rows, lean_rows=lean_rows, comparisons=len(expected), policies=sorted({k[0] for k in expected}))
            report['source_drift'] = [str(p.relative_to(ROOT)) for p in tracked if sha(p) != initial[str(p.relative_to(ROOT))]]
            report['passed'] = not report['source_drift']
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        report['error'] = str(error)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'passed': report['passed'], 'comparisons':report.get('comparisons'), 'error':report.get('error'), 'report':str(args.output)}))
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
