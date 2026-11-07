#!/usr/bin/env python3
"""V2 summary-only guard mutations against an exact cached native library graph.

First build the current library once with CARGO_PROFILE_DEV_DEBUG=0
CARGO_INCREMENTAL=0 cargo build -p cbcl-checkpoint -j 1. This script invokes only
rustc on temporary copies, never mutates shared source and never runs Cargo.
Old v1 scaling/proof reports are not updated or reused as v2 measurements.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-profile', choices=['debug', 'release'], default='debug')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    deps = root / 'target' / args.dependency_profile / 'deps'
    fingerprints = deps.parent / '.fingerprint'
    graphs = []
    for path in fingerprints.glob('cbcl-checkpoint-*/lib-cbcl_checkpoint.json'):
        suffix = path.parent.name.rsplit('-', 1)[1]
        library = deps / f'libcbcl_checkpoint-{suffix}.rlib'
        graph = json.loads(path.read_text())
        if library.exists() and {'cbcl_core', 'serde', 'serde_json'}.issubset({d[1] for d in graph['deps']}):
            graphs.append((path, library, graph))
    if not graphs:
        raise SystemExit('No complete cached native checkpoint library; build first')
    metadata, checkpoint, graph = max(graphs, key=lambda item: item[1].stat().st_mtime)
    externs = ['--extern', f'checkpoint={checkpoint}']
    for _, name, _, expected in graph['deps']:
        if name not in {'cbcl_core', 'serde', 'serde_json'}:
            continue
        libraries = []
        for fingerprint in fingerprints.glob(f'*/lib-{name}'):
            if int.from_bytes(bytes.fromhex(fingerprint.read_text().strip()), 'little') == expected:
                suffix = fingerprint.parent.name.rsplit('-', 1)[1]
                library = deps / f'lib{name}-{suffix}.rlib'
                if library.exists():
                    libraries.append(library)
        if len(libraries) != 1:
            raise SystemExit(f'Cannot resolve exact cached dependency {name}')
        externs += ['--extern', f'{name}={libraries[0]}']
    ed25519 = max(deps.glob('libed25519_dalek-*.rlib'), key=lambda p: p.stat().st_mtime)
    externs += ['--extern', f'ed25519_dalek={ed25519}']
    source = (here / 'summary.rs').read_text()
    mutations = [
        ('drop-covered-duplicate-guard', 'if covered(&act.address) {', 'if false {',
         'covered_replay_cannot_restore_retired_contribution'),
        ('forget-unseen-suppression', 'if writer(r, act) && !suppressed {', 'if writer(r, act) {',
         'all_fourteen_plain_rules_every_prefix_cut_permutation_duplicate'),
        ('allow-invalid-derived-source', 'return Err(Error::Invalid("derived source"));', 'let _ = source;',
         'derived_fields_require_earlier_eligible_materialized_maps'),
        ('retain-cross-scope-pending', 'p.target != act.address',
         'p.target != act.address || p.scope != k',
         'cross_scope_late_nonstate_and_covered_target_pruning'),
        ('skip-snapshot-byte-budget', 'Reader::new(bytes, MAX)?', 'Reader::new(bytes, usize::MAX)?',
         'binary_snapshot_byte_budget_is_checked_before_recognition'),
        ('skip-incoming-metadata-validation', 'record_work(1, 0, 0, 0);\n        check_act(act)?;',
         'record_work(1, 0, 0, 0);', 'malformed_metadata_and_snapshots_fail_before_mutation'),
        ('store-unrelated-event-payload', 'selected_value: value,',
         'selected_value: native(match act.message.innermost_simple().unwrap() { Message::Simple {content,..} => content, _ => unreachable!() }),',
         'events_store_projected_slice_and_derive_histogram_and_sum'),
        ('forget-pair-value-sum', 'Value::Pair { value, .. } => int_value(value),',
         'Value::Pair { .. } => None,', 'all_fourteen_plain_rules_every_prefix_cut_permutation_duplicate'),
    ]
    support = (here / 'test_support.rs').read_text().split('pub fn installed(')[0]
    records = []
    with tempfile.TemporaryDirectory(prefix='cbcl-summary-v2-mutants-') as temporary:
        directory = Path(temporary)
        shutil.copyfile(here / 'summary_tests.rs', directory / 'summary_tests.rs')
        harness = ('extern crate alloc;\n'
                   'pub use checkpoint::{Error,Hash,Result,hash,hex,codec,certificate,member,progress_resume,resource_resume};\n'
                   'mod test_support {\n' + support + '\n}\n'
                   '#[path="summary.rs"] mod summary;\n')
        (directory / 'harness.rs').write_text(harness)
        def compile_summary(text):
            (directory / 'summary.rs').write_text(text)
            build = subprocess.run(['rustc', '--test', '--edition=2021', '--cfg', 'feature="std"',
                                    '-C', 'opt-level=2', '-C', 'debuginfo=0', '-L', f'dependency={deps}',
                                    *externs, str(directory / 'harness.rs'), '-o', str(directory / 'tests')],
                                   text=True, capture_output=True, timeout=60)
            if build.returncode:
                raise SystemExit('Harness/mutant did not compile; not a kill:\n' + build.stderr)
        compile_summary(source)
        baseline = subprocess.run([str(directory / 'tests')], text=True, capture_output=True, timeout=60)
        if baseline.returncode:
            raise SystemExit('Unmutated baseline failed:\n' + baseline.stdout + baseline.stderr)
        print(baseline.stdout, flush=True)
        for name, old, new, test in mutations:
            if source.count(old) != 1:
                raise SystemExit(f'Mutation anchor changed: {name}: {source.count(old)} matches')
            compile_summary(source.replace(old, new))
            trial = subprocess.run([str(directory / 'tests'), test], text=True, capture_output=True, timeout=60)
            killed = trial.returncode != 0 and 'test result: FAILED' in trial.stdout
            record = {'mutation': name, 'test': test, 'compiled': True, 'killed_by_test': killed}
            records.append(record)
            print(json.dumps(record), flush=True)
            if not killed:
                raise SystemExit('Mutant survived or test did not run:\n' + trial.stdout + trial.stderr)
    print(json.dumps({'summary_codec_version': 2, 'dependency_fingerprint': str(metadata.relative_to(root)),
                      'status': 'all compiled mutants killed', 'mutations': records}, indent=2))


if __name__ == '__main__':
    main()
