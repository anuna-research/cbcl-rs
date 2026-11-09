import test from 'node:test';
import assert from 'node:assert/strict';
import { copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'lean-cache-key-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, 'scripts'));
  mkdirSync(join(root, 'lean-cbcl'));
  const script = join(root, 'scripts/ci-lean-cache-key.mjs');
  copyFileSync(new URL('./ci-lean-cache-key.mjs', import.meta.url), script);
  writeFileSync(join(root, 'lean-cbcl/lean-toolchain'), 'leanprover/lean4:v4.27.0\n');
  writeFileSync(join(root, 'scripts/ci-install-lean.sh'), '#!/bin/sh\nexit 0\n');
  const output = join(root, 'output');
  return { root, output, run: () => spawnSync(process.execPath, [script], {
    cwd: tmpdir(), env: { ...process.env, GITHUB_OUTPUT: output }, encoding: 'utf8',
  }) };
}

test('preserves the known hashFiles digest independently of working directory', t => {
  const f = fixture(t);
  const run = f.run();
  assert.equal(run.status, 0, run.stderr);
  assert.equal(readFileSync(f.output, 'utf8'), 'digest=5c9f5fcd2bc7e4f1eaca70d3d8c163ef017e9d7fc01d7370404ecbbc78b45ea0\n');
});

test('both toolchain and installer contents invalidate the cache', t => {
  const f = fixture(t);
  assert.equal(f.run().status, 0);
  const original = readFileSync(f.output, 'utf8');
  for (const path of ['lean-cbcl/lean-toolchain', 'scripts/ci-install-lean.sh']) {
    const originalFile = readFileSync(join(f.root, path));
    writeFileSync(join(f.root, path), 'changed\n');
    writeFileSync(f.output, '');
    const run = f.run();
    assert.equal(run.status, 0, run.stderr);
    assert.notEqual(readFileSync(f.output, 'utf8'), original);
    writeFileSync(join(f.root, path), originalFile);
  }
});

test('missing input fails before publishing any digest', t => {
  const f = fixture(t);
  rmSync(join(f.root, 'scripts/ci-install-lean.sh'));
  const run = f.run();
  assert.notEqual(run.status, 0);
  assert.match(run.stderr, /ci-install-lean\.sh/);
  assert.equal(existsSync(f.output), false);
});

// Runner output records must be newline-delimited, including when appended.
test('publishes a parseable output record after an existing record', t => {
  const f = fixture(t);
  writeFileSync(f.output, 'previous=ok\n');
  const run = f.run();
  assert.equal(run.status, 0, run.stderr);
  const records = readFileSync(f.output, 'utf8').split('\n');
  assert.equal(records.length, 3);
  assert.equal(records[0], 'previous=ok');
  assert.match(records[1], /^digest=[0-9a-f]{64}$/);
  assert.equal(records[2], '');
});
