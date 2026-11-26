import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtemp, readFile, mkdir, symlink, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import test from 'node:test';
import * as cbcl from 'cbcl';
import * as object from 'cbcl/object';
import * as view from 'cbcl/view';

const root = fileURLToPath(new URL('../../', import.meta.url));
const guide = await readFile(join(root, 'js/README.md'), 'utf8');
const tutorial = await readFile(join(root, 'docs/tutorials/lunch-vote.md'), 'utf8');

function snippet(markdown, label, language) {
  const marker = '<!-- runnable: ' + label + ' -->\n```' + language + '\n';
  const start = markdown.indexOf(marker);
  assert.notEqual(start, -1, label);
  const end = markdown.indexOf('\n```', start + marker.length);
  assert.notEqual(end, -1, label);
  return markdown.slice(start + marker.length, end);
}

test('documented SDK imports and reading and state functions are public exports', () => {
  const modules = { cbcl, 'cbcl/object': object, 'cbcl/view': view };
  for (const [, names, entry] of guide.matchAll(/import\s*\{([^}]+)\}\s*from '(cbcl(?:\/(?:object|view))?)'/g)) {
    for (const name of names.split(',').map(n => n.trim())) {
      assert.ok(Object.hasOwn(modules[entry], name), entry + ' export ' + name);
    }
  }
  for (const task of ['Read an S-expression', 'Work with state frames']) {
    const row = guide.split('\n').find(line => line.startsWith('| ' + task + ' |'));
    assert.ok(row, task);
    for (const [, name] of row.matchAll(/`([\w]+)`/g)) assert.equal(typeof cbcl[name], 'function', name);
  }
});

test('the SDK guide writes a dialect and reads it back', async t => {
  const cwd = await mkdtemp(join(tmpdir(), 'cbcl-sdk-docs-'));
  t.after(() => rm(cwd, { recursive: true, force: true }));
  await mkdir(join(cwd, 'node_modules'));
  await symlink(join(root, 'js'), join(cwd, 'node_modules/cbcl'), 'dir');
  const output = execFileSync(process.execPath, ['--input-type=module'], {
    cwd, input: snippet(guide, 'dialect-file', 'js'), encoding: 'utf8',
  });
  assert.equal(output.trim(), 'true decimal');
});

test('the lunch-vote tutorial produces its documented output with the edited dialect', async t => {
  const tmp = await mkdtemp(join(tmpdir(), 'cbcl-vote-docs-'));
  t.after(() => rm(tmp, { recursive: true, force: true }));
  const output = execFileSync('sh', ['-eu', '-c', snippet(tutorial, 'lunch-vote', 'sh')], {
    cwd: root, env: { ...process.env, TMPDIR: tmp }, encoding: 'utf8',
  });
  const expected = tutorial.match(/Expected output:\n\n```text\n([^]*?)\n```/);
  assert.ok(expected);
  assert.equal(output.trimEnd(), expected[1]);
});
