import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtemp, readFile, writeFile, mkdir, symlink, rm } from 'node:fs/promises';
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

test('generated dialect declarations type-check SDK view authors and reject invalid intents', async t => {
  const cwd = await mkdtemp(join(tmpdir(), 'cbcl-view-types-'));
  t.after(() => rm(cwd, { recursive: true, force: true }));
  await mkdir(join(cwd, 'node_modules'));
  await symlink(join(root, 'js'), join(cwd, 'node_modules/cbcl'), 'dir');
  const source = await readFile(join(root, 'dialects/lunch-vote.cbcl'), 'utf8');
  const poll = await view.generateViewTypes(source);
  await writeFile(join(cwd, 'poll.d.mts'), poll);
  const contract = await object.defineContract({ name: 'typed-colours',
    types: { colour: object.t.oneOf({ keyword: 'red' }, { keyword: 'blue' }) },
    verbs: { open: { after: ['begin'] }, paint: { after: ['open'], fields: { shade: object.optional('colour') } } },
    state: { paints: object.c.count('paint') } });
  const colours = await view.generateViewTypes(contract);
  assert.equal(colours, await view.generateViewTypes(contract.dialect));
  await writeFile(join(cwd, 'colours.d.mts'), colours);
  await writeFile(join(cwd, 'consumer.mts'), `
    import { defineView } from 'cbcl/view';
    import type { Render } from './poll.mjs';
    import type { Render as Paint } from './colours.mjs';
    declare const dialect: string;
    const render: Render = (state, host) => {
      host.emit('vote', { choice: 'Soup' });
      // @ts-expect-error vote requires choice
      host.emit('vote');
      // @ts-expect-error opener belongs to the host
      host.emit('propose', {});
      // @ts-expect-error clock belongs to the host
      host.emit('vote', { choice: 'Soup', clock: 'x' });
      // @ts-expect-error choice is a string
      host.emit('vote', { choice: true });
      // @ts-expect-error no such projection
      return state.missing;
    };
    await defineView({ contract: dialect, view: render });
    const paint: Paint = (state, host) => {
      host.emit('paint');
      host.emit('paint', { shade: { keyword: 'red' } });
      // @ts-expect-error shade is a named one-of
      host.emit('paint', { shade: { keyword: 'pink' } });
      return state.paints.toFixed();
    };
    await defineView({ contract: dialect, view: paint });
  `);
  execFileSync(process.execPath, [join(root, 'js/node_modules/typescript/bin/tsc'), '--strict', '--noEmit',
    '--target', 'ES2022', '--module', 'NodeNext', 'consumer.mts'], { cwd, stdio: 'inherit' });
});
