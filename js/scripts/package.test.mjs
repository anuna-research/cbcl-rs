import test from 'node:test';
import { checkBusExecutor } from './bus-executor-check.mjs';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createServer } from 'node:http';
import { mkdtemp, mkdir, readdir, cp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';
import { chromium } from 'playwright-core';

const root = fileURLToPath(new URL('../', import.meta.url));
test('packed SDK runs in clean Node, TypeScript and Chromium consumers', async t => {
  const work = await mkdtemp(join(tmpdir(), 'cbcl-packed-'));
  t.after(() => rm(work, { recursive: true, force: true }));
  execFileSync('npm', ['pack', '--pack-destination', work], { cwd: root, env: { ...process.env, npm_config_loglevel: 'silent' } });
  const tarballs = (await readdir(work)).filter(name => name.endsWith('.tgz'));
  assert.equal(tarballs.length, 1);
  const app = join(work, 'app');
  await mkdir(app);
  execFileSync('npm', ['install', '--offline', '--ignore-scripts', '--no-audit', '--no-fund', join(work, tarballs[0])], { cwd: app });
  const pkg = join(app, 'node_modules/cbcl');
  const tutorial = execFileSync(process.execPath, [join(pkg, 'examples/lunch-vote.mjs')], { cwd: app, encoding: 'utf8' });
  assert.match(tutorial, /Tally: \{"Sushi":1\}/);
  await writeFile(join(app, 'consumer.mts'), `
    import { ready, installDialect } from 'cbcl';
    import { c, createRuntime, defineContract } from 'cbcl/object';
    import { defaultPresentation, generateViewTypes, importBundle, exportBundle } from 'cbcl/view';
    await ready();
    const contract = await defineContract({ name: 'example', verbs: { open: { after: ['begin'] } }, state: { opens: c.count('open') } });
    const handle = installDialect(contract.dialect);
    const view = await defaultPresentation(handle);
    if (createRuntime(handle).info.opener !== 'open') throw Error('Unexpected opener');
    if ((await importBundle(exportBundle(view, contract))).presentation.id !== view.id) throw Error('Bundle ID mismatch');
    if (!(await generateViewTypes(handle)).includes('ViewState')) throw Error('Missing generated declaration');
  `);
  execFileSync(process.execPath, [join(root, 'node_modules/typescript/bin/tsc'), '--module', 'nodenext', '--target', 'es2022', '--strict', 'consumer.mts'], { cwd: app });
  execFileSync(process.execPath, ['consumer.mjs'], { cwd: app });
  await build({ entryPoints: [join(root, 'scripts/package-browser.mjs')], outfile: join(app, 'browser.js'),
    bundle: true, platform: 'browser', format: 'esm', external: ['cbcl', 'cbcl/*'] });
  const imports = { cbcl: '/node_modules/cbcl/dist/index.js', 'cbcl/view': '/node_modules/cbcl/dist/view/index.js' };
  await writeFile(join(app, 'index.html'), '<script type="importmap">' + JSON.stringify({ imports }) + '</script>');
  let wasmRequests = 0;
  const server = createServer(async (req, res) => {
    const path = resolve(app, '.' + new URL(req.url, 'http://localhost').pathname);
    if (!path.startsWith(app + sep)) { res.writeHead(404).end(); return; }
    if (path.endsWith('/cbcl_wasm_bg.wasm') && ++wasmRequests === 1) { res.writeHead(503).end(); return; }
    try {
      const bytes = await readFile(path);
      const type = path.endsWith('.wasm') ? 'application/wasm' : path.endsWith('.js') ? 'text/javascript' : 'text/html';
      res.writeHead(200, { 'Content-Type': type }).end(bytes);
    } catch { res.writeHead(404).end(); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  t.after(() => server.close());
  const browser = await chromium.launch({ executablePath: process.env.CHROMIUM_EXECUTABLE_PATH });
  t.after(() => browser.close());
  const page = await browser.newPage();
  await page.goto('http://127.0.0.1:' + server.address().port + '/index.html');
  const result = await page.evaluate(async source => (await import('/browser.js')).checkBrowser(source),
    await readFile(join(pkg, 'dist/lunch-vote.cbcl'), 'utf8'));
  assert.deepEqual(result, { seen: [1, 2], revoked: true, cleaned: true, disposed: true, subscribed: false });
  assert.equal(wasmRequests, 2);
  // Optional compatibility run with the separately maintained bus executor.
  if (process.env.CBCL_BUS_VIEW_RUNTIME) {
    await cp(process.env.CBCL_BUS_VIEW_RUNTIME, join(app, 'bus-runtime'), { recursive: true });
    const text = await readFile(join(pkg, 'dist/lunch-vote.cbcl'), 'utf8');
    const bus = await page.evaluate(checkBusExecutor, text);
    assert.deepEqual(bus, { url: 'https://example.org/echo', revoked: true });
  }
});
