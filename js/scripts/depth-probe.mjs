// Browser probe for SPEC-001 REQ-046 (BUG-007): drive the built wasm glue in
// real Chromium, Firefox and WebKit and record, per export and depth, what
// the first and second calls throw and whether a benign frame still parses
// on the same instance afterwards. Each depth gets a fresh Blob-isolated
// instance, the loader shape the Chat client uses.
//
//   node js/scripts/depth-probe.mjs <playwright-core dir> [glue dir] > out.txt
//
// Each engine launches Playwright's default build, or the executable named
// by CBCL_PROBE_CHROMIUM / CBCL_PROBE_FIREFOX / CBCL_PROBE_WEBKIT when set
// (a cached build other than the one this playwright-core expects).
//
// <glue dir> defaults to js/src (run `npm run build:wasm` first) and must
// hold cbcl_wasm.js and cbcl_wasm_bg.wasm. Exit status 1 when any call at or
// below the limit fails, any call past it is not a string refusal carrying
// the limit reason, or any benign call after a refusal fails.
import { existsSync } from 'node:fs';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { createRequire } from 'node:module';
import { join, resolve } from 'node:path';

const [pwDir, glueArg] = process.argv.slice(2);
if (!pwDir) { console.error('usage: depth-probe.mjs <playwright-core dir> [glue dir]'); process.exit(2); }
const glueDir = resolve(glueArg ?? new URL('../src', import.meta.url).pathname);
const { chromium, firefox, webkit } = createRequire(import.meta.url)(resolve(pwDir));

const LIMIT = 256;
const DEPTHS = [LIMIT - 1, LIMIT, LIMIT + 1, 3000, 7000, 20000, 100000];
const EXPORTS = ['parse_message', 'read', 'parse'];

const page = `<!doctype html><meta charset="utf-8"><script type="module">
const bytes = async u => new Uint8Array(await (await fetch(u)).arrayBuffer());
const glue = await bytes('/cbcl_wasm.js'), wasm = await bytes('/cbcl_wasm_bg.wasm');
async function fresh() {
  const u = URL.createObjectURL(new Blob([glue], { type: 'text/javascript' }));
  let m; try { m = await import(u); } finally { URL.revokeObjectURL(u); }
  await m.default({ module_or_path: wasm }); return m;
}
const kind = e => typeof e === 'string' ? 'string' : (e?.constructor?.name ?? typeof e);
const call = (f, x) => { try { f(x); return 'ok'; } catch (e) { return kind(e) + ': ' + String(e?.message ?? e).slice(0, 60); } };
const rows = [];
for (const n of ${JSON.stringify(DEPTHS)}) for (const fn of ${JSON.stringify(EXPORTS)}) {
  const m = await fresh(), s = '(tell @room ' + '('.repeat(n - 1) + ')'.repeat(n - 1) + ')';
  rows.push({ fn, n, bytes: s.length, first: call(m[fn], s), second: call(m[fn], s), benignAfter: call(m.parse_message, '(tell @room "hi")') });
}
await fetch('/result', { method: 'POST', body: JSON.stringify({ ua: navigator.userAgent, rows }) });
</script>`;

let deliver;
const server = createServer(async (req, res) => {
  if (req.method === 'POST') {
    let body = ''; for await (const c of req) body += c;
    res.end(); deliver(JSON.parse(body)); return;
  }
  const files = { '/cbcl_wasm.js': 'text/javascript', '/cbcl_wasm_bg.wasm': 'application/wasm' };
  if (files[req.url]) { res.setHeader('content-type', files[req.url]); res.end(await readFile(join(glueDir, req.url))); return; }
  res.setHeader('content-type', 'text/html'); res.end(page);
});
await new Promise(r => server.listen(0, '127.0.0.1', r));
const url = `http://127.0.0.1:${server.address().port}/`;

const OFFSET = '(tell @room '.length + LIMIT - 1;
// The glue reports the parser's reason, prefixed `parse error: ` by the
// message exports; the probe page keeps the first 60 characters.
const REASON = `at byte ${OFFSET}: list nesting exceeds limit ${LIMIT}`;
const refused = (out, fn) => out === 'string: ' + `${fn === 'parse' ? '' : 'parse error: '}${REASON}`.slice(0, 60);
let failed = 0;
console.log(`# glue: ${glueDir}`);
for (const [name, engine] of [['chromium', chromium], ['firefox', firefox], ['webkit', webkit]]) {
  const exe = process.env[`CBCL_PROBE_${name.toUpperCase()}`];
  if (exe && !existsSync(exe)) throw new Error(`${name}: ${exe} does not exist`);
  const browser = await engine.launch(exe ? { executablePath: exe } : {});
  const result = new Promise(r => { deliver = r; });
  const tab = await browser.newPage();
  await tab.goto(url);
  const { ua, rows } = await Promise.race([result, new Promise((_, j) => setTimeout(() => j(new Error('timeout')), 120000))]);
  console.log(`== ${name} ${browser.version()} | ${ua}`);
  for (const r of rows) {
    const good = r.n <= LIMIT
      ? r.first === 'ok' && r.second === 'ok'
      : refused(r.first, r.fn) && refused(r.second, r.fn);
    const verdict = good && r.benignAfter === 'ok' ? 'PASS' : 'FAIL';
    if (verdict === 'FAIL') failed++;
    console.log(`${verdict} ${r.fn.padEnd(13)} depth ${String(r.n).padStart(6)} (${r.bytes} B) | #1 ${r.first} | #2 ${r.second} | benign after -> ${r.benignAfter}`);
  }
  await browser.close();
}
server.close();
console.log(`# ${failed} failed`);
process.exit(failed ? 1 : 0);
