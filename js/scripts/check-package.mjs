// Fail before creating a tarball if an entry point or the matching verifier is missing.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { access, readFile } from 'node:fs/promises';

const pkg = JSON.parse(await readFile('package.json', 'utf8'));
for (const entry of Object.values(pkg.exports)) {
  for (const path of typeof entry === 'string' ? [entry] : Object.values(entry)) await access(path);
}
const wasm = await readFile('dist/cbcl_wasm_bg.wasm');
const provenance = JSON.parse(await readFile('dist/cbcl_wasm.provenance.json', 'utf8'));
assert.equal(createHash('sha256').update(wasm).digest('hex'), provenance.wasmSha256);
await import('cbcl/view');
