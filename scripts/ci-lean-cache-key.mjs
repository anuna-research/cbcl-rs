// Preserve the existing hashFiles digest while exposing hashing as a normal step.
import { createHash } from 'node:crypto';
import { appendFileSync, readFileSync } from 'node:fs';

const hash = createHash('sha256');
for (const path of ['../lean-cbcl/lean-toolchain', './ci-install-lean.sh']) {
  hash.update(createHash('sha256').update(readFileSync(new URL(path, import.meta.url))).digest());
}
const digest = hash.digest('hex');
if (!process.env.GITHUB_OUTPUT) throw new Error('GITHUB_OUTPUT is required for the Lean cache digest');
appendFileSync(process.env.GITHUB_OUTPUT, `digest=${digest}\n`);
console.log(`Lean cache digest: ${digest}`);
