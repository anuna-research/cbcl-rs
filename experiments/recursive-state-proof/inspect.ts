import { writeFile } from 'node:fs/promises';
import { setNumberOfWorkers } from 'o1js';
import { makeProgram } from './program.js';
import { publicKeys } from './helpers.js';
setNumberOfWorkers(1);
const analysis = await makeProgram(publicKeys).analyzeMethods();
const compact = Object.fromEntries(Object.entries(analysis).map(([name, method]) => [name, { rows: method.rows, digest: method.digest }]));
await writeFile('evidence/circuit-analysis.json', JSON.stringify(compact, null, 2) + '\n');
console.log(JSON.stringify(compact));
