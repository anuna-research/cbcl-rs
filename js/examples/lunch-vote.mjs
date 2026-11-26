import { readFile } from 'node:fs/promises';
import { parseDialect, verifyDialect } from 'cbcl';
import { actRecord, createRuntime, makeHlc, openerText } from 'cbcl/object';

const file = process.argv[2] ?? new URL('../../dialects/lunch-vote.cbcl', import.meta.url);
const source = await readFile(file, 'utf8');
verifyDialect(source);
const dialect = parseDialect(source);
const runtime = createRuntime(source);
console.log('Verified', dialect.name);

const thread = 'friday-lunch';
const opener = openerText({
  dialect: dialect.name, verb: dialect.opener, room: '@team', thread, from: '@alice',
  fields: { question: 'What should we order?', options: ['Sushi', 'Pizza'] },
});
const records = [];
function accept(text, signer) {
  const record = actRecord(text, signer);
  const admission = runtime.admit(thread, records, record);
  if (admission.verdict !== 'accepted') throw new Error(JSON.stringify(admission));
  records.push(record);
}
accept(opener, '@alice');

// Local fixture identities. A network host authenticates signers before admission.
const clock = makeHlc();
const vote = runtime.intend(thread, records, '@bob', 'vote', { choice: 'Sushi', clock });
if (!vote.ok) throw new Error(vote.reason);
accept(vote.canonical, '@bob');

const outside = runtime.intend(thread, records, '@bob', 'vote', {
  choice: 'Soup', clock: makeHlc({ previous: clock }),
});
if (outside.ok || outside.reject !== 'domain') throw new Error('Expected a domain rejection');
console.log('Soup rejected: outside the proposed options');
console.log('Tally:', JSON.stringify(runtime.read(thread, records).tally));
