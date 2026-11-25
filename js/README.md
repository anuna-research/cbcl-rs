# cbcl

CBCL for JavaScript: the verifier as typed wrappers over the cbcl-rs WebAssembly build, and, under `cbcl/object`, the object authoring runtime on top of it. Nothing in this package judges a message or a dialect itself; every verdict is cbcl-rs's, so a browser, a Node agent, and a hub running the NIF agree by construction.

```sh
npm install cbcl
```

Requires Node 22.6 or later (or a browser with WebAssembly). The wasm is inside the package; under Node it initialises at import, in a browser call `await ready()` before the first frame.

## `cbcl`

```js
import { ready, read, parseMessage, messageHash, wireAddress, dialectHash, verifyDialect,
         verifyShape, verifyStateShape, verifyProtocol, compileContract } from 'cbcl';

await ready();
read('(tell @bo "hi" :n 3)');            // ['tell', '@bo', {str: 'hi'}, ':n', '3']
wireAddress('(tell @bo "hi")');          // 'f1220…', as :caused-by and :replaces spell it
verifyDialect(defineText);               // throws with cbcl-rs's blame when refused (R1–R7)
verifyShape(defineText, 'vote', '(vote @r :choice "x")');   // {ok: true} | {ok: false, reason}
compileContract(json);                   // {name: 'f1220…', label, dialect}   (SPEC-087)
```

Use `parseDialect(source)` from either `cbcl` or `cbcl/object` to read a
handwritten `.cbcl` dialect. It returns a `DialectInfo` with canonical CBCL
in `text`, named definitions in `types`, and each verb’s field constraints,
requiredness, and defaults in `verbs[verb].contracts`. Malformed source throws.
Call `verifyDialect(info.text)` when you also need installation checks.

Also exported: `parseSexpr`, `kwargs`, `asText`, `readValue`, `sliceForm` (reading helpers over `read`), and the state-layer frames `foldState`, `intendAct`, `admitAct`, `maySend`, `frontierOf`, `stateSchema` (SPEC-019 R.7), each taking the S-expression frame and returning typed results.

Audience extraction is available as `recipientOf(message)` and
`recipientOfLax(message)`, both backed by the compiled Rust parser. The strict
accessor requires dialect-scoped custom verbs; the lax accessor also recognizes
bare host control verbs, which the host must authorize. Both retain `@`, honor
the outer envelope's routing `:to`, and throw on missing or ambiguous audiences.
They enforce current parser grammar, including a final wrapper body. Legacy
post-body proof fields and keyword-value bodies are rejected; the routing corpus
records these compatibility differences explicitly.

## `cbcl/object`

A JSON contract (verbs, fields, state rules) compiles to one CBCL dialect carrying the state clause, named by its self-address; every host installs it through R1–R7 and folds it with cbcl-rs.

```js
import { defineContract, c, enumOf, actRecord, ThreadStore } from 'cbcl/object';

const poll = await defineContract({
  dialect: 'team-choice',
  verbs: {
    propose: { causedBy: 'begin', fields: { question: 'string', options: ['string'] } },
    vote: { causedBy: ['propose'], fields: { choice: enumOf('options'), clock: 'hlc' } },
  },
  state: {
    question: c.initial('propose', 'question'), options: c.initial('propose', 'options'),
    ballots: c.lwwPerSigner('vote', 'choice', 'clock'), tally: c.histogram('ballots'),
  },
});

poll.name;     // 'f1220…', the dialect's self-address
poll.dialect;  // the (define …) text to declare to a room
const opener = poll.open({ room: '@general', thread: 'lunch-1', from: '@me', fields: { question: 'Lunch?', options: ['Sushi', 'Pizza'] } });

const store = new ThreadStore();
store.append(actRecord(opener, '@me'));   // authenticated records, keyed by wire address
const agent = poll.agent({ store, me: () => '@me', send: text => transport.send(text) });
// The host generates and persists clock evidence before binding.
await agent.act('lunch-1', 'vote', { choice: 'Sushi', clock: 'hlc-000001a3185c5000-00000000' });   // cbcl-rs binds, the host signs
agent.read('lunch-1');                                       // the fold
```

Declare reusable field types in the top-level `types` record. Both definitions
and verb fields accept the full CBCL flat type-expression grammar, including
numeric bounds, string patterns, list lengths, `one-of`, `and`, and `or`.

```js
import { c, defineContract, t } from 'cbcl/object';

const prices = await defineContract({
  name: 'prices',
  types: { price: t.decimal({ gte: 0 }) },
  verbs: { open: { after: ['begin'], fields: { amount: 'price', quantity: t.integer({ gt: 0 }) } } },
  state: { amount: c.initial('open', 'amount') },
});
prices.info.types.price.representations; // ['decimal']
```

The builders return CBCL type-expression strings. Compose them with `t.and(a, b)`
or `t.or(a, b)`. Use `t.oneOf("draft", "final")` for string choices and
`t.string({ length: { lte: 32 }, matches: "[A-Z]+" })` for constrained text.
For repeated clauses or a specific order, pass tuples such as
`t.string([["matches", "a.*"], ["length", [">=", 1]], ["matches", ".*b"]])`.
Numeric builders accept ordered comparisons such as `t.float([[">=", { float: 2 }]])`.
Builtin types and local type references also work as plain names.

**Exact act fields.** The same literals work in enumerations, openers and intents.
Use `{ keyword: "2fa" }` for `:2fa`, `{ symbol: "@team/red" }` for a symbol,
`{ float: 2 }` for `2.0`, and `{ decimal: "0.01" }` for an exact decimal.
Use a bigint or `{ integer: "9223372036854775807" }` for a signed 64-bit integer
outside JavaScript’s safe range. These representations work inside lists.

`readActExact(text).fields` (from either SDK entry point) returns fields you can
pass back to `open` or `act`. Large integers use the JSON-safe string wrapper.
`readAct` and folded state retain their existing display representations.

The state grammar has 16 heads, including `initial` and the explicit
`lwwRegister`, `lwwPerSigner` and `lwwMap` rules. LWW writes declare an `hlc` field and supply its
canonical clock string; the host generates it before calling the binder. Choice
uses HLC, signer, then content address as an exact final tie-break. `initial`
reads the sole raw opener without arbitration. The retired `last`,
`latestPerSigner`, `latestPerKey`, and `registerPerKey` operations are rejected.
Conflict-preserving alternatives are `multiValueRegister` and `multiValueMap`.
Replacement metadata remains compiler/binder-owned; callers cannot forge it.
See [HLC registers](../docs/concepts/hlc-registers.md) for assumptions and migration.


`poll.read(records)` folds without a transport; `poll.verdicts(records)` says which are accepted, pending, or rejected; `createRuntime(dialectText)` is the runtime for any dialect text, including one learned from a room.

## Development

```sh
npm run build:wasm   # cbcl-wasm → src/cbcl_wasm.*  (needs wasm-bindgen-cli matching Cargo.lock)
npm test             # node --test over test/*.test.ts, no build step
npm run build        # dist/: ES modules, .d.ts, the wasm, LICENSE
```

`test/corpus.test.ts` reproduces every vector of the cbcl-rs conformance corpus (`test-vectors/state`); `test/verifier.test.ts` proves the contract compile names `dialects/checklist.cbcl` by hash.

Apache-2.0, as cbcl-rs.

`c.progress('tick')` compiles to `(progress tick)`: the maximum established protocol occurrence, defaulting to zero. Competing ticks at the same occurrence do not inflate it. Installation rejects missing or incomparable occurrences. This reads causal metadata over accepted acts independently of application-data domain filters. See [protocol progress](../docs/concepts/protocol-progress.md) for semantics and the Lean proof boundary.


State observations (SPEC-038): `state_schema` marks current field values with
`"observation":"snapshot"`. An external effect fired on a snapshot has no
finality guarantee from the kernel. Use a reached threshold to establish a
stable successful fact, or wait for the declared freeze and inspect the folded
`{frozen, superseded, value}` result for its exact causal cut. A `freeze` entry
in the schema describes that capability; before the freezer arrives the value
is still a snapshot. Thresholds and frozen reads can report a terminal fault;
handle its evidence explicitly. The host remains responsible for effect
idempotency, delivery and any external transaction or finality policy.
