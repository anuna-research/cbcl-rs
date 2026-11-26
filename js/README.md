# cbcl

CBCL for JavaScript: the verifier as typed wrappers over the cbcl-rs WebAssembly build, and, under `cbcl/object`, the object authoring runtime on top of it. Nothing in this package judges a message or a dialect itself; every verdict is cbcl-rs's, so a browser, a Node agent, and a hub running the NIF agree by construction.

```sh
npm install cbcl
```

Requires Node 22.6 or later (or a browser with WebAssembly). The wasm is inside the package; under Node it initialises at import, in a browser call `await ready()` before the first frame.

For a first working example, [open a lunch poll and count a vote](../docs/tutorials/lunch-vote.md). The [documentation guide](../docs/README.md) covers the language, hosts and proof model.

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

| Task | Functions exported by `cbcl` |
|---|---|
| Read an S-expression | `parseSexpr`, `kwargs`, `asText`, `readValue` |
| Work with state frames | `foldState`, `intendAct`, `admitAct`, `maySend`, `frontierOf`, `stateSchema` |

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
import { defineContract, c, makeHlc, enumOf, actRecord, ThreadStore } from 'cbcl/object';

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
// Load and save the signer's clock in host-owned durable storage.
const clock = makeHlc({ previous: await loadClock() });
await saveClock(clock);
await agent.act('lunch-1', 'vote', { choice: 'Sushi', clock });   // cbcl-rs binds, the host signs
agent.read('lunch-1');                                       // the fold
```

### Write and read a dialect file

Run this Node example in a directory where you want to create `prices.cbcl`.
It compiles a JS definition, writes the complete dialect, verifies the file,
and reads its named type back.

<!-- runnable: dialect-file -->
```js
import { readFile, writeFile } from 'node:fs/promises';
import { verifyDialect } from 'cbcl';
import { c, defineContract, parseDialect, t } from 'cbcl/object';

const prices = await defineContract({
  name: 'prices',
  types: { price: t.decimal({ gte: 0 }) },
  verbs: { open: { after: ['begin'], fields: { amount: 'price', quantity: t.integer({ gt: 0 }) } } },
  state: { amount: c.initial('open', 'amount') },
});
await writeFile('prices.cbcl', prices.dialect, { flag: 'wx' });
const source = await readFile('prices.cbcl', 'utf8');
verifyDialect(source);
const info = parseDialect(source);
console.log(info.name === prices.name, info.types.price.representations.join(', '));
// true decimal
```

The file declares the generated self-address (`prices.name`). The authoring label
is `prices.label`. For a handwritten dialect, start at `readFile` with its filename.

### Field types

Declare reusable field types in the top-level `types` record. Both definitions
and verb fields accept the full CBCL flat type-expression grammar.

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

`makeHlc()` issues a first timestamp using the current millisecond. For later
writes pass the previous timestamp, and pass `received` to merge an observed HLC.
Hosts can supply `nowMs` explicitly and serialize issuance per signer.

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

## `cbcl/view`

Use `defineView` to bind a presentation to an object’s dialect address. For the
poll above, this view shows the tally and offers a vote. The host supplies the
HLC when it binds the submitted intent.

```js
import { defineView, bundleText, importBundle } from 'cbcl/view';

const presentation = await defineView({
  contract: poll,
  view: [
    { type: 'value', field: 'tally', label: 'Votes' },
    { type: 'form', verb: 'vote', label: 'Vote', fields: { choice: 'Your choice' } },
  ],
});
const bundle = bundleText(poll, presentation);
const restored = await importBundle(bundle);
console.log(restored.presentation.id === presentation.id); // true
```

`importView(text, contract)` checks a serialized view against its dialect.
`defaultPresentation(contract)` gives a read-only view of the state.
Version 3 view and bundle records from cbcl-bus use the same format and IDs.
Optional `layout`, `composer`, `resources`, and `capabilities` describe
presentation preferences and requests.

Custom views accept an HTML source record or a render function using the
exported `html` template tag. A render function travels as source and must
be self-contained. `presentation.body()` produces document source for a host
sandbox. The host supplies isolation, grants requested capabilities, and binds
intents to the authenticated signer. Importing a view does not execute it.

## Development

```sh
npm run build:wasm   # cbcl-wasm → src/cbcl_wasm.*  (needs wasm-bindgen-cli matching Cargo.lock)
npm test             # node --test over test/*.test.ts, no build step
npm run build        # dist/: ES modules, .d.ts, the wasm, LICENSE
npm run test:docs    # run the documentation examples against the built package
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

## State observations, shapes, and resource checks

Use `optional(type, defaultValue?)` in a verb's fields. For a nested shape,
`{ type: 'list', children: { title: 'string' } }` checks the contents
of the list. The serialized field descriptor uses CBCL source for `default`.
Omitted optional fields are accepted. Read the declared default and child
constraints through `info.verbs[verb].contracts[field]`.

```js
import { c, defineContract, optional, stateEntry } from 'cbcl/object';

const poll = await defineContract({
  name: 'approvals',
  verbs: {
    open: { after: ['begin'], fields: { title: optional('string', 'Vote') } },
    approve: { after: ['open'] },
  },
  state: { approvals: c.count('approve') },
  stateEntries: [stateEntry('threshold', 'quorum', 'approvals', ['count', 2])],
});
```

`stateEntries` follows the named `state` fields in declaration order. It accepts
native CBCL entries for lattices, lifts, composed thresholds, domains and freezes.
Use it alone when all declarations need an explicit order. `stateEntry` writes
nested arrays as lists, names as atoms and `{ str: 'text' }` as a quoted string.
`parseDialect` exposes `thresholds`, `lattices`, `freezes`, and recursive shape metadata.

For escrow, `c.boundedCounter(options)` accepts the native option lists.
`object.runtime.resourceCheck(thread, messages, candidate)` checks an authenticated
candidate against the accepted prefix. Inspect its `status` for ready, pending,
fault or rejected. Amounts outside the JS safe-integer range use decimal strings.
Hosts authenticate records and separately check protocol admission.

## Public keys and certified checkpoints

`cbcl` exports `inspectMultikey(text)`, `encodeMultikey(codec, bytes)`,
`publicKeyCodecs`, and `multikeyIdentity(text)`. Inspection returns a numeric
codec and public key bytes for Ed25519, X25519, P-256 or P-384. Identity
conversion accepts Ed25519.

```js
import { openCheckpoint } from 'cbcl';

const client = openCheckpoint({
  dialect, targetRoot, companionRoot, policy: { roster, faults }, publicKeys,
}, certificateBytes);
try {
  client.apply(step);
  const state = client.read();
} finally {
  client.close();
}
```

Supply independently trusted dialect and signed root texts, roster policy, and
a map from signer handles to their Ed25519 public Multikeys. The Rust verifier
checks the native certificate before returning a fresh in-memory client.
A continuation step contains the signed message text, ancestry witnesses,
identity proof and replacement proofs. Failed applications preserve the previous
state. `readJson()` returns the native JSON text, including exact integer digits.
To switch certificates on a running client, use `client.replace(bytes, floorProofs, tail)`.
Rust verifies the proposed continuation covers the current `client.frontier()`
and retains local evidence before installing it. Hosts own durable storage
and checkpoint selection across restarts.
