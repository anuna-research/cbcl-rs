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
wireAddress('(tell @bo "hi")');          // 'sha256-…', as :caused-by and :replaces spell it
verifyDialect(defineText);               // throws with cbcl-rs's blame when refused (R1–R7)
verifyShape(defineText, 'vote', '(vote @r :choice "x")');   // {ok: true} | {ok: false, reason}
compileContract(json);                   // {name: 'sha256-…', label, dialect}   (SPEC-087)
```

Also exported: `parseSexpr`, `kwargs`, `asText`, `readValue`, `sliceForm` (reading helpers over `read`), and the state-layer frames `foldState`, `intendAct`, `admitAct`, `maySend`, `frontierOf`, `stateSchema` (SPEC-019 R.7), each taking the S-expression frame and returning typed results.

## `cbcl/object`

A JSON contract (verbs, fields, state rules) compiles to one CBCL dialect carrying the state clause, named by its self-address; every host installs it through R1–R7 and folds it with cbcl-rs.

```js
import { defineContract, c, enumOf, actRecord, ThreadStore } from 'cbcl/object';

const poll = await defineContract({
  dialect: 'team-choice',
  verbs: {
    propose: { causedBy: 'begin', fields: { question: 'string', options: ['string'] } },
    vote: { causedBy: ['propose'], fields: { choice: enumOf('options') } },
  },
  state: {
    question: c.last('propose', 'question'), options: c.last('propose', 'options'),
    ballots: c.latestPerSigner('vote', 'choice'), tally: c.histogram('ballots'),
  },
});

poll.name;     // 'sha256-…', the dialect's self-address
poll.dialect;  // the (define …) text to declare to a room
const opener = poll.open({ room: '@general', thread: 'lunch-1', from: '@me', fields: { question: 'Lunch?', options: ['Sushi', 'Pizza'] } });

const store = new ThreadStore();
store.append(actRecord(opener, '@me'));   // authenticated records, keyed by wire address
const agent = poll.agent({ store, me: () => '@me', send: text => transport.send(text) });
await agent.act('lunch-1', 'vote', { choice: 'Sushi' });   // cbcl-rs binds, the host signs
agent.read('lunch-1');                                       // the fold
```

Rules are the fourteen of SPEC-019 R.1 (`last`, `latestPerSigner`, `latestPerKey`, `exists`, `count`, `events`, `setUnion`, `values`, `valuesPerKey`, `registerPerKey`, `observedSet`, `counter`, `histogram(field)`, `sum(field)`); optional `author`, `requirements`, `bounds`, and `roles` with `from`/`to` per verb. Registers carry replacement in a reserved `:replaces` field that cbcl-rs inserts and the binder fills. An intent supplies a verb and its data fields only; a routing keyword is refused as a forge.

`poll.read(records)` folds without a transport; `poll.verdicts(records)` says which are accepted, pending, or rejected; `createRuntime(dialectText)` is the runtime for any dialect text, including one learned from a room.

## Development

```sh
npm run build:wasm   # cbcl-wasm → src/cbcl_wasm.*  (needs wasm-bindgen-cli matching Cargo.lock)
npm test             # node --test over test/*.test.ts, no build step
npm run build        # dist/: ES modules, .d.ts, the wasm, LICENSE
```

`test/corpus.test.ts` reproduces every vector of the cbcl-rs conformance corpus (`test-vectors/state`); `test/verifier.test.ts` proves the contract compile names `dialects/checklist.cbcl` by hash.

Apache-2.0, as cbcl-rs.
