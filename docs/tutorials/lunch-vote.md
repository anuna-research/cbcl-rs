# Open a lunch poll and count a vote

You’ll edit a copy of a dialect, open a poll with two choices, accept one vote and see why a third choice is refused. This example runs locally with Node and the Rust verifier compiled to WebAssembly. Start in the repository root.

## Build the SDK

Use Node 22.6 or later, npm, and the repository’s Rust toolchain. The WASM build requires the wasm-bindgen CLI version pinned in Cargo.lock. From a fresh checkout:

```sh
rustup target add wasm32-unknown-unknown
bindgen_version=$(awk '/^name = "wasm-bindgen"$/{getline; gsub(/version = |"/, ""); print; exit}' Cargo.lock)
cargo install wasm-bindgen-cli --version "$bindgen_version" --locked
(cd js && npm ci && npm run build:wasm && npm run build)
```

## Edit the dialect

Open [lunch-vote.cbcl](../../dialects/lunch-vote.cbcl). The `propose` shape requires a question and a list of options. The domain rule ties a vote’s choice to those options. The tally counts the current ballot from each signer.

```lisp
(domain vote :choice options)
(ballots (lww-per-signer vote :choice :clock))
(tally (histogram ballots))
```

Make a scratch copy with a maximum list length of three, then run the [example](../../js/examples/lunch-vote.mjs) on that file. The two proposed choices fit the new bound.

<!-- runnable: lunch-vote -->
```sh
workdir=$(mktemp -d)
sed 's/(max-list 24)/(max-list 3)/' dialects/lunch-vote.cbcl > "$workdir/lunch-vote.cbcl"
grep -Fq '(max-list 3)' "$workdir/lunch-vote.cbcl"
node js/examples/lunch-vote.mjs "$workdir/lunch-vote.cbcl"
```

Expected output:

```text
Verified lunch-vote
Soup rejected: outside the proposed options
Tally: {"Sushi":1}
```

## Follow the vote

1. `verifyDialect(source)` checks the edited dialect for installation. `parseDialect(source)` gives the example its dialect name and opener verb.
2. Alice opens the thread with `Sushi` and `Pizza`. The example admits the opener before adding it to the thread history.
3. Bob supplies `Sushi` and a timestamp from `makeHlc()`. The runtime binds the vote to its predecessor, then admits the resulting act. The local example supplies the signer identities directly. A network host authenticates each signer.
4. Bob tries `Soup`. The binder returns a domain rejection, so there is no second act to admit. Folding the accepted history yields one vote for Sushi.

To author the dialect in JavaScript and produce a `.cbcl` file yourself, follow [Write and read a dialect file](../../js/README.md#write-and-read-a-dialect-file).
