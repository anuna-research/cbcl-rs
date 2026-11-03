# cbcl-erl

Erlang/BEAM NIF bindings for CBCL via [rustler]. Protocol semantics, NIF
surface, and conformance vectors are in `specs/SPEC-009-erl-nif.md`.

## Building

```
cargo build -p cbcl-erl --release
```

Output (Windows is not supported in v0.1.0):

- Linux: `target/release/libcbcl_erl.so`
- macOS: `target/release/libcbcl_erl.dylib` (see below)

## macOS post-build step

`erlang:load_nif("…/libcbcl_erl", 0)` always appends `.so`, but Cargo emits
`.dylib` on Darwin. The build script patches the binary's `install_name`
to `@rpath/libcbcl_erl.so`, so a copy or symlink is sufficient:

```
crates/cbcl-erl/scripts/install-mac-nif.sh release
```

Set `CBCL_ERL_SUPPRESS_MACOS_WARNING=1` to silence the build-time warning
once your packaging is wired up.

[rustler]: https://github.com/rusterlium/rustler

## Erlang loader and smoke test

`erlang/cbcl_erl.erl` is the BEAM side of the binding: a module named by
`rustler::init!("cbcl_erl")` whose `-on_load` stubs are replaced by the
natives when `erlang:load_nif/2` succeeds and raise `nif_not_loaded`
otherwise. It exports `versions/0`, `verify_dialect/1`, `parse_message/1`,
`parse_message_lax/1`, and the eight SPEC-019 state NIFs (`fold/1`,
`intend/1`, `verify_state_shape/1`, `state_schema/1`, `may_send/1`,
`frontier/1`, `dialect_hash/1`, `admit/1`) `read/1` (the parser's tree of one S-expression as JSON) `verify_message_shape/1` (a message against a dialect's `(shape …)` clauses, the browser's own verdict; cbcl-rs #14) `compile_contract/1` (SPEC-087: a JSON contract to its self-addressed dialect), and the reads `define_text/1`, `describe_dialect/1`, `read_act/1`, each `binary() -> {ok, Bin} | {error, Bin}`.
The loader reads `CBCL_ERL_NIF` (the library path without its extension)
and falls back to `priv/libcbcl_erl`; a host such as cbcl-bus copies the
module beside its own sources and points `init/0` at its `priv`.

`scripts/smoke.escript` proves the binding on a real BEAM (`erl` and
`escript` from Erlang/OTP; on this machine `/opt/homebrew/bin`). It builds
the NIF, runs `install-mac-nif.sh`, compiles and loads the module, and
calls every NIF: the state NIFs once with a valid frame built from
`dialects/lunch-vote.cbcl` and once with a malformed one, asserting the
`{ok, Bin}` and `{error, Bin}` shapes. It exits 0 when every check passes.

```
crates/cbcl-erl/scripts/smoke.escript            # release profile
crates/cbcl-erl/scripts/smoke.escript debug
SKIP_BUILD=1 crates/cbcl-erl/scripts/smoke.escript
```
