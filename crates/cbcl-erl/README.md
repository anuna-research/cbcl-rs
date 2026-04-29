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
