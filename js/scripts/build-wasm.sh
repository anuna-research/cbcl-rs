#!/usr/bin/env bash
# Build the cbcl-wasm crate for the browser (wasm-bindgen `web` target) into
# js/wasm/, the files the package ships beside its TypeScript output.
#
#   WASM_BINDGEN=/path/to/wasm-bindgen bash scripts/build-wasm.sh
#
# The wasm-bindgen CLI must match the wasm-bindgen crate in Cargo.lock
# exactly; a mismatched CLI refuses the build. Paths are remapped so the
# artifact embeds no local directories.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
root="$(cd "$here/.." && pwd)"
bindgen="${WASM_BINDGEN:-wasm-bindgen}"
locked="$(awk '/^name = "wasm-bindgen"$/{getline; gsub(/version = |"/, ""); print; exit}' "$root/Cargo.lock")"
if [[ "$("$bindgen" --version)" != "wasm-bindgen $locked" ]]; then
  echo "build-wasm: requires wasm-bindgen-cli $locked (matching Cargo.lock); got $("$bindgen" --version)" >&2
  echo "  cargo install wasm-bindgen-cli --version $locked --locked --root <dir>; WASM_BINDGEN=<dir>/bin/wasm-bindgen" >&2
  exit 1
fi
target="${CARGO_TARGET_DIR:-$root/target}"
cargo_home="${CARGO_HOME:-$HOME/.cargo}"
RUSTFLAGS="--remap-path-prefix=$root=/cbcl-rs --remap-path-prefix=$cargo_home=/cargo" \
  cargo build --locked --release --manifest-path "$root/Cargo.toml" \
    -p cbcl-wasm --features bindgen --target wasm32-unknown-unknown
rm -f "$here"/src/cbcl_wasm*
"$bindgen" "$target/wasm32-unknown-unknown/release/cbcl_wasm.wasm" --target web --out-dir "$here/src" --out-name cbcl_wasm
rm -f "$here/src/.gitignore"
cat > "$here/src/cbcl_wasm.provenance.json" <<JSON
{
  "cbclRsSha": "$(git -C "$root" rev-parse HEAD)",
  "crate": "cbcl-wasm",
  "features": ["bindgen"],
  "rustcVersion": "$(rustc --version | cut -d' ' -f2)",
  "wasmBindgenVersion": "$locked",
  "wasmSha256": "$(shasum -a 256 "$here/src/cbcl_wasm_bg.wasm" | cut -d' ' -f1)",
  "buildHost": "$(rustc -vV | sed -n 's/^host: //p')"
}
JSON
echo "build-wasm: $here/src/cbcl_wasm ($(git -C "$root" rev-parse --short HEAD))"
