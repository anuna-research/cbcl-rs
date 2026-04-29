#!/usr/bin/env bash
# Copy (or symlink) the macOS cdylib produced by `cargo build -p cbcl-erl`
# to a `.so` filename so `erlang:load_nif/2` can dlopen it.
#
# Cargo always emits libcbcl_erl.dylib on Darwin; the BEAM appends `.so`
# regardless of platform. The build script already rewrites the binary's
# install_name to @rpath/libcbcl_erl.so, so renaming/symlinking here is
# enough — no codesign or otool fixup required.
#
# Usage:
#   crates/cbcl-erl/scripts/install-mac-nif.sh           # uses target/release
#   crates/cbcl-erl/scripts/install-mac-nif.sh debug     # uses target/debug
#   PROFILE=release MODE=symlink scripts/install-mac-nif.sh
#
# Environment:
#   PROFILE  release|debug                (default: release; positional arg wins)
#   MODE     copy|symlink                 (default: copy)
#   TARGET   override target dir          (default: workspace target/)

set -euo pipefail

if [[ "$(uname -s)" != "Darwin" ]]; then
    echo "install-mac-nif.sh: not on macOS, nothing to do." >&2
    exit 0
fi

PROFILE="${1:-${PROFILE:-release}}"
MODE="${MODE:-copy}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
workspace_root="$(cd "${script_dir}/../../.." && pwd)"
target_dir="${TARGET:-${workspace_root}/target}/${PROFILE}"

src="${target_dir}/libcbcl_erl.dylib"
dst="${target_dir}/libcbcl_erl.so"

if [[ ! -f "${src}" ]]; then
    echo "install-mac-nif.sh: ${src} not found — run \`cargo build -p cbcl-erl --${PROFILE}\` first." >&2
    exit 1
fi

case "${MODE}" in
    copy)
        cp -f "${src}" "${dst}"
        ;;
    symlink)
        ln -sf "libcbcl_erl.dylib" "${dst}"
        ;;
    *)
        echo "install-mac-nif.sh: unknown MODE='${MODE}' (expected 'copy' or 'symlink')." >&2
        exit 2
        ;;
esac

echo "install-mac-nif.sh: ${dst} (${MODE})"
