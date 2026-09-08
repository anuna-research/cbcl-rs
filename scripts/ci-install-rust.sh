#!/usr/bin/env bash
# Bootstrap Rust on a Forgejo runner, including images without rustup.
set -euo pipefail

export CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"
export PATH="$CARGO_HOME/bin:$PATH"

if ! command -v rustup >/dev/null 2>&1; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs |
        sh -s -- -y --profile minimal --default-toolchain none --no-modify-path
fi

# Keep subsequent workflow steps on the same installation. This script can
# also run outside Actions, where GITHUB_PATH is absent.
if [[ -n "${GITHUB_PATH:-}" ]]; then
    printf '%s\n' "$CARGO_HOME/bin" >> "$GITHUB_PATH"
fi

# rust-toolchain.toml selects stable; install it before invoking its proxies.
rustup toolchain install stable --profile minimal
rustc --version
cargo --version
