#!/usr/bin/env bash
# Bootstrap elan and the repository-pinned Lean toolchain on Forgejo runners.
set -euo pipefail

export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

retry() {
    local label="$1"
    shift
    local attempt
    for attempt in 1 2 3 4 5; do
        if "$@"; then
            return 0
        fi
        if [[ "$attempt" == 5 ]]; then
            printf 'FAIL: %s after %s attempts\n' "$label" "$attempt" >&2
            return 1
        fi
        printf 'Retrying %s after attempt %s/5\n' "$label" "$attempt" >&2
        sleep "$((attempt * 5))"
    done
}

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
    # Pin official release assets instead of the repeatedly failing latest/download
    # redirect. Digests are published by the v4.2.4 GitHub release asset metadata.
    elan_version="v4.2.4"
    if [[ "$(uname -s)" != Linux ]]; then
        printf 'FAIL: CI elan bootstrap supports Linux runners\n' >&2
        exit 1
    fi
    case "$(uname -m)" in
        x86_64 | amd64)
            elan_arch="x86_64-unknown-linux-gnu"
            elan_asset="529114798"
            elan_digest="42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
            ;;
        aarch64 | arm64)
            elan_arch="aarch64-unknown-linux-gnu"
            elan_asset="529114794"
            elan_digest="05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9"
            ;;
        *) printf 'FAIL: unsupported CI elan architecture\n' >&2; exit 1 ;;
    esac
    download_dir="$(mktemp -d)"
    trap 'rm -rf "$download_dir"' EXIT
    archive="$download_dir/elan.tar.gz"
    download_archive() {
        curl --proto '=https' --tlsv1.2 --fail --silent --show-error --location \
            --connect-timeout 15 --max-time 120 -H 'Accept: application/octet-stream' \
            -H 'X-GitHub-Api-Version: 2022-11-28' -o "$archive" "$1" || return 1
        if ! printf '%s  %s\n' "$elan_digest" "$archive" | sha256sum --check --status; then
            printf 'FAIL: elan archive checksum mismatch\n' >&2
            return 1
        fi
    }
    if ! retry "pinned elan archive download" download_archive \
        "https://github.com/leanprover/elan/releases/download/$elan_version/elan-$elan_arch.tar.gz"; then
        retry "pinned elan API asset download" download_archive \
            "https://api.github.com/repos/leanprover/elan/releases/assets/$elan_asset"
    fi
    tar -xzf "$archive" -C "$download_dir"
    retry "elan installation" "$download_dir/elan-init" -y --default-toolchain none --no-modify-path
fi

if [[ -n "${GITHUB_PATH:-}" ]]; then
    printf '%s\n' "$ELAN_HOME/bin" >> "$GITHUB_PATH"
fi

toolchain="$(tr -d '\r\n' < "$repository_root/lean-cbcl/lean-toolchain")"
if [[ -z "$toolchain" ]]; then
    printf 'FAIL: lean-cbcl/lean-toolchain is empty\n' >&2
    exit 1
fi
# Avoid a download on warm caches, including older elan versions whose
# toolchain-install command errors when the toolchain is already present.
if ! "$ELAN_HOME/bin/elan" run "$toolchain" lean --version >/dev/null 2>&1; then
    retry "Lean toolchain installation" "$ELAN_HOME/bin/elan" toolchain install "$toolchain"
fi
"$ELAN_HOME/bin/elan" run "$toolchain" lean --version
"$ELAN_HOME/bin/elan" run "$toolchain" lake --version
