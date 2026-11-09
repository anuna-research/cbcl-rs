#!/usr/bin/env bash
# Bootstrap elan and the repository-pinned Lean toolchain on Forgejo runners.
set -euo pipefail

export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
download_dir=""
toolchain_download_dir=""
cleanup() {
    [[ -z "$download_dir" ]] || rm -rf "$download_dir"
    [[ -z "$toolchain_download_dir" ]] || rm -rf "$toolchain_download_dir"
}
trap cleanup EXIT

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
    if ! retry "Lean toolchain installation" "$ELAN_HOME/bin/elan" toolchain install "$toolchain"; then
        # The releases.lean-lang.org redirect can return 504 independently of
        # elan's own download. Use verified official assets for the pinned Lean
        # version, then link that distribution under the exact toolchain name.
        if [[ "$toolchain" != "leanprover/lean4:v4.27.0" || "$(uname -s)" != Linux ]]; then
            printf 'FAIL: no verified fallback for %s on this platform\n' "$toolchain" >&2
            exit 1
        fi
        case "$(uname -m)" in
            x86_64 | amd64)
                lean_platform="linux"
                lean_asset="344780904"
                lean_digest="0a62138ea5b9880a8eccd5e88d0920f93a58cf3428a9c78f99b8f4316383c69b"
                ;;
            aarch64 | arm64)
                lean_platform="linux_aarch64"
                lean_asset="344780906"
                lean_digest="da069c96a5d8ccb3b84cdfa6a025b78219070d1818d1e36f9b8936cf6c34e341"
                ;;
            *) printf 'FAIL: unsupported Lean fallback architecture\n' >&2; exit 1 ;;
        esac
        command -v unzip >/dev/null || { printf 'FAIL: unzip is required for the Lean fallback\n' >&2; exit 1; }
        toolchain_download_dir="$(mktemp -d)"
        lean_archive="$toolchain_download_dir/lean.zip"
        download_toolchain() {
            curl --proto '=https' --tlsv1.2 --fail --silent --show-error --location \
                --connect-timeout 15 --max-time 600 -H 'Accept: application/octet-stream' \
                -H 'X-GitHub-Api-Version: 2022-11-28' -o "$lean_archive" "$1" || return 1
            if ! printf '%s  %s\n' "$lean_digest" "$lean_archive" | sha256sum --check --status; then
                printf 'FAIL: Lean archive checksum mismatch\n' >&2
                return 1
            fi
        }
        if ! retry "pinned Lean archive download" download_toolchain \
            "https://github.com/leanprover/lean4/releases/download/v4.27.0/lean-4.27.0-$lean_platform.zip"; then
            retry "pinned Lean API asset download" download_toolchain \
                "https://api.github.com/repos/leanprover/lean4/releases/assets/$lean_asset"
        fi
        # Keep the extracted distribution outside temporary download storage:
        # elan links it rather than copying it, and subsequent CI steps use it.
        mkdir -p "$ELAN_HOME/cbcl-toolchains"
        toolchain_install_dir="$(mktemp -d "$ELAN_HOME/cbcl-toolchains/lean.XXXXXX")"
        unzip -q "$lean_archive" -d "$toolchain_install_dir"
        distribution="$toolchain_install_dir/lean-4.27.0-$lean_platform"
        [[ -x "$distribution/bin/lean" && -x "$distribution/bin/lake" ]] || {
            printf 'FAIL: verified Lean archive lacks expected executables\n' >&2
            exit 1
        }
        "$ELAN_HOME/bin/elan" toolchain link "$toolchain" "$distribution"
    fi
fi
"$ELAN_HOME/bin/elan" run "$toolchain" lean --version
"$ELAN_HOME/bin/elan" run "$toolchain" lake --version
