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
    installer_path="$(mktemp)"
    trap 'rm -f "$installer_path"' EXIT
    retry "elan installer download" curl --proto '=https' --tlsv1.2 \
        --fail --silent --show-error --location --connect-timeout 15 --max-time 120 \
        -o "$installer_path" https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
    # Retry the installer itself: its internal GitHub release download can fail
    # even after the initial script download succeeded (for example HTTP 504).
    retry "elan installation" sh "$installer_path" -y --default-toolchain none --no-modify-path
fi

if [[ -n "${GITHUB_PATH:-}" ]]; then
    printf '%s\n' "$ELAN_HOME/bin" >> "$GITHUB_PATH"
fi

toolchain="$(tr -d '\r\n' < "$repository_root/lean-cbcl/lean-toolchain")"
if [[ -z "$toolchain" ]]; then
    printf 'FAIL: lean-cbcl/lean-toolchain is empty\n' >&2
    exit 1
fi
retry "Lean toolchain installation" "$ELAN_HOME/bin/elan" toolchain install "$toolchain"
"$ELAN_HOME/bin/elan" run "$toolchain" lean --version
"$ELAN_HOME/bin/elan" run "$toolchain" lake --version
