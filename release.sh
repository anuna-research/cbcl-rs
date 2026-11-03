#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Usage: ./release.sh X.Y.Z
# Updates the shared Cargo workspace version, checks Rust and Lean, then pushes
# a version commit and annotated tag. Does not publish crates or binaries.
set -euo pipefail
cd "$(dirname "$0")"

fail() { printf 'release: %s\n' "$*" >&2; exit 1; }
if [[ "${1:-}" == --help || "${1:-}" == -h ]]; then
    printf 'Usage: ./release.sh X.Y.Z\nChecks Rust and Lean, commits the workspace version, and pushes main and vX.Y.Z.\n'
    exit 0
fi
[[ $# == 1 ]] || fail 'Usage: ./release.sh X.Y.Z'
version=$1
# Stable SemVer only; leading zeroes are not permitted.
[[ $version =~ ^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$ ]] || fail 'Expected a stable version X.Y.Z (without v or leading zeroes).'
tag="v$version"
for tool in git cargo make python3 lake; do
    command -v "$tool" >/dev/null || fail "Required tool not found: $tool"
done
[[ -z $(git status --porcelain --untracked-files=normal) ]] || fail 'Working tree must be clean, including untracked files.'
[[ $(git symbolic-ref --quiet --short HEAD) == main ]] || fail 'Release from main.'
git fetch origin main --tags
[[ $(git rev-parse HEAD) == $(git rev-parse refs/remotes/origin/main) ]] || fail 'Local main must match origin/main.'
if git show-ref --verify --quiet "refs/tags/$tag"; then
    fail "Tag $tag already exists."
fi
# Validate and change only workspace.package.version. Other package/dependency
# versions are untouched. Require a forward version change.
python3 - "$version" <<'PY'
import pathlib, re, sys
path = pathlib.Path('Cargo.toml')
text = path.read_text()
section = re.search(r'(?ms)^\[workspace\.package\]\s*\n(.*?)(?=^\[|\Z)', text)
if section is None:
    sys.exit('release: workspace.package section not found')
field = re.search(r'(?m)^version = "([0-9]+\.[0-9]+\.[0-9]+)"$', section[1])
if field is None:
    sys.exit('release: expected a stable workspace version')
if tuple(map(int, sys.argv[1].split('.'))) <= tuple(map(int, field[1].split('.'))):
    sys.exit('release: new version must exceed the current workspace version')
start = section.start(1) + field.start(1)
end = section.start(1) + field.end(1)
path.write_text(text[:start] + sys.argv[1] + text[end:])
PY
# Refresh workspace package versions in Cargo.lock before using locked gates.
# --offline avoids updating registry dependencies during version synchronization.
cargo metadata --offline --format-version 1 >/dev/null
printf 'Checking release %s. A failed gate leaves the version changes for inspection.\n' "$tag"
make check
make proof
git add -- Cargo.toml Cargo.lock
git commit -m "chore: release $tag"
git tag -a "$tag" -m "Release $version"
# Push both refs together; never leave a published version commit without its tag.
git push --atomic origin main "refs/tags/$tag"
printf 'Pushed %s to https://git.anuna.io/anuna-research/cbcl-rs. No packages or binaries published.\n' "$tag"
