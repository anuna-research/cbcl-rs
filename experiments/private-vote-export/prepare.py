"""Stage owned packages, leaving existing experiments and upstream sources intact."""
import pathlib, shutil, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
jolt = pathlib.Path(sys.argv[1]).resolve()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=jolt,text=True).strip() == 'beebf45d829f5aecc5d330f78879cd914e47541e'
for package in ('common','guest','host'):
    dest = jolt/'.vote-overlay'/package
    if dest.exists(): shutil.rmtree(dest)
    shutil.copytree(root/package,dest)
    if package == 'common':
        manifest = dest/'Cargo.toml'
        s = manifest.read_text().replace("[workspace]", "")
        for name in ('cbcl-core','cbcl-parser'):
            s = s.replace('../../../crates/'+name, str(root.parents[1]/'crates'/name))
        manifest.write_text(s)
p = jolt/'Cargo.toml'
s = p.read_text()
# Cargo cannot lock two path copies of the same CBCL version. Temporarily remove
# the older experiment's workspace membership; its files/builds remain intact.
backup = jolt/'.vote-backup'
backup.mkdir(exist_ok=True)
for filename in ('Cargo.toml','Cargo.lock'):
    saved = backup/filename
    if not saved.exists():
        text = (jolt/filename).read_text()
        if filename == 'Cargo.toml':
            text = ''.join(line for line in text.splitlines(keepends=True) if '".vote-overlay/' not in line)
        saved.write_text(text)
s = ''.join(line for line in s.splitlines(keepends=True) if '".cbcl-overlay/' not in line)
for package in ('common','guest','host'):
    member = '.vote-overlay/'+package
    if '"'+member+'"' not in s:
        s = s.replace('members = [','members = [\n  "'+member+'",',1)
p.write_text(s)

# Apply the recorded resolution delta to the exact pinned upstream lock.
lock_patch = root/'jolt-lock.patch'
if lock_patch.exists():
    base_lock = subprocess.check_output(['git','show','HEAD:Cargo.lock'],cwd=jolt)
    (jolt/'Cargo.lock').write_bytes(base_lock)
    subprocess.run(['git','apply',str(lock_patch)],cwd=jolt,check=True)
