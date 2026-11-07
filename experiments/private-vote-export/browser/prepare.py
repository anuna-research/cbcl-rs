"""Stage the browser adapter into the same pinned workspace as the native experiment."""
import pathlib,shutil,subprocess,sys
root=pathlib.Path(__file__).resolve().parent;jolt=pathlib.Path(sys.argv[1]).resolve()
subprocess.run([sys.executable,str(root.parent/'prepare.py'),str(jolt)],check=True)
dest=jolt/'.vote-overlay/browser'
if dest.exists():shutil.rmtree(dest)
shutil.copytree(root,dest,ignore=shutil.ignore_patterns('__pycache__'))
p=jolt/'Cargo.toml';s=p.read_text()
if '".vote-overlay/browser"' not in s:s=s.replace('members = [','members = [\n  ".vote-overlay/browser",',1)
p.write_text(s)
lock=root/'jolt-browser-lock.patch'
if lock.exists():
 (jolt/'Cargo.lock').write_bytes(subprocess.check_output(['git','show','HEAD:Cargo.lock'],cwd=jolt))
 subprocess.run(['git','apply',str(lock)],cwd=jolt,check=True)

# Optional portability repair for the pinned upstream WASM prover. Apply once;
# an already-applied exact patch is accepted, any conflicting source fails closed.
index_patch = root/'jolt-wasm-portability.patch'
if index_patch.exists():
 forward = subprocess.run(['git','apply','--check',str(index_patch)],cwd=jolt,capture_output=True,text=True)
 if forward.returncode == 0:
  subprocess.run(['git','apply',str(index_patch)],cwd=jolt,check=True)
 else:
  reverse = subprocess.run(['git','apply','--reverse','--check',str(index_patch)],cwd=jolt,capture_output=True,text=True)
  if reverse.returncode != 0:
   raise RuntimeError('WASM index patch neither applicable nor already applied: '+forward.stderr+reverse.stderr)
