"""Execute the owned host under its pinned vendor workspace, with scoped tooling."""
import os,sys
from pathlib import Path
root=Path(__file__).resolve().parent
jolt=Path(os.environ.get('CBCL_JOLT_SOURCE','/tmp/cbcl-jolt-akita-source')).resolve()
cli=root/'target/build-fast/jolt';host=root/'target/build-fast/cbcl-akita-host'
os.environ.update(JOLT_PATH=str(cli),CBCL_GUEST_TARGET=str(root/'target/guest'),CARGO_TARGET_DIR=str(root/'target'),RUSTUP_TOOLCHAIN='1.95.0')
os.chdir(jolt)
os.execv(str(host),[str(host),*sys.argv[1:]])
