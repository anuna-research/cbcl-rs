"""Execute one pinned host binary with explicit guest tools and no global settings."""
import os,pathlib,sys
root=pathlib.Path(__file__).resolve().parents[2]
out=pathlib.Path(os.environ.get('CBCL_VOTE_OUTPUT',root/'outputs/private-vote-export')).resolve()
mode=sys.argv[1];assert mode in ('clear','zk')
binary=out/('cbcl-vote-'+mode)
jolt=pathlib.Path(os.environ.get('CBCL_JOLT_SOURCE','/tmp/cbcl-jolt-akita-source')).resolve()
cache=pathlib.Path(os.environ.get('CBCL_JOLT_TARGET','/Users/anuna-02/Code/cbcl-rs-jolt-akita/experiments/jolt-akita-checkpoint/target')).resolve()
os.environ.update(JOLT_PATH=str(cache/'build-fast/jolt'),CBCL_GUEST_TARGET=str(out/'guest-target'),CARGO_TARGET_DIR=str(cache),RUSTUP_TOOLCHAIN='1.95.0')
os.chdir(jolt)
os.execv(str(binary),[str(binary),*sys.argv[2:]])
