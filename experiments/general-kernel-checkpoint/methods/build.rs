fn main() {
    // The guest's path dependencies are outside methods/guest. Track them so
    // kernel/wrapper edits cannot leave a silently stale embedded program.
    for path in [
        "../common/src",
        "../../../crates/cbcl-core/src",
        "../../../crates/cbcl-parser/src",
    ] {
        println!("cargo:rerun-if-changed={path}");
    }
    risc0_build::embed_methods();
}
