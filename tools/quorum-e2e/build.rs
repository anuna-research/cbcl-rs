fn main() {
    for name in ["PROFILE", "OPT_LEVEL", "TARGET"] {
        println!(
            "cargo:rustc-env=BENCH_{name}={}",
            std::env::var(name).unwrap_or_default()
        );
    }
    let version = std::process::Command::new(std::env::var("RUSTC").unwrap())
        .arg("--version")
        .output()
        .unwrap();
    println!(
        "cargo:rustc-env=BENCH_RUSTC={}",
        String::from_utf8_lossy(&version.stdout).trim()
    );
}
