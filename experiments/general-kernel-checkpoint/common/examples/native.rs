fn main() {
    let args: Vec<_> = std::env::args().collect();
    let bytes = std::fs::read(&args[1]).unwrap();
    let computed = checkpoint_common::compute(&bytes).unwrap();
    println!("{}", computed.state);
}
