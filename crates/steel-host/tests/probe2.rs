#[test]
fn probe_both() {
    let wasm = std::fs::read(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../lean/wasm-backend/target/demo.wasm"),
    )
    .unwrap();
    let pat: [u8; 10] = [0x20, 0x00, 0x20, 0x00, 0x7C, 0x21, 0x01, 0x20, 0x01, 0x0F];
    let n = wasm.windows(10).filter(|w| *w == pat).count();
    println!("matches={n}");
}
