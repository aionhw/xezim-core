//! IEEE 1800-2023 §5.4: the text of a comment is not interpreted. A `-v`/`-y`
//! library file is decoded as source files and `include`d files are: a byte
//! that is not UTF-8 (a Latin-1 `®`, 0xAE, in a comment) becomes U+FFFD. The
//! read used to fail ("stream did not contain valid UTF-8") and the whole
//! file was dropped, so its modules were "not found".

#[test]
fn latin1_byte_in_a_library_file_keeps_the_file() {
    let dir = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("library_file_latin1");
    std::fs::create_dir_all(dir.join("y")).unwrap();
    let mut text = b"// Copyright ".to_vec();
    text.push(0xAE);
    text.extend_from_slice(b" vendor\nmodule sub; localparam int X = 7; endmodule\n");
    let v = dir.join("lib.v");
    std::fs::write(&v, &text).unwrap();
    // The same comment line in a `-y` file.
    let ysub = [&text[..14], b"\nmodule ysub; localparam int Y = 9; endmodule\n"].concat();
    std::fs::write(dir.join("y").join("ysub.v"), ysub).unwrap();
    xezim_core::set_library_cli(xezim_core::LibraryCli {
        lib_files: vec![v.display().to_string()],
        lib_dirs: vec![dir.join("y").display().to_string()],
        lib_exts: Some(vec!["v".into()]),
        ..Default::default()
    });
    let m = xezim_core::parse_and_elaborate_multi(
        &["module top; sub u(); ysub w(); endmodule\n".to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("library modules found")
    .1;
    xezim_core::set_library_cli(Default::default());
    assert_eq!(m.parameters.get("u.X").and_then(|v| v.to_i64()), Some(7));
    assert_eq!(m.parameters.get("w.Y").and_then(|v| v.to_i64()), Some(9));
}
