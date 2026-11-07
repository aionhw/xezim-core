//! #937: a `-v` library file supplies only modules, interfaces, programs and
//! primitives, so the packages it declares are not compiled and an import of
//! one is an error. `--relax-library-packages` (`RELAX_LIBRARY_PACKAGES`)
//! compiles them, as if the file were also a source file; a package a source
//! file declares wins. One test, since the switch and the library list are
//! process-wide.

fn elaborate(src: &str, lib: &std::path::Path) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::set_library_cli(xezim_core::LibraryCli {
        lib_files: vec![lib.display().to_string()],
        ..Default::default()
    });
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".into()],
        &[],
    )
    .map(|(_, m)| m)
}

#[test]
fn relax_library_packages_compiles_a_v_file_package() {
    let dir = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("relax_lib_pkg_937");
    std::fs::create_dir_all(&dir).unwrap();
    let lib = dir.join("lib.v");
    std::fs::write(
        &lib,
        "package LP; localparam int W = 5; endpackage\nmodule unused_cell; endmodule\n",
    )
    .unwrap();
    let top = "module top; import LP::*; localparam int X = W + 1; endmodule";

    xezim_core::sv_parser::RELAX_LIBRARY_PACKAGES.set(false);
    let err = elaborate(top, &lib).expect_err("not compiled by default");
    assert!(err.contains("Package 'LP' not found"), "{err}");
    assert!(err.contains("--relax-library-packages"), "{err}");

    xezim_core::sv_parser::RELAX_LIBRARY_PACKAGES.set(true);
    let m = elaborate(top, &lib).expect("compiled with the switch");
    assert_eq!(m.parameters.get("X").and_then(|v| v.to_i64()), Some(6));
    assert!(m.packages.contains("LP"));

    let own = "package LP; localparam int W = 9; endpackage\n".to_string() + top;
    let m = elaborate(&own, &lib).expect("source package wins");
    assert_eq!(m.parameters.get("X").and_then(|v| v.to_i64()), Some(10));
    xezim_core::sv_parser::RELAX_LIBRARY_PACKAGES.set(false);
}
