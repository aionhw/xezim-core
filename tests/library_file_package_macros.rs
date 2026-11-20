//! §22.5.1 with `--relax-library-packages` (`RELAX_LIBRARY_PACKAGES`): the
//! packages of the `-v` files are compiled in a pass of their own, before
//! their modules are indexed. Both passes read the files in command-line
//! order, each from the macros the design and the files before it left, so
//! a macro one library file defines selects the same `` `ifdef `` branch of a
//! later one in both, and the module adopted from that branch imports the
//! package compiled from it. The package pass used to start every file from
//! the design's macros only: it compiled the other branch's package, and the
//! import failed. One test, since the switch and the library list are
//! process-wide.

#[test]
fn library_file_macros_reach_the_package_pass() {
    let dir = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("library_file_package_macros");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    // A library file with no package defines the macro.
    let feature = dir.join("feature.v");
    std::fs::write(&feature, "`define FEATURE\nmodule unused_cell; endmodule\n").unwrap();
    let leaf = dir.join("leaf.v");
    std::fs::write(
        &leaf,
        "`ifdef FEATURE\n\
         package pk_on; localparam int V = 7; endpackage\n\
         module leaf; import pk_on::*; localparam int X = V; endmodule\n\
         `else\n\
         package pk_off; localparam int V = 3; endpackage\n\
         module leaf; import pk_off::*; localparam int X = V; endmodule\n\
         `endif\n",
    )
    .unwrap();
    xezim_core::set_library_cli(xezim_core::LibraryCli {
        lib_files: vec![feature.display().to_string(), leaf.display().to_string()],
        ..Default::default()
    });
    xezim_core::sv_parser::RELAX_LIBRARY_PACKAGES.set(true);
    let m = xezim_core::parse_and_elaborate_multi(
        &["module top; leaf u(); endmodule\n".to_string()],
        Some("top"),
        &[],
        &["top.sv".into()],
        &[],
    )
    .map(|(_, m)| m);
    xezim_core::sv_parser::RELAX_LIBRARY_PACKAGES.set(false);
    xezim_core::set_library_cli(Default::default());
    let m = m.expect("the adopted leaf imports the package compiled from its branch");
    assert_eq!(m.parameters.get("u.X").and_then(|v| v.to_i64()), Some(7));
    assert!(m.packages.contains("pk_on"));
    assert!(!m.packages.contains("pk_off"));
}
