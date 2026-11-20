//! §22.5.1, §3.12.1: a text macro a `-y`/`-v` library file defines, itself
//! or through an `include` of the design's headers, stays defined for the
//! library files read after it: library files are read as part of the one
//! compilation, in the order their modules are resolved. Each library file
//! used to start from the primary sources' macros only, so a library module
//! that included the headers did not share them with the library modules it
//! instantiates. One test, since the library list is process-wide.

use std::path::Path;

fn elaborate(dir: &Path, cli: xezim_core::LibraryCli) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::set_library_cli(cli);
    let top = "module top;\n  mid u();\nendmodule\n";
    xezim_core::parse_and_elaborate_multi(
        &[top.to_string()],
        Some("top"),
        &[dir.display().to_string()],
        &[dir.join("top.v").display().to_string()],
        &[],
    )
    .map(|(_, m)| m)
}

fn write(dir: &Path, name: &str, text: &str) {
    let p = dir.join(name);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

fn y(dirs: &[&Path]) -> xezim_core::LibraryCli {
    xezim_core::LibraryCli {
        lib_dirs: dirs.iter().map(|d| d.display().to_string()).collect(),
        lib_exts: Some(vec!["v".into()]),
        ..Default::default()
    }
}

#[test]
fn library_file_macros_reach_later_library_files() {
    let dir = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("library_file_macros");
    let _ = std::fs::remove_dir_all(&dir);
    write(&dir, "defs.vh", "`define W 5\n");
    let mid = "`include \"defs.vh\"\nmodule mid;\n  LEAF l();\nendmodule\n";
    let leaf = "module LEAF;\n  localparam int X = `W;\nendmodule\n";
    // The leaf sorts before and after the module that includes the header.
    for (sub, name) in [("lib2", "aleaf"), ("lib3", "zleaf")] {
        write(&dir, &format!("{sub}/mid.v"), &mid.replace("LEAF", name));
        write(&dir, &format!("{sub}/{name}.v"), &leaf.replace("LEAF", name));
        let m = elaborate(&dir, y(&[&dir.join(sub)])).expect(sub);
        assert_eq!(m.parameters.get("u.l.X").and_then(|v| v.to_i64()), Some(5), "{sub}");
    }
    // The two files in different `-y` directories.
    write(&dir, "lib4a/aleaf.v", &leaf.replace("LEAF", "aleaf"));
    write(&dir, "lib4b/mid.v", &mid.replace("LEAF", "aleaf"));
    let m = elaborate(&dir, y(&[&dir.join("lib4a"), &dir.join("lib4b")])).expect("lib4");
    assert_eq!(m.parameters.get("u.l.X").and_then(|v| v.to_i64()), Some(5));
    // `-v` files, read in command-line order; a later `undef` takes the
    // macro away again.
    write(&dir, "v/mid.v", &mid.replace("LEAF", "aleaf"));
    write(&dir, "v/aleaf.v", &leaf.replace("LEAF", "aleaf"));
    let v = |names: &[&str]| xezim_core::LibraryCli {
        lib_files: names
            .iter()
            .map(|n| dir.join("v").join(n).display().to_string())
            .collect(),
        ..Default::default()
    };
    let m = elaborate(&dir, v(&["mid.v", "aleaf.v"])).expect("-v");
    assert_eq!(m.parameters.get("u.l.X").and_then(|v| v.to_i64()), Some(5));
    write(&dir, "v/undef.v", "`undef W\n");
    let undefined = elaborate(&dir, v(&["mid.v", "undef.v", "aleaf.v"]));
    assert!(
        undefined
            .as_ref()
            .map_or(true, |m| m.parameters.get("u.l.X").and_then(|v| v.to_i64()) != Some(5)),
        "`undef in a library file read before was ignored"
    );
    // A file named twice is read twice. Its text for `--dump-merged-sv` is
    // that of the read its module came from, not the second read, which its
    // include guard leaves empty.
    let guarded = dir.join("guard").join("mid.v");
    write(&dir, "guard/mid.v", "`ifndef MID_V\n`define MID_V\nmodule mid;\nendmodule\n`endif\n");
    let twice = guarded.display().to_string();
    let cli = xezim_core::LibraryCli {
        lib_files: vec![twice.clone(), twice],
        ..Default::default()
    };
    elaborate(&dir, cli).expect("guarded file named twice");
    let text = xezim_core::preprocess_adopted_lib(&guarded).expect("the adopted file's text");
    assert!(text.contains("module mid"), "{text}");
    xezim_core::set_library_cli(Default::default());
}
