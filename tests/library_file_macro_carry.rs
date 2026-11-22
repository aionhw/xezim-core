//! §22.5.1, §3.12.1: the macros a `-v`/`-y` library file is preprocessed
//! with (`LibraryCli::macro_carry`). By default, as in the reference
//! simulator, a library file starts from the command-line defines only: no
//! macro of a source file or of another library file reaches it.
//! `Source` (`--carry-src-macros`) adds the macros the source files left
//! defined; `Library` (`--carry-lib-macros`) adds as well those of the
//! library files read before it, in read order. No library macro reaches a
//! source file in any mode. One test, since the library list is
//! process-wide.

use std::path::Path;
use xezim_core::LibraryMacroCarry as Carry;

const MODES: [Carry; 3] = [Carry::None, Carry::Source, Carry::Library];

fn write(dir: &Path, name: &str, text: &str) {
    let p = dir.join(name);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

/// `u.l.X` of `top` → `mid u` → `leaf l`, where the leaf sets `X` to `W`, or
/// to -1 with `W` undefined; and `TOPX`, which the top sets the same way
/// after the instance.
fn run(
    dir: &Path,
    top_macros: &str,
    defines: &[(&str, &str)],
    cli: xezim_core::LibraryCli,
) -> (Option<i64>, Option<i64>) {
    xezim_core::set_library_cli(cli);
    let top = format!(
        "{top_macros}module top;\n  mid u();\n`ifdef W\n  localparam int TOPX = `W;\n`else\n  localparam int TOPX = -1;\n`endif\nendmodule\n"
    );
    let defines: Vec<(String, Option<String>)> = defines
        .iter()
        .map(|(n, v)| (n.to_string(), Some(v.to_string())))
        .collect();
    let m = xezim_core::parse_and_elaborate_multi(
        &[top],
        Some("top"),
        &[dir.display().to_string()],
        &[dir.join("top.sv").display().to_string()],
        &defines,
    )
    .map(|(_, m)| m)
    .expect("elaborate");
    let get = |n: &str| m.parameters.get(n).and_then(|v| v.to_i64());
    (get("u.l.X"), get("TOPX"))
}

#[test]
fn library_file_macros_follow_the_carry_mode() {
    let dir =
        std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("library_file_macro_carry");
    let _ = std::fs::remove_dir_all(&dir);
    let leaf = "module leaf;\n`ifdef W\n  localparam int X = `W;\n`else\n  localparam int X = -1;\n`endif\nendmodule\n";
    write(&dir, "defs.vh", "`define W 5\n");
    write(
        &dir,
        "v/mid.v",
        "`define W 5\nmodule mid;\n  leaf l();\nendmodule\n",
    );
    write(&dir, "v/leaf.v", leaf);
    write(
        &dir,
        "v/plain_mid.v",
        "module mid;\n  leaf l();\nendmodule\n",
    );
    write(
        &dir,
        "y/mid.v",
        "`include \"defs.vh\"\nmodule mid;\n  leaf l();\nendmodule\n",
    );
    write(&dir, "y/leaf.v", leaf);
    let v = |names: &[&str], carry| xezim_core::LibraryCli {
        lib_files: names
            .iter()
            .map(|n| dir.join("v").join(n).display().to_string())
            .collect(),
        macro_carry: carry,
        ..Default::default()
    };
    let y = |carry| xezim_core::LibraryCli {
        lib_dirs: vec![dir.join("y").display().to_string()],
        lib_exts: Some(vec!["v".into()]),
        macro_carry: carry,
        ..Default::default()
    };
    for carry in MODES {
        let lib = |want_lib: i64| {
            if carry == Carry::Library {
                want_lib
            } else {
                -1
            }
        };
        let src = |want_src: i64, want_none: i64| {
            if carry == Carry::None {
                want_none
            } else {
                want_src
            }
        };
        // `-v` files: one library file's macro reaches a later one only under
        // `Library`, and never an earlier one.
        let (x, topx) = run(&dir, "", &[], v(&["mid.v", "leaf.v"], carry));
        assert_eq!((x, topx), (Some(lib(5)), Some(-1)), "{carry:?} forward");
        let (x, topx) = run(&dir, "", &[], v(&["leaf.v", "mid.v"], carry));
        assert_eq!((x, topx), (Some(-1), Some(-1)), "{carry:?} reversed");
        // `-y`: the macro of a header the module that instantiates the leaf
        // includes.
        let (x, topx) = run(&dir, "", &[], y(carry));
        assert_eq!((x, topx), (Some(lib(5)), Some(-1)), "{carry:?} -y");
        // A source file's macro reaches a library file under `Source` and
        // `Library`.
        let (x, topx) = run(
            &dir,
            "`define W 7\n",
            &[],
            v(&["plain_mid.v", "leaf.v"], carry),
        );
        assert_eq!(
            (x, topx),
            (Some(src(7, -1)), Some(7)),
            "{carry:?} source macro"
        );
        // A command-line define reaches every library file; a source file
        // that redefines it passes its own value on only when it carries.
        let (x, topx) = run(
            &dir,
            "",
            &[("W", "3")],
            v(&["plain_mid.v", "leaf.v"], carry),
        );
        assert_eq!(
            (x, topx),
            (Some(3), Some(3)),
            "{carry:?} command-line define"
        );
        let (x, topx) = run(
            &dir,
            "`define W 7\n",
            &[("W", "3")],
            v(&["plain_mid.v", "leaf.v"], carry),
        );
        assert_eq!((x, topx), (Some(src(7, 3)), Some(7)), "{carry:?} redefined");
        // The `-y` leaf with the command-line define and no header.
        write(&dir, "y2/mid.v", "module mid;\n  leaf l();\nendmodule\n");
        write(&dir, "y2/leaf.v", leaf);
        let cli = xezim_core::LibraryCli {
            lib_dirs: vec![dir.join("y2").display().to_string()],
            lib_exts: Some(vec!["v".into()]),
            macro_carry: carry,
            ..Default::default()
        };
        let (x, _) = run(&dir, "", &[("W", "4")], cli);
        assert_eq!(x, Some(4), "{carry:?} -y command-line define");
    }
    // A library file that uses a macro it does not see, which a carry
    // switch would pass it, gets a note naming that switch.
    write(
        &dir,
        "v/use_leaf.v",
        "module leaf;\n  localparam int X = `W;\nendmodule\n",
    );
    // The leaf does not parse without `W`, so the design does not elaborate.
    let notes = |top_macros: &str, cli| {
        xezim_core::set_library_cli(cli);
        xezim_core::elab_diag_capture_begin();
        let _ = xezim_core::parse_and_elaborate_multi(
            &[format!("{top_macros}module top;\n  mid u();\nendmodule\n")],
            Some("top"),
            &[dir.display().to_string()],
            &[dir.join("top.sv").display().to_string()],
            &[],
        );
        xezim_core::elab_diag_capture_take()
            .into_iter()
            .filter(|m| m.contains("uses macro `W"))
            .collect::<Vec<_>>()
    };
    for (top_macros, files, carry, switch) in [
        (
            "",
            ["mid.v", "use_leaf.v"],
            Carry::None,
            Some("--carry-lib-macros"),
        ),
        (
            "",
            ["mid.v", "use_leaf.v"],
            Carry::Source,
            Some("--carry-lib-macros"),
        ),
        ("", ["mid.v", "use_leaf.v"], Carry::Library, None),
        (
            "`define W 7\n",
            ["plain_mid.v", "use_leaf.v"],
            Carry::None,
            Some("--carry-src-macros"),
        ),
        (
            "`define W 7\n",
            ["plain_mid.v", "use_leaf.v"],
            Carry::Source,
            None,
        ),
        ("", ["use_leaf.v", "mid.v"], Carry::None, None),
    ] {
        let found = notes(top_macros, v(&files, carry));
        match switch {
            Some(switch) => assert!(
                found.len() == 1 && found[0].contains(switch) && found[0].contains("use_leaf.v"),
                "{carry:?} {files:?}: {found:?}"
            ),
            None => assert!(found.is_empty(), "{carry:?} {files:?}: {found:?}"),
        }
    }
    xezim_core::set_library_cli(Default::default());
}
