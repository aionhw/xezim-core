//! VHDL front end: the vendored standard packages parse, and syntax errors
//! are reported once per design unit at their source location.

use xezim_core::vhdl;

/// Every vendored `std`/`ieee` source (IEEE P1076 WG packages) parses with
/// no syntax error.
#[test]
fn vendored_libraries_parse() {
    assert!(vhdl::libraries::SOURCES.len() >= 25);
    for s in vhdl::libraries::SOURCES {
        let errs = vhdl::check_syntax(s.file, s.text);
        assert!(
            errs.is_empty(),
            "{}/{}:\n{}",
            s.library,
            s.file,
            errs.join("\n")
        );
    }
}

/// One error per design unit, at line:column of the offending token, with
/// the source line and a caret.
#[test]
fn syntax_error_located_once_per_unit() {
    let src = b"entity a is\n  port (x : in bit\nend entity;\n\nentity b is\nend entity;\n\narchitecture r of b is\nbegin\n  process begin\n    wait until;\n  end process;\nend architecture;\n";
    let errs = vhdl::check_syntax("bad.vhd", src);
    assert_eq!(errs.len(), 2, "{}", errs.join("\n"));
    assert!(
        errs[0].starts_with("bad.vhd:2:19: error: VHDL: syntax error: Expected ';' or ')'"),
        "{}",
        errs[0]
    );
    assert!(errs[0].contains("2 |   port (x : in bit"), "{}", errs[0]);
    assert!(
        errs[1].starts_with("bad.vhd:11:15: error: VHDL: syntax error:"),
        "{}",
        errs[1]
    );
    assert!(errs[1].contains("^"), "{}", errs[1]);
}

#[test]
fn vhdl_paths() {
    assert!(vhdl::is_vhdl_path("a/b/top.vhd"));
    assert!(vhdl::is_vhdl_path("PKG.VHDL"));
    assert!(!vhdl::is_vhdl_path("top.v"));
    assert!(!vhdl::is_vhdl_path("top.sv"));
}

/// External corpus check (not run by default): every `.vhd`/`.vhdl` file
/// under `$XEZIM_VHDL_CORPUS` parses and converts with no error, except
/// the files listed in `$XEZIM_VHDL_CORPUS_SKIP` (comma-separated names).
#[test]
#[ignore]
fn external_corpus_converts() {
    let Some(dir) = std::env::var_os("XEZIM_VHDL_CORPUS") else {
        return;
    };
    let skip: Vec<String> = std::env::var("XEZIM_VHDL_CORPUS_SKIP")
        .map(|s| s.split(',').map(str::to_string).collect())
        .unwrap_or_default();
    let mut stack = vec![std::path::PathBuf::from(dir)];
    let (mut files, mut bad) = (0, Vec::new());
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else if vhdl::is_vhdl_path(&p.to_string_lossy())
                && !skip.iter().any(|s| p.ends_with(s))
            {
                files += 1;
                let errs = vhdl::check_syntax(&p.to_string_lossy(), &std::fs::read(&p).unwrap());
                if !errs.is_empty() {
                    bad.push(errs[0].clone());
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "{} of {} files:\n{}",
        bad.len(),
        files,
        bad.join("\n")
    );
}
