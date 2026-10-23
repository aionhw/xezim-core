//! sv-parse: SystemVerilog parser CLI
//!
//! Usage: sv-parse [OPTIONS] <files...>
//!
//! Files with a C++ extension (`.cpp`, `.cc`, `.h`, `.hpp`, …) go through
//! the SystemC front end ([`sv_parser::systemc`]).
//!
//! Options:
//!   --dump-tokens   Print token stream
//!   --dump-ast      Print parsed AST (Rust Debug format)
//!   --dump-json     Print parsed AST as JSON — one object per file
//!                   (fields: file, source_text, ast, errors, warnings)
//!   --check         Parse only, report errors (default)
//!   --systemc       Parse every file as SystemC (C++), whatever its extension
//!   -I <dir>        Add include directory
//!   -D <name=val>   Define preprocessor macro
//!   --help          Show this help

use std::process;
use sv_parser::diagnostics::render_diagnostic;
use sv_parser::*;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 || args.contains(&"--help".to_string()) {
        eprintln!("sv-parse: SystemVerilog parser (IEEE 1800-2017/2023)");
        eprintln!();
        eprintln!("Usage: sv-parse [OPTIONS] <files...>");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --dump-tokens   Print token stream");
        eprintln!("  --dump-ast      Print parsed AST (Rust Debug format)");
        eprintln!("  --dump-json     Print parsed AST as JSON");
        eprintln!("  --check         Parse and report errors (default)");
        eprintln!("  --systemc       Parse every file as SystemC (C++)");
        eprintln!("                  (default for .cpp/.cc/.cxx/.h/.hpp/.hh files)");
        eprintln!("  -I <dir>        Add include directory");
        eprintln!("  -D <name=val>   Define preprocessor macro");
        eprintln!("  --help          Show this help");
        process::exit(0);
    }

    let mut files = Vec::new();
    let mut include_dirs = Vec::new();
    let mut defines = Vec::new();
    let mut dump_tokens = false;
    let mut dump_ast = false;
    let mut dump_json = false;
    let mut force_systemc = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--dump-tokens" => dump_tokens = true,
            "--dump-ast" => dump_ast = true,
            "--dump-json" => dump_json = true,
            "--check" => {}
            "--systemc" => force_systemc = true,
            "-I" => {
                i += 1;
                if i < args.len() {
                    include_dirs.push(args[i].clone());
                }
            }
            "-D" => {
                i += 1;
                if i < args.len() {
                    let def = &args[i];
                    if let Some(eq) = def.find('=') {
                        defines.push((def[..eq].to_string(), def[eq + 1..].to_string()));
                    } else {
                        defines.push((def.clone(), "1".to_string()));
                    }
                }
            }
            _ if args[i].starts_with("-I") => {
                include_dirs.push(args[i][2..].to_string());
            }
            _ if args[i].starts_with("-D") => {
                let def = &args[i][2..];
                if let Some(eq) = def.find('=') {
                    defines.push((def[..eq].to_string(), def[eq + 1..].to_string()));
                } else {
                    defines.push((def.to_string(), "1".to_string()));
                }
            }
            _ => files.push(args[i].clone()),
        }
        i += 1;
    }

    if files.is_empty() {
        eprintln!("Error: no input files");
        process::exit(1);
    }

    let inc_refs: Vec<&str> = include_dirs.iter().map(|s| s.as_str()).collect();
    let def_refs: Vec<(&str, &str)> = defines
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();

    let mut total_errors = 0;
    let mut total_warnings = 0;
    let mut total_modules = 0;

    for file in &files {
        if force_systemc || systemc::is_systemc_path(file) {
            let (errors, warnings, modules) =
                run_systemc(file, &inc_refs, &def_refs, dump_tokens, dump_ast, dump_json);
            total_errors += errors;
            total_warnings += warnings;
            total_modules += modules;
            continue;
        }
        if dump_tokens {
            let content = match std::fs::read_to_string(file) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("Error: {}: {}", file, e);
                    total_errors += 1;
                    continue;
                }
            };
            let tokens = tokenize(&content);
            for tok in &tokens {
                println!(
                    "{:?} {:?} @ {}..{}",
                    tok.kind, tok.text, tok.span.start, tok.span.end
                );
            }
            continue;
        }

        let result = match parse_file(file, &inc_refs, &def_refs) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("Error: {}", e);
                total_errors += 1;
                continue;
            }
        };

        for err in &result.preprocess_errors {
            eprintln!("{}", err);
        }
        let map = result.line_map.as_ref();
        for diag in result.errors.iter().chain(&result.warnings) {
            eprintln!(
                "{}",
                render_diagnostic(diag, &result.source_text, map, file)
            );
        }

        total_errors += result.errors.len() + result.preprocess_errors.len();
        total_warnings += result.warnings.len();
        total_modules += result.source.descriptions.len();

        if dump_ast {
            println!("{:#?}", result.source);
        }

        #[cfg(feature = "json-cli")]
        if dump_json {
            let envelope = serde_json::json!({
                "file": file,
                "source_text": result.source_text,
                "ast": result.source,
                "errors": result.errors,
                "warnings": result.warnings,
            });
            // JSONL: one object per file, single line — ready for
            // line-buffered consumers (xevdb's sv.py reads one per file).
            println!(
                "{}",
                serde_json::to_string(&envelope).expect("ast serialization")
            );
        }

        #[cfg(not(feature = "json-cli"))]
        if dump_json {
            eprintln!("--dump-json requires the `json-cli` cargo feature");
            process::exit(2);
        }
    }

    eprintln!(
        "Parsed {} file(s): {} module(s), {} error(s), {} warning(s)",
        files.len(),
        total_modules,
        total_errors,
        total_warnings,
    );

    if total_errors > 0 {
        process::exit(1);
    }
}

/// Parse one SystemC file; returns (errors, warnings, modules).
fn run_systemc(
    file: &str,
    include_dirs: &[&str],
    defines: &[(&str, &str)],
    dump_tokens: bool,
    dump_ast: bool,
    dump_json: bool,
) -> (usize, usize, usize) {
    if dump_tokens {
        let content = match std::fs::read_to_string(file) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Error: {}: {}", file, e);
                return (1, 0, 0);
            }
        };
        let mut pp = systemc::preprocess::Preprocessor::new(include_dirs, defines);
        for tok in pp.run(file, content) {
            println!(
                "{:?} {:?} @ {}:{}..{}",
                tok.kind, tok.text, tok.span.file, tok.span.start, tok.span.end
            );
        }
        return (0, 0, 0);
    }
    let result = match systemc::parse_file(file, include_dirs, defines) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error: {}", e);
            return (1, 0, 0);
        }
    };
    for diag in result.errors.iter().chain(&result.warnings) {
        eprintln!("{}", result.render(diag));
    }
    if dump_ast {
        println!("{:#?}", result.unit);
    }
    #[cfg(feature = "json-cli")]
    if dump_json {
        let envelope = serde_json::json!({
            "file": file,
            "language": "systemc",
            "ast": result.unit,
            "errors": result.errors,
            "warnings": result.warnings,
        });
        println!(
            "{}",
            serde_json::to_string(&envelope).expect("ast serialization")
        );
    }
    #[cfg(not(feature = "json-cli"))]
    if dump_json {
        eprintln!("--dump-json requires the `json-cli` cargo feature");
        process::exit(2);
    }
    (
        result.errors.len(),
        result.warnings.len(),
        result.unit.modules().len(),
    )
}
