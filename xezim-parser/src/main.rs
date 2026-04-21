//! sv-parse: SystemVerilog parser CLI
//!
//! Usage: sv-parse [OPTIONS] <files...>
//!
//! Options:
//!   --dump-tokens   Print token stream
//!   --dump-ast      Print parsed AST
//!   --check         Parse only, report errors (default)
//!   -I <dir>        Add include directory
//!   -D <name=val>   Define preprocessor macro
//!   --help          Show this help

use sv_parser::*;
use sv_parser::diagnostics::format_diagnostic;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 || args.contains(&"--help".to_string()) {
        eprintln!("sv-parse: SystemVerilog parser (IEEE 1800-2017/2023)");
        eprintln!();
        eprintln!("Usage: sv-parse [OPTIONS] <files...>");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --dump-tokens   Print token stream");
        eprintln!("  --dump-ast      Print parsed AST");
        eprintln!("  --check         Parse and report errors (default)");
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

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--dump-tokens" => dump_tokens = true,
            "--dump-ast" => dump_ast = true,
            "--check" => {}
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
    let def_refs: Vec<(&str, &str)> = defines.iter().map(|(k, v)| (k.as_str(), v.as_str())).collect();

    let mut total_errors = 0;
    let mut total_warnings = 0;
    let mut total_modules = 0;

    for file in &files {
        if dump_tokens {
            let content = match std::fs::read_to_string(file) {
                Ok(c) => c,
                Err(e) => { eprintln!("Error: {}: {}", file, e); total_errors += 1; continue; }
            };
            let tokens = tokenize(&content);
            for tok in &tokens {
                println!("{:?} {:?} @ {}..{}", tok.kind, tok.text, tok.span.start, tok.span.end);
            }
            continue;
        }

        let result = match parse_file(file, &inc_refs, &def_refs) {
            Ok(r) => r,
            Err(e) => { eprintln!("Error: {}", e); total_errors += 1; continue; }
        };

        for err in &result.errors {
            eprintln!("{}", format_diagnostic(&result.source_text, err).replace("<source>", file));
        }
        for warn in &result.warnings {
            eprintln!("{}", format_diagnostic(&result.source_text, warn).replace("<source>", file));
        }

        total_errors += result.errors.len();
        total_warnings += result.warnings.len();
        total_modules += result.source.descriptions.len();

        if dump_ast {
            println!("{:#?}", result.source);
        }
    }

    eprintln!(
        "Parsed {} file(s): {} module(s), {} error(s), {} warning(s)",
        files.len(), total_modules, total_errors, total_warnings,
    );

    if total_errors > 0 {
        process::exit(1);
    }
}
