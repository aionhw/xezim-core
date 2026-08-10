//! SystemVerilog preprocessor (IEEE 1800-2017 §22)
//!
//! Handles `define, `ifdef/`ifndef/`else/`endif, `include, `undef, etc.
//! This is a simplified preprocessor suitable for parsing purposes.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
pub struct MacroDef {
    pub name: String,
    /// Formal parameters as (name, default) pairs. `default` is `Some` when the
    /// macro declares a default value (`P=`, `P=expr`); an empty default is
    /// `Some("")`. Actual args that are missing or blank fall back to it.
    pub params: Option<Vec<(String, Option<String>)>>,
    pub body: String,
}

pub struct Preprocessor {
    defines: HashMap<String, MacroDef>,
    /// Directories to search for `include files (in order).
    /// The directory of the current source file is always searched first.
    include_dirs: Vec<PathBuf>,
    /// Current include depth (to prevent infinite recursion).
    include_depth: usize,
    /// Current source file path (for `__FILE__` expansion). Updated on entry
    /// to `resolve_directives` and across `include nesting.
    current_file: String,
    /// 1-based line number within `current_file` of the line being processed
    /// (for `__LINE__` expansion).
    current_line: u32,
    /// Active `begin_keywords` stack — each entry holds the (validated)
    /// version string that pushed it. End_keywords pops one. Tracked so that
    /// invalid version strings can be reported and (future) per-region
    /// keyword sets can be wired in. SV-2023 §22.14.
    keywords_stack: Vec<String>,
    /// Most-recently-seen `\`timescale` directive parsed to (unit_s, prec_s)
    /// in seconds (e.g. 1ns → 1e-9). The simulation tick is the finest
    /// precision declared in the design, so any precision is honoured.
    /// LRM §22.7.
    timescale: Option<(f64, f64)>,
    /// Per-design-element timescale: `module/interface/program/package name →
    /// (unit_s, prec_s)`, captured as each declaration is emitted so the
    /// elaborator/simulator can scale that scope's delays by its own timeunit
    /// (LRM §22.7 — a `timescale` applies to all following declarations until the
    /// next directive, persisting across files in compilation order).
    pub module_timescales: std::collections::HashMap<String, (f64, f64)>,
    /// Modules whose active `\`timescale` was declared in their OWN top-level
    /// file (vs. inherited sticky from a prior file). `--module-timescale`
    /// overrides a cross-file-INHERITED directive but NOT an own-file one, so
    /// the driver needs to tell the two apart. Reset per top-level file via
    /// `begin_top_level_file`.
    pub module_ts_own_file: std::collections::HashSet<String>,
    /// True once a `\`timescale` directive has been seen in the CURRENT
    /// top-level file (set by the directive handler, cleared per file).
    current_file_ts: bool,
    /// §22 strict-mode directive errors (bad `\`line`/`\`define`/`\`pragma`/
    /// `\`resetall`). Collected only when `strict_checks()` is on; the driver
    /// treats a non-empty list as a hard failure (non-zero exit).
    errors: Vec<String>,
    /// Nesting depth of open design elements (module/interface/package/…),
    /// tracked line-by-line so `\`resetall` inside one can be flagged (§22.3).
    design_element_depth: i32,
    /// §22.9: pull direction of the ACTIVE `unconnected_drive region
    /// (Some(true)=pull1, Some(false)=pull0), None outside a region.
    unconnected_pull: Option<bool>,
    /// Macro-expansion-time strict errors (bad argument counts). Interior
    /// mutability because `expand_macros*` run behind `&self`; drained into
    /// `errors` after each line is expanded.
    expansion_errors: std::cell::RefCell<Vec<String>>,
    /// Names already reported by `note_undefined_macro`, so a macro used in a
    /// loop or an `include pulled in many times warns once rather than once
    /// per use.
    reported_undefined: std::cell::RefCell<HashSet<String>>,
}

const MAX_INCLUDE_DEPTH: usize = 32;

#[derive(Clone, Copy)]
struct IfdefState {
    parent_active: bool,
    branch_taken: bool,
    active: bool,
}

impl Preprocessor {
    /// Seed the predefined `$coverage_control` constants (IEEE 1800-2023
    /// §39.6). Called by `new()` and again by `undefineall` so the
    /// predefined names survive a wipe of user-defined macros.
    fn seed_predefined(defines: &mut HashMap<String, MacroDef>) {
        for (name, val) in [
            ("SV_COV_START", "0"),
            ("SV_COV_STOP", "1"),
            ("SV_COV_RESET", "2"),
            ("SV_COV_CHECK", "3"),
            ("SV_COV_MODULE", "10"),
            ("SV_COV_HIER", "11"),
            ("SV_COV_ASSERTION", "20"),
            ("SV_COV_FSM_STATE", "21"),
            ("SV_COV_STATEMENT", "22"),
            ("SV_COV_TOGGLE", "23"),
            ("SV_COV_OVERFLOW", "-2"),
            ("SV_COV_ERROR", "-1"),
            ("SV_COV_NOCOV", "0"),
            ("SV_COV_OK", "1"),
            ("SV_COV_PARTIAL", "2"),
        ] {
            defines.insert(name.to_string(), MacroDef {
                name: name.to_string(),
                params: None,
                body: val.to_string(),
            });
        }
    }

    pub fn new() -> Self {
        let mut defines = HashMap::new();
        Self::seed_predefined(&mut defines);
        Self {
            defines,
            include_dirs: Vec::new(),
            include_depth: 0,
            current_file: String::new(),
            current_line: 0,
            keywords_stack: Vec::new(),
            timescale: None,
            module_timescales: std::collections::HashMap::new(),
            module_ts_own_file: std::collections::HashSet::new(),
            current_file_ts: false,
            errors: Vec::new(),
            design_element_depth: 0,
            unconnected_pull: None,
            expansion_errors: std::cell::RefCell::new(Vec::new()),
            reported_undefined: std::cell::RefCell::new(HashSet::new()),
        }
    }

    /// Strict-mode directive errors collected during preprocessing (empty
    /// unless `strict_checks()` is on and an illegal directive was seen).
    /// Report a `\`name` that no `\`define` (and no compiler directive) covers,
    /// once per name, naming the file and line of the first use.
    ///
    /// Standard compiler directives reach this path too when they appear in a
    /// position `resolve_directives` does not handle, and an unrecognised
    /// tool-specific pragma is legitimate input, so this warns rather than
    /// failing the build. It is written straight to stderr because the
    /// preprocessor's own error list only surfaces on the `--preprocess` path,
    /// and this is most useful precisely when compiling.
    fn note_undefined_macro(&self, name: &str) {
        const DIRECTIVES: &[&str] = &[
            "define", "undef", "undefineall", "ifdef", "ifndef", "elsif",
            "else", "endif", "include", "line", "pragma", "resetall",
            "timescale", "begin_keywords", "end_keywords",
            "default_nettype", "celldefine", "endcelldefine",
            "unconnected_drive", "nounconnected_drive", "protect",
            "endprotect", "protected", "endprotected", "uselib", "default_decay_time",
            "default_trireg_strength", "delay_mode_distributed", "delay_mode_path",
            "delay_mode_unit", "delay_mode_zero", "accelerate", "noaccelerate",
            "autoexpand_vectornets", "expand_vectornets", "noexpand_vectornets",
            "remove_gatenames", "noremove_gatenames", "remove_netnames",
            "noremove_netnames", "suppress_faults", "nosuppress_faults",
            "enable_portfaults", "disable_portfaults", "signed", "unsigned",
        ];
        if name.is_empty() || DIRECTIVES.contains(&name) {
            return;
        }
        if !self.reported_undefined.borrow_mut().insert(name.to_string()) {
            return;
        }
        eprintln!(
            "[{}] {}: warning: macro `{} is undefined (IEEE 1800-2017 §22.5.1) \
             — it is left as literal text, which usually causes a syntax error \
             at the point of use",
            self.current_file, self.current_line, name
        );
    }

    pub fn errors(&self) -> &[String] {
        &self.errors
    }

    fn push_error_here(&mut self, message: String) {
        let file = if self.current_file.is_empty() {
            "<input>"
        } else {
            self.current_file.as_str()
        };
        self.errors
            .push(format!("{}:{}: {}", file, self.current_line.max(1), message));
    }

    /// True when `trimmed` is the directive `\`<name>` followed by whitespace
    /// or end-of-line (so `\`line` matches but `\`linefoo` does not).
    /// §34.2: does this `pragma`'s argument list OPEN a protected envelope?
    /// Matches both `protect begin_protected` and the short `protect begin`.
    /// A `begin_protected` may be followed by further arguments on the same
    /// line, so only the leading keywords are inspected.
    fn protect_envelope_opens(args: &str) -> bool {
        let mut it = args.split_whitespace();
        if it.next() != Some("protect") {
            return false;
        }
        matches!(it.next(), Some("begin_protected") | Some("begin"))
    }

    /// §34.2: does this `pragma`'s argument list CLOSE a protected envelope?
    fn protect_envelope_closes(args: &str) -> bool {
        let mut it = args.split_whitespace();
        if it.next() != Some("protect") {
            return false;
        }
        matches!(it.next(), Some("end_protected") | Some("end"))
    }

    fn is_directive(trimmed: &str, name: &str) -> bool {
        let tick = format!("`{}", name);
        if let Some(rest) = trimmed.strip_prefix(&tick) {
            rest.is_empty() || rest.starts_with(|c: char| c.is_whitespace())
        } else {
            false
        }
    }

    /// Update the design-element nesting depth from one source line. Opening
    /// keywords increment; `end…` keywords decrement (floored at 0).
    fn update_design_depth(trimmed: &str, depth: &mut i32) {
        let first = trimmed.split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .next().unwrap_or("");
        match first {
            "module" | "macromodule" | "interface" | "package" | "program"
            | "primitive" | "checker" => *depth += 1,
            "endmodule" | "endinterface" | "endpackage" | "endprogram"
            | "endprimitive" | "endchecker" => {
                if *depth > 0 { *depth -= 1; }
            }
            _ => {}
        }
    }

    /// §22.12: validate `\`line <number> "<filename>" <level>`.
    fn check_line_directive(&mut self, trimmed: &str) {
        let rest = trimmed["`line".len()..].trim();
        // number "filename" level — split into the integer, the quoted string,
        // and the level. The filename may contain spaces, so parse positionally.
        let num_tok = rest.split_whitespace().next().unwrap_or("");
        let after_num = rest[num_tok.len()..].trim_start();
        let mut bad = false;
        let mut why = String::new();
        // number: positive integer
        if num_tok.parse::<u32>().is_err() {
            bad = true; why = format!("number `{}` must be a positive integer", num_tok);
        } else if !after_num.starts_with('"') {
            bad = true;
            if after_num.is_empty() {
                why = "missing filename and level".into();
            } else {
                why = "filename must be a string literal".into();
            }
        } else if let Some(end) = after_num[1..].find('"') {
            let level = after_num[1 + end + 1..].trim();
            if !matches!(level, "0" | "1" | "2") {
                // Reference tools accept an out-of-range level with a
                // WARNING (number/filename still apply) — a hard error here
                // failed otherwise-valid third-party sources.
                eprintln!(
                    "[PP] warning: {}:{}: `line level `{}` is not 0/1/2 \
                     (IEEE 1800-2017 §22.12) — ignored",
                    self.current_file, self.current_line, level
                );
            }
        } else {
            bad = true; why = "unterminated filename string".into();
        }
        if bad {
            self.push_error_here(format!(
                "illegal `line directive (IEEE 1800-2017 §22.12): {}", why));
        }
    }

    /// Parse a `1ns`-style time literal into seconds. Returns None on
    /// malformed input. LRM §22.7 Table 22-5 — units are s/ms/us/ns/ps/fs
    /// and the mantissa must be 1, 10, or 100.
    fn parse_time_literal(s: &str) -> Option<f64> {
        let s = s.trim();
        let (num_str, unit) = if let Some(stripped) = s.strip_suffix("fs") { (stripped, 1e-15) }
            else if let Some(stripped) = s.strip_suffix("ps") { (stripped, 1e-12) }
            else if let Some(stripped) = s.strip_suffix("ns") { (stripped, 1e-9) }
            else if let Some(stripped) = s.strip_suffix("us") { (stripped, 1e-6) }
            else if let Some(stripped) = s.strip_suffix("ms") { (stripped, 1e-3) }
            else if let Some(stripped) = s.strip_suffix("s")  { (stripped, 1.0) }
            else { return None; };
        let mantissa: f64 = num_str.trim().parse().ok()?;
        if mantissa != 1.0 && mantissa != 10.0 && mantissa != 100.0 { return None; }
        Some(mantissa * unit)
    }

    /// Return the most recent `timescale` (unit_s, prec_s) seen, if any.
    pub fn timescale(&self) -> Option<(f64, f64)> {
        self.timescale
    }

    /// Call before preprocessing each TOP-LEVEL source file. Marks the start of
    /// a new file so a `\`timescale` inherited (sticky) from a PRIOR file is not
    /// counted as declared in this file — which is what lets `--module-timescale`
    /// override a cross-file-inherited timescale but not an own-file one.
    pub fn begin_top_level_file(&mut self) {
        self.current_file_ts = false;
    }

    /// If `line` begins a design-element declaration
    /// (`module`/`macromodule`/`interface`/`program`/`package <name>`), return
    /// its name. Used to associate the active timescale with each scope.
    fn design_element_name(line: &str) -> Option<String> {
        let t = line.trim_start();
        for kw in ["macromodule", "module", "interface", "program", "package"] {
            if let Some(rest) = t.strip_prefix(kw) {
                if !rest.starts_with(char::is_whitespace) { continue; }
                let mut rest = rest.trim_start();
                // skip an optional lifetime qualifier
                for q in ["static", "automatic"] {
                    if let Some(r2) = rest.strip_prefix(q) {
                        if r2.starts_with(char::is_whitespace) { rest = r2.trim_start(); }
                    }
                }
                let name: String = rest
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '$')
                    .collect();
                if name.chars().next().map_or(false, |c| c.is_alphabetic() || c == '_') {
                    return Some(name);
                }
            }
        }
        None
    }

    /// Set include search directories.
    pub fn set_include_dirs(&mut self, dirs: Vec<PathBuf>) {
        self.include_dirs = dirs;
    }

    /// Add an include search directory.
    pub fn add_include_dir(&mut self, dir: PathBuf) {
        if !self.include_dirs.contains(&dir) {
            self.include_dirs.push(dir);
        }
    }

    pub fn with_defines(defines: HashMap<String, String>) -> Self {
        let mut pp = Self::new();
        for (k, v) in defines {
            pp.defines.insert(k.clone(), MacroDef {
                name: k,
                params: None,
                body: v,
            });
        }
        pp
    }

    pub fn define(&mut self, name: String, value: MacroDef) {
        self.defines.insert(name, value);
    }

    pub fn snapshot_defines(&self) -> HashMap<String, MacroDef> {
        self.defines.clone()
    }

    pub fn is_defined(&self, name: &str) -> bool {
        matches!(name, "__FILE__" | "__LINE__") || self.defines.contains_key(name)
    }

    /// Preprocess source text, resolving `include directives relative to `source_path`.
    /// If `source_path` is None, `include directives that require file I/O are skipped.
    pub fn preprocess_file(&mut self, source: &str, source_path: Option<&Path>) -> String {
        // Automatically add the source file's parent directory to include search
        if let Some(path) = source_path {
            if let Some(parent) = path.parent() {
                let parent = if parent.as_os_str().is_empty() {
                    PathBuf::from(".")
                } else {
                    parent.to_path_buf()
                };
                self.add_include_dir(parent);
            }
        }
        let stripped = self.strip_comments(source);
        let resolved = self.resolve_directives(&stripped, source_path);
        Self::strip_attributes(&resolved)
    }

    /// Simple preprocessing pass (no file context — `include lines are skipped).
    pub fn preprocess(&mut self, source: &str) -> String {
        // Reset per-source compiler-directive state so a `none`
        // directive from a previous file in the same process doesn't
        // pollute this one.
        crate::set_default_nettype_none_seen(false);
        let stripped = self.strip_comments(source);
        let resolved = self.resolve_directives(&stripped, None);
        Self::strip_attributes(&resolved)
    }

    fn strip_comments(&self, source: &str) -> String {
        let mut result = String::with_capacity(source.len());
        let bytes = source.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'/' && i + 1 < bytes.len() {
                if bytes[i+1] == b'/' {
                    // Line comment: replace with spaces until newline to preserve line numbers
                    // BUT: keep the backslash if it's at the end of the line (continuation)
                    let start = i;
                    while i < bytes.len() && bytes[i] != b'\n' {
                        i += 1;
                    }
                    // Check if the line ends with a backslash (ignoring whitespace)
                    let mut j = i;
                    while j > start && bytes[j-1].is_ascii_whitespace() {
                        j -= 1;
                    }
                    if j > start && bytes[j-1] == b'\\' {
                        // Preserve the backslash by replacing everything else with spaces
                        for _ in start..j-1 { result.push(' '); }
                        result.push('\\');
                        for _ in j..i { result.push(' '); }
                    } else {
                        for _ in start..i { result.push(' '); }
                    }
                    continue;
                }
                if bytes[i+1] == b'*' {
                    // Block comment: replace with spaces, preserving newlines.
                    // A `\` immediately before a newline is a line-continuation;
                    // keep it so a multi-line `/* */` comment inside a `define
                    // body doesn't sever the macro's backslash-continuation
                    // (IEEE 1800-2017 §22.5.1 — the macro text continues across
                    // backslash-newline, and the comment is part of that text).
                    // Mirrors the `//` branch above.
                    result.push(' ');
                    result.push(' ');
                    i += 2;
                    while i + 1 < bytes.len() {
                        if bytes[i] == b'*' && bytes[i+1] == b'/' {
                            result.push(' ');
                            result.push(' ');
                            i += 2;
                            break;
                        }
                        if bytes[i] == b'\n' {
                            result.push('\n');
                        } else if bytes[i] == b'\\' && bytes[i+1] == b'\n' {
                            result.push('\\');
                        } else {
                            result.push(' ');
                        }
                        i += 1;
                    }
                    continue;
                }
            }
            if bytes[i] == b'"' {
                // String literal: skip until closing quote
                result.push('\"');
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' && i + 1 < bytes.len() {
                        result.push('\\');
                        result.push(bytes[i+1] as char);
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        result.push('\"');
                        i += 1;
                        break;
                    }
                    result.push(bytes[i] as char);
                    i += 1;
                }
                continue;
            }
            result.push(bytes[i] as char);
            i += 1;
        }
        result
    }

    /// Length of a conditional-compilation directive at the start of `s`
    /// (including the backtick), and whether it takes a macro-name argument.
    /// Requires a word boundary after the keyword so `\`endiff` / `\`elsewhere`
    /// do not match.
    fn conditional_directive_len(s: &str) -> Option<(usize, bool)> {
        for (kw, takes_name) in [
            ("`ifdef", true),
            ("`ifndef", true),
            ("`elsif", true),
            ("`endif", false),
            ("`else", false),
        ] {
            if let Some(rest) = s.strip_prefix(kw) {
                if rest.is_empty() || rest.starts_with(|c: char| c.is_whitespace()) {
                    return Some((kw.len(), takes_name));
                }
            }
        }
        None
    }

    /// IEEE 1800-2017 §22.6: `\`ifdef`/`\`ifndef`/`\`elsif`/`\`else`/`\`endif`
    /// may appear MID-LINE, not only at the start of a line. UVM 2020 writes
    /// `static \`ifndef UVM_ENABLE_DEPRECATED_API local \`endif bit m;`. The
    /// resolver below is line-based, so lift every inline conditional directive
    /// onto its own line first. String literals are respected; comments are
    /// already stripped. A `\`define` and its backslash-continued body are left
    /// untouched — an `\`ifdef` there belongs to the macro body and must survive
    /// to expansion time.
    fn split_inline_conditionals(source: &str) -> String {
        if !source.contains('`') {
            return source.to_string();
        }
        let mut out = String::with_capacity(source.len() + 64);
        let mut in_define_cont = false;
        for line in source.lines() {
            let trimmed = line.trim_start();
            if in_define_cont || trimmed.starts_with("`define") {
                in_define_cont = line.trim_end().ends_with('\\');
                out.push_str(line);
                out.push('\n');
                continue;
            }
            // A line STARTING with a conditional directive may still carry
            // trailing content (`\`endif initial ...`; `\`endif junk`) —
            // §22.6 makes the directive its own token, so the tail must be
            // split off and processed, not swallowed with the directive.
            let starts_cond =
                trimmed.starts_with('`') && Self::conditional_directive_len(trimmed).is_some();
            if (trimmed.starts_with('`') && !starts_cond) || !line.contains('`') {
                out.push_str(line);
                out.push('\n');
                continue;
            }
            let b = line.as_bytes();
            let mut i = 0usize;
            let mut seg = 0usize;
            let mut in_str = false;
            while i < b.len() {
                let c = b[i];
                if c == b'"' && (i == 0 || b[i - 1] != b'\\') {
                    in_str = !in_str;
                    i += 1;
                    continue;
                }
                if !in_str && c == b'`' {
                    if let Some((dir_len, takes_name)) =
                        Self::conditional_directive_len(&line[i..])
                    {
                        let mut j = i + dir_len;
                        if takes_name {
                            let rest = &line[j..];
                            j += rest.len() - rest.trim_start().len();
                            j += line[j..]
                                .chars()
                                .take_while(|ch| ch.is_alphanumeric() || *ch == '_' || *ch == '$')
                                .map(|ch| ch.len_utf8())
                                .sum::<usize>();
                        }
                        let before = &line[seg..i];
                        if !before.trim().is_empty() {
                            out.push_str(before);
                            out.push('\n');
                        }
                        out.push_str(line[i..j].trim());
                        out.push('\n');
                        seg = j;
                        i = j;
                        continue;
                    }
                }
                i += 1;
            }
            out.push_str(&line[seg..]);
            out.push('\n');
        }
        out
    }

    fn resolve_directives(&mut self, source: &str, source_path: Option<&Path>) -> String {
        let source = Self::split_inline_conditionals(source);
        let source = source.as_str();
        let mut output = String::with_capacity(source.len());
        let mut lines = source.lines().peekable();
        let mut ifdef_stack: Vec<IfdefState> = Vec::new();

        // Directory of the current source file (for relative `include resolution)
        let source_dir = source_path.and_then(|p| p.parent().map(|d| d.to_path_buf()));

        // Save the caller's `__FILE__` / `__LINE__` cursor (so nested
        // `include returns leave it untouched), then point it at this source.
        let saved_file = std::mem::take(&mut self.current_file);
        let saved_line = self.current_line;
        self.current_file = source_path
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_default();
        self.current_line = 0;

        while let Some(line) = lines.next() {
            self.current_line += 1;
            let trimmed = line.trim();

            // Strip (* ... *) attributes (IEEE 1800-2017 §5.12)
            if trimmed.starts_with("(*") && trimmed.ends_with("*)") {
                output.push('\n');
                continue;
            }

            if trimmed.starts_with("`define") {
                // Join backslash-continuation lines (IEEE 1800-2017 §22.5.1)
                let mut consumed_lines = 1;
                
                // For the directive, we want to strip the \ and the newline
                let mut clean_line = String::new();
                let mut current = line.to_string();
                
                loop {
                    let text = current.as_str();
                    // Handle trailing comment if any? No, trim_end handles it if it's after \.
                    // But if comment has \, it's tricky. Let's assume clean source after strip_comments.
                    if let Some(pos) = text.trim_end().rfind('\\') {
                        if text[pos+1..].chars().all(|c| c.is_ascii_whitespace()) {
                            clean_line.push_str(&text[..pos]);
                            if let Some(next) = lines.next() {
                                // Preserve the line break between continuation
                                // lines of a multi-line `define body. Without
                                // it, a body line like `\`ifndef X` is flattened
                                // mid-line and the post-expansion directive
                                // re-scan (which only recognises line-start
                                // directives) misses it — exactly how UVM's
                                // field macros leaked `\`ifndef … \`endif` into
                                // the parser.
                                clean_line.push('\n');
                                consumed_lines += 1;
                                current = next.to_string();
                                continue;
                            }
                            // The source ended while the body was still
                            // continued — a `\` on the very last line, with
                            // nothing left to splice onto it. The text before
                            // the backslash was already taken above, so the
                            // body ends here. Falling through instead appended
                            // the same text a SECOND time, backslash and all,
                            // so `\`define FOO(arg) \ / {1, arg} \` (EOF)
                            // expanded to `{1, arg} {1, arg} \`.
                            break;
                        }
                    }
                    clean_line.push_str(text);
                    break;
                }
                
                if ifdef_stack.iter().all(|s| s.active) {
                    self.parse_define(&clean_line);
                }
                // Don't output `define lines, but preserve line numbers
                for _ in 0..consumed_lines {
                    output.push('\n');
                }
                continue;
            }

            // IEEE 1800-2023 §22.5.2: `undefineall — clear every user-defined
            // macro. Predefined `SV_COV_*` system constants stay (re-seeded).
            // Check BEFORE `undef so the longer name wins token match.
            if trimmed.starts_with("`undefineall") {
                if ifdef_stack.iter().all(|s| s.active) {
                    self.defines.clear();
                    Self::seed_predefined(&mut self.defines);
                }
                output.push('\n');
                continue;
            }

            if trimmed.starts_with("`undef") {
                if ifdef_stack.iter().all(|s| s.active) {
                    let name = trimmed[6..].trim().to_string();
                    self.defines.remove(&name);
                }
                output.push('\n');
                continue;
            }

            if trimmed.starts_with("`ifdef") {
                let name = trimmed[6..].trim();
                // Strip trailing // comments from ifdef macro name
                let name = name.split_whitespace().next().unwrap_or(name);
                let parent_active = ifdef_stack.iter().all(|s| s.active);
                let active = parent_active && self.is_defined(name);
                ifdef_stack.push(IfdefState { parent_active, branch_taken: active, active });
                output.push('\n');
                continue;
            }

            if trimmed.starts_with("`ifndef") {
                let name = trimmed[7..].trim();
                let name = name.split_whitespace().next().unwrap_or(name);
                let parent_active = ifdef_stack.iter().all(|s| s.active);
                let active = parent_active && !self.is_defined(name);
                ifdef_stack.push(IfdefState { parent_active, branch_taken: active, active });
                output.push('\n');
                continue;
            }

            if trimmed.starts_with("`elsif") {
                let name = trimmed[6..].trim();
                let name = name.split_whitespace().next().unwrap_or(name);
                if let Some(last) = ifdef_stack.last_mut() {
                    if !last.parent_active || last.branch_taken {
                        last.active = false;
                    } else {
                        let active = self.is_defined(name);
                        last.active = active;
                        if active {
                            last.branch_taken = true;
                        }
                    }
                }
                output.push('\n');
                continue;
            }

            if trimmed.starts_with("`else") {
                if let Some(last) = ifdef_stack.last_mut() {
                    let active = last.parent_active && !last.branch_taken;
                    last.active = active;
                    last.branch_taken = true;
                }
                output.push('\n');
                continue;
            }

            if trimmed.starts_with("`endif") {
                ifdef_stack.pop();
                output.push('\n');
                continue;
            }

            // Skip inactive blocks
            if !ifdef_stack.iter().all(|s| s.active) {
                output.push('\n');
                continue;
            }

            // Track design-element nesting (for §22.3 `\`resetall` placement).
            // Heuristic, line-based: a leading module/interface/package/program/
            // primitive/checker keyword opens one; the matching `end…` closes it.
            if crate::strict_checks() && !trimmed.starts_with('`') {
                Self::update_design_depth(trimmed, &mut self.design_element_depth);
            }

            // Handle `include — read and recursively preprocess the included file
            if trimmed.starts_with("`include") {
                // §22.4: the filename may come from a text macro
                // (`include `DEFINED_PATH). Silently dropping the line left
                // the file un-included and everything downstream undefined.
                let parsed = Self::parse_include_path(trimmed).or_else(|| {
                    let expanded = self.expand_macros_once(trimmed);
                    Self::parse_include_path(expanded.trim())
                });
                if parsed.is_none() {
                    self.errors.push(format!(
                        "malformed `include directive: {}", trimmed
                    ));
                    eprintln!("[PP] error: malformed `include directive: {}", trimmed);
                }
                if let Some(inc_file) = parsed {
                    if self.include_depth < MAX_INCLUDE_DEPTH {
                        if let Some(resolved) = self.resolve_include(&inc_file, source_dir.as_deref()) {
                            // Lossy decode — tolerate stray non-UTF-8 bytes in
                            // included RTL (replace with U+FFFD, don't fail).
                            match std::fs::read(&resolved).map(|b| String::from_utf8_lossy(&b).into_owned()) {
                                Ok(contents) => {
                                    self.include_depth += 1;
                                    let stripped = self.strip_comments(&contents);
                                    let included = self.resolve_directives(&stripped, Some(&resolved));
                                    self.include_depth -= 1;
                                    output.push_str(&included);
                                    // Don't push extra newline — included content has its own
                                    continue;
                                }
                                Err(e) => {
                                    // FATAL: the design text that follows may
                                    // silently depend on declarations from this
                                    // file — every mainstream tool errors here.
                                    self.errors.push(format!(
                                        "cannot read `include file '{}': {}",
                                        resolved.display(), e
                                    ));
                                    eprintln!("[PP] error: cannot read `include file '{}': {}", resolved.display(), e);
                                }
                            }
                        } else {
                            // FATAL, not a warning: a failed `include used to
                            // continue preprocessing, and the missing
                            // declarations then degraded downstream — an
                            // undeclared port actual became a silent implicit
                            // net and a whole testbench checked garbage. The
                            // reference tooling hard-errors here; so do we.
                            self.errors.push(format!(
                                "cannot find `include file '{}' (searched the including file's directory and {} include dir(s))",
                                inc_file, self.include_dirs.len()
                            ));
                            eprintln!("[PP] error: cannot find `include file '{}'", inc_file);
                        }
                    } else {
                        self.errors.push(format!(
                            "`include depth limit ({}) exceeded for '{}' — recursive include?",
                            MAX_INCLUDE_DEPTH, inc_file
                        ));
                        eprintln!("[PP] error: `include depth limit ({}) exceeded for '{}'", MAX_INCLUDE_DEPTH, inc_file);
                    }
                }
                output.push('\n');
                continue;
            }

            // Record `default_nettype none` so the elaborator can
            // reject implicit-net auto-creation. We sticky-set the
            // flag on first appearance; the test for IEEE 1800-2017
            // §6.10 only needs to fail when implicit-net usage occurs
            // anywhere a `none` directive is in effect.
            // §22.9 `unconnected_drive pull0|pull1 ... `nounconnected_drive:
            // record the region; modules declared inside get their
            // unconnected INPUT ports pulled instead of Z.
            if trimmed.starts_with("`unconnected_drive") {
                let arg = trimmed["`unconnected_drive".len()..].trim();
                match arg.split_whitespace().next() {
                    Some("pull1") => self.unconnected_pull = Some(true),
                    Some("pull0") => self.unconnected_pull = Some(false),
                    other => {
                        if crate::strict_checks() {
                            self.push_error_here(format!(
                                "`unconnected_drive requires pull0 or pull1 (IEEE                                  1800-2017 §22.9), found `{}`",
                                other.unwrap_or("")
                            ));
                        }
                    }
                }
                output.push('\n');
                continue;
            }
            if trimmed.starts_with("`nounconnected_drive") {
                self.unconnected_pull = None;
                output.push('\n');
                continue;
            }
            if trimmed.starts_with("`default_nettype") {
                let rest = trimmed.trim_start_matches("`default_nettype").trim();
                if rest.starts_with("none") {
                    crate::set_default_nettype_none_seen(true);
                }
                output.push('\n');
                continue;
            }
            // IEEE 1800-2023 §22.14: `begin_keywords "<version>" pushes a
            // keyword-set onto the stack. We validate the version string
            // (warn on unknown) and track depth so a stray `end_keywords is
            // visible. Active-set switching for the lexer is future work; for
            // now this just enforces well-formedness and avoids silently
            // accepting typos in the version string.
            if trimmed.starts_with("`begin_keywords") {
                if ifdef_stack.iter().all(|s| s.active) {
                    let rest = trimmed.trim_start_matches("`begin_keywords").trim();
                    let ver = rest.trim_matches(|c: char| c == '"' || c.is_whitespace());
                    const VALID: &[&str] = &[
                        "1800-2023", "1800-2017", "1800-2012", "1800-2009", "1800-2005",
                        "1364-2005", "1364-2001", "1364-2001-noconfig", "1364-1995",
                    ];
                    if VALID.contains(&ver) {
                        self.keywords_stack.push(ver.to_string());
                    } else {
                        eprintln!(
                            "[PP] warning: `begin_keywords \"{}\" — unknown version string \
                             (IEEE 1800-2023 §22.14); accepted set is {}",
                            ver,
                            VALID.join(", ")
                        );
                        // Push anyway so end_keywords stays balanced.
                        self.keywords_stack.push(ver.to_string());
                    }
                    // Pass the directive through so the lexer can switch its
                    // active keyword set (downgrade SV-only keywords under a
                    // `1364-*` region). The version string is consumed by the
                    // scanner; the trailing `\n` keeps line numbers stable.
                    output.push_str(&format!("`begin_keywords \"{}\"", ver));
                }
                output.push('\n');
                continue;
            }
            if trimmed.starts_with("`end_keywords") {
                if ifdef_stack.iter().all(|s| s.active) {
                    if self.keywords_stack.pop().is_none() {
                        eprintln!(
                            "[PP] warning: `end_keywords without matching `begin_keywords \
                             (IEEE 1800-2023 §22.14)"
                        );
                    }
                    output.push_str("`end_keywords");
                }
                output.push('\n');
                continue;
            }

            // `timescale: parse it so the value is available downstream,
            // but emit no SV tokens (drop to a blank line). LRM §22.7.
            if let Some(rest) = trimmed.strip_prefix("`timescale") {
                let rest = rest.trim_start();
                if let Some(slash) = rest.find('/') {
                    let unit_str = rest[..slash].trim();
                    let prec_str = rest[slash + 1..].trim_end_matches("//").trim_end_matches("/*").trim();
                    let unit = Self::parse_time_literal(unit_str);
                    let prec = Self::parse_time_literal(prec_str);
                    if let (Some(u), Some(p)) = (unit, prec) {
                        // The global simulation tick is the finest precision
                        // declared anywhere in the design, so sub-nanosecond
                        // precision (down to fs) is honoured; delays scale to
                        // that tick. No truncation, no warning.
                        self.timescale = Some((u, p));
                        // A directive in THIS file: modules that follow it here
                        // have an own-file timescale (not merely inherited).
                        self.current_file_ts = true;
                    }
                }
                output.push('\n');
                continue;
            }

            // §22.12 `line <number> "<filename>" <level>` — strict-mode
            // validation (number positive int, filename a string literal,
            // level 0/1/2, all three present). Otherwise skipped.
            if Self::is_directive(trimmed, "line") {
                if crate::strict_checks() {
                    self.check_line_directive(trimmed);
                }
                // §22.12: APPLY the override — `__LINE__`/`__FILE__` after
                // this directive report the VIRTUAL position. (Previously
                // validated but ignored.) An out-of-range level is tolerated
                // with a warning, matching reference-tool behavior.
                let rest = trimmed["`line".len()..].trim();
                let num_tok = rest.split_whitespace().next().unwrap_or("");
                if let Ok(n) = num_tok.parse::<u32>() {
                    let after_num = rest[num_tok.len()..].trim_start();
                    if let Some(end) =
                        after_num.strip_prefix('"').and_then(|r| r.find('"'))
                    {
                        let fname = &after_num[1..1 + end];
                        let level = after_num[1 + end + 1..].trim();
                        if !matches!(level, "0" | "1" | "2") && !crate::strict_checks() {
                            eprintln!(
                                "[PP] warning: {}:{}: `line level `{}` is not 0/1/2                                  (IEEE 1800-2017 §22.12) — ignored",
                                self.current_file, self.current_line, level
                            );
                        }
                        self.current_file = fname.to_string();
                        // The NEXT source line must read as `n`; the loop
                        // increments before use.
                        self.current_line = n.saturating_sub(1);
                    }
                }
                output.push('\n');
                continue;
            }
            // §22.11 `pragma <pragma_name> ...` — the name is required.
            if Self::is_directive(trimmed, "pragma") {
                let args = trimmed["`pragma".len()..].trim();
                if crate::strict_checks() && args.is_empty() {
                    self.push_error_here(
                        "`pragma requires a pragma_name (IEEE 1800-2017 §22.11)".into());
                }
                // §34.2 protect pragmas: everything between
                // `pragma protect begin_protected` and the matching
                // `end_protected` (or the short `begin` / `end` pair) is
                // PROTECTED payload — typically encrypted, and in general not
                // valid SystemVerilog. It must never reach the lexer, where it
                // explodes into Unknown tokens and unbalances the surrounding
                // module. Skip to the matching end, emitting a newline per
                // skipped line so diagnostics keep their line numbers.
                if Self::protect_envelope_opens(args) {
                    output.push('\n');
                    for skipped in lines.by_ref() {
                        self.current_line += 1;
                        output.push('\n');
                        let st = skipped.trim();
                        if Self::is_directive(st, "pragma")
                            && Self::protect_envelope_closes(st["`pragma".len()..].trim())
                        {
                            break;
                        }
                    }
                    continue;
                }
                output.push('\n');
                continue;
            }
            // §22.3 `resetall` is illegal inside a design element (module,
            // interface, package, program, …).
            if Self::is_directive(trimmed, "resetall") {
                if crate::strict_checks() && self.design_element_depth > 0 {
                    self.push_error_here(
                        "`resetall is illegal inside a design element \
                         (IEEE 1800-2017 §22.3)".into());
                }
                // §22.3: `\`resetall` resets all compiler directives to their
                // defaults, including clearing the active `\`timescale`, so a
                // module declared after it has no explicit source-level timescale.
                self.timescale = None;
                output.push('\n');
                continue;
            }

            // Skip other compiler directives that don't affect simulation
            // semantics (kept silent — no warning).
            if trimmed.starts_with("`celldefine") || trimmed.starts_with("`endcelldefine")
                || trimmed.starts_with("`nounconnected_drive") || trimmed.starts_with("`unconnected_drive")
            {
                output.push('\n');
                continue;
            }

            let mut logical_line = line.to_string();
            let mut consumed_lines = 1;
            while logical_line.contains('`') && Self::has_unclosed_paren(&logical_line) {
                if let Some(next) = lines.next() {
                    logical_line.push('\n');
                    logical_line.push_str(next);
                    consumed_lines += 1;
                } else {
                    break;
                }
            }

            let expanded = self.expand_macros(&logical_line);
            // Promote any macro-expansion-time strict errors collected behind
            // `&self` into the main error list.
            if !self.expansion_errors.borrow().is_empty() {
                let drained: Vec<String> = self.expansion_errors.borrow_mut().drain(..).collect();
                self.errors.extend(drained);
            }
            let expanded = if Self::contains_preprocessor_directive(&expanded) {
                self.resolve_directives(&expanded, source_path)
            } else {
                expanded
            };
            if expanded.trim().is_empty() {
                for _ in 0..consumed_lines {
                    output.push('\n');
                }
            } else {
                // Capture the timescale in effect for any design element this
                // (expanded) line declares, so its scope's delays can later be
                // scaled by the right timeunit. `module foo`, `interface bar`,
                // `program baz`, `package p` — name is the first identifier after
                // the keyword. Standard one-declaration-per-line form (which
                // black-parrot uses); good enough for timescale association.
                if let Some(name) = Self::design_element_name(&expanded) {
                    if let Some(pull1) = self.unconnected_pull {
                        crate::record_unconnected_drive(&name, pull1);
                    }
                    // Only record a design element when a `\`timescale` directive
                    // is actually ACTIVE. An entry therefore means "has an
                    // explicit source-level timescale", which the
                    // `--module-timescale` extension keys off. A module with no
                    // active directive is absent from the map (and defaults to
                    // 1 ns / 1 ns downstream, unchanged).
                    if let Some(ts) = self.timescale {
                        if self.current_file_ts {
                            self.module_ts_own_file.insert(name.clone());
                        }
                        self.module_timescales.entry(name).or_insert(ts);
                    }
                }
                output.push_str(&expanded);
                output.push('\n');
            }
            // Account for additional physical lines consumed by paren-spanning
            // continuations so __LINE__ on subsequent lines stays correct.
            if consumed_lines > 1 {
                self.current_line += (consumed_lines - 1) as u32;
            }
        }

        // Restore caller's cursor (so a returning `include leaves the outer
        // file's __FILE__/__LINE__ intact).
        self.current_file = saved_file;
        self.current_line = saved_line;

        output
    }

    /// Extract the filename from an `include directive.
    /// Handles both `include "file.v" and `include <file.v> forms.
    fn parse_include_path(line: &str) -> Option<String> {
        let rest = line.strip_prefix("`include")?.trim();
        if rest.starts_with('"') {
            // `include "filename"
            let end = rest[1..].find('"')?;
            Some(rest[1..1 + end].to_string())
        } else if rest.starts_with('<') {
            // `include <filename>
            let end = rest[1..].find('>')?;
            Some(rest[1..1 + end].to_string())
        } else {
            None
        }
    }

    /// Resolve an `include filename to an absolute path by searching:
    /// 1. The directory of the currently-processed source file
    /// 2. Each directory in include_dirs (in order)
    fn resolve_include(&self, filename: &str, source_dir: Option<&Path>) -> Option<PathBuf> {
        let inc_path = Path::new(filename);

        // If the include path is absolute, use it directly
        if inc_path.is_absolute() {
            if inc_path.exists() {
                return Some(inc_path.to_path_buf());
            }
            return None;
        }

        // Search relative to the current source file's directory first
        if let Some(dir) = source_dir {
            let candidate = dir.join(inc_path);
            if candidate.exists() {
                return Some(candidate);
            }
        }

        // Search include directories
        for dir in &self.include_dirs {
            let candidate = dir.join(inc_path);
            if candidate.exists() {
                return Some(candidate);
            }
        }

        // Fallback: try relative to current working directory
        if let Ok(cwd) = std::env::current_dir() {
            let candidate = cwd.join(inc_path);
            if candidate.exists() {
                return Some(candidate);
            }
        }

        None
    }

    fn parse_define(&mut self, line: &str) {
        let trimmed = line.trim();
        if !trimmed.starts_with("`define") { return; }
        let rest = trimmed[7..].trim(); // after `define
        // Find name
        let name_end = rest.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(rest.len());
        let name = rest[..name_end].to_string();
        let after_name = rest[name_end..].trim_start();
        
        // Check for parameterized macro: `define NAME(param1, param2) body
        // Note: LRM says NO space between NAME and '('
        let (params, body) = if rest[name_end..].starts_with('(') {
            // Find closing paren (handling nested parens)
            let mut depth = 0;
            let mut close_pos = None;
            for (idx, c) in rest[name_end..].char_indices() {
                if c == '(' { depth += 1; }
                else if c == ')' {
                    depth -= 1;
                    if depth == 0 {
                        close_pos = Some(name_end + idx);
                        break;
                    }
                }
            }
            
            if let Some(close) = close_pos {
                let param_str = &rest[name_end + 1..close];
                let params: Vec<(String, Option<String>)> = Self::split_top_level_commas(param_str)
                    .into_iter()
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty())
                    .map(|s| match s.find('=') {
                        Some(eq) => (
                            s[..eq].trim().to_string(),
                            Some(s[eq + 1..].trim().to_string()),
                        ),
                        None => (s, None),
                    })
                    .collect();
                let body = rest[close + 1..].to_string();
                (Some(params), body)
            } else {
                (None, rest[name_end..].to_string())
            }
        } else {
            (None, after_name.to_string())
        };
        
        if !name.is_empty() {
            if crate::strict_checks() {
                // §22.5.1: a compiler-directive name is a predefined macro and
                // shall not be redefined as a user macro.
                const DIRECTIVES: &[&str] = &[
                    "define", "undef", "undefineall", "ifdef", "ifndef", "elsif",
                    "else", "endif", "include", "line", "pragma", "resetall",
                    "timescale", "begin_keywords", "end_keywords",
                    "default_nettype", "celldefine", "endcelldefine",
                    "unconnected_drive", "nounconnected_drive",
                    "__FILE__", "__LINE__",
                ];
                if DIRECTIVES.contains(&name.as_str()) {
                    self.push_error_here(format!(
                        "`{}` is a compiler directive and cannot be redefined as \
                         a macro (IEEE 1800-2017 §22.5.1)", name));
                }
                // §22.5.1: the macro text shall not contain an unterminated
                // string literal (a `"` opened in the body and never closed).
                let (mut quotes, mut esc) = (0u32, false);
                for c in body.chars() {
                    if esc { esc = false; continue; }
                    match c { '\\' => esc = true, '"' => quotes += 1, _ => {} }
                }
                if quotes % 2 == 1 {
                    self.push_error_here(format!(
                        "macro `{}` text has an unterminated string literal \
                         (IEEE 1800-2017 §22.5.1)", name));
                }
            }
            // eprintln!("[PP] defining macro '{}'", name);
            self.defines.insert(name.clone(), MacroDef {
                name,
                params,
                body,
            });
        }
    }

    fn expand_macros(&self, source: &str) -> String {
        let mut result = self.expand_macros_once(source);
        // Recursively expand up to 128 times to handle deeply nested macros.
        // C906's aq_idu_cfig.h chains 25+ DIS_VEC_* defines (DIS_VEC_WIDTH →
        // DIS_VEC_FUNC → DIS_VEC_EU → … → DIS_VEC_SRC1_DATA), each requiring
        // one expansion iteration. The earlier 16-step cap silently truncated
        // expansion mid-chain, leaving residual `IDENT directives that the
        // tokenizer then reported as parse errors. We stop early on
        // fixed-point so the cap only matters for pathological cases.
        for _ in 0..128 {
            if !result.contains('`') { break; }
            let next = self.expand_macros_once(&result);
            if next == result { break; }
            result = next;
        }
        result
    }

fn apply_token_pasting(text: &str) -> String {
    if !text.contains("``") {
        return text.to_string();
    }
    let mut result = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    let mut in_string = false;
    while i < bytes.len() {
        if in_string {
            let ch = text[i..].chars().next().unwrap();
            if ch == '\\' {
                result.push(ch);
                i += ch.len_utf8();
                if i < bytes.len() {
                    let n = text[i..].chars().next().unwrap();
                    result.push(n);
                    i += n.len_utf8();
                }
                continue;
            }
            if ch == '"' {
                in_string = false;
            }
            result.push(ch);
            i += ch.len_utf8();
            continue;
        }

        if bytes[i] == b'`' && i + 1 < bytes.len() && bytes[i + 1] == b'`' {
            // §22.5.1: `` DELIMITS lexical tokens "without introducing white
            // space" — it is deleted, nothing more. It must NOT eat existing
            // whitespace around it: `localparam `` i``a``b``j` keeps the gap
            // after `localparam` (br979), while `i``a` glues because there
            // was no whitespace between the tokens to begin with.
            i += 2;
            continue;
        }

        if bytes[i] == b'"' && !(i > 0 && bytes[i - 1] == b'`') {
            in_string = true;
        }

        let ch = text[i..].chars().next().unwrap();
        result.push(ch);
        i += ch.len_utf8();
    }
    result
}

    fn expand_macros_once(&self, line: &str) -> String {
        let line_pasted = Self::apply_token_pasting(line);
        let line = &line_pasted;
        let mut result = String::with_capacity(line.len());
        let bytes = line.as_bytes();
        let mut i = 0;
        // IEEE 1800.1-2023 §22.5.1: macro expansion does not occur inside
        // string literals. Track "..." state (honoring `\"` escapes) so a
        // backtick-prefixed macro name that appears in a message string — e.g.
        // $display("see `uvm_object_utils here") — is left as literal text
        // instead of being mis-expanded. Without this a *defined* parameterized
        // macro name followed by non-'(' text inside a string was falsely
        // rejected as "requires parentheses", breaking any testbench whose
        // $display/$info strings mention a macro by name. A bare '"' reaching
        // the non-backtick path always opens a regular string: stringify
        // delimiters (`` `" ``) are backtick-prefixed and consumed by the
        // backtick handler below, so they never reach this path.
        let mut in_string = false;
        while i < bytes.len() {
            if in_string {
                let ch = line[i..].chars().next().unwrap();
                if ch == '\\' {
                    // Escaped char: copy verbatim, stay in the string.
                    result.push(ch);
                    i += ch.len_utf8();
                    if i < bytes.len() {
                        let n = line[i..].chars().next().unwrap();
                        result.push(n);
                        i += n.len_utf8();
                    }
                    continue;
                }
                if ch == '"' {
                    in_string = false;
                }
                result.push(ch);
                i += ch.len_utf8();
                continue;
            }
            if bytes[i] == b'`' {
                if i + 1 < bytes.len() && bytes[i+1] == b'`' {
                    // Concatenation: skip both backticks
                    i += 2;
                    continue;
                }
                if i + 1 < bytes.len() && bytes[i+1] == b'\"' {
                    // Stringification: replace with normal quote
                    result.push('\"');
                    i += 2;
                    continue;
                }
                if i + 3 < bytes.len()
                    && bytes[i + 1] == b'\\'
                    && bytes[i + 2] == b'`'
                    && bytes[i + 3] == b'\"'
                {
                    // §22.5.1 `\`" — an ESCAPED quote inside the expanded
                    // string literal. Previously fell into the macro-name
                    // scan and came out mangled.
                    result.push('\\');
                    result.push('\"');
                    i += 4;
                    continue;
                }
                
                i += 1;
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let macro_name = &line[start..i];
                if macro_name == "__FILE__" {
                    // IEEE 1800-2023 §22.13: expands to the current source
                    // file's path as a double-quoted string. We re-quote any
                    // backslashes/quotes in the path so the resulting token
                    // is a valid SV string literal.
                    result.push('\"');
                    for ch in self.current_file.chars() {
                        match ch {
                            '\\' => { result.push('\\'); result.push('\\'); }
                            '\"' => { result.push('\\'); result.push('\"'); }
                            _ => result.push(ch),
                        }
                    }
                    result.push('\"');
                } else if macro_name == "__LINE__" {
                    // IEEE 1800-2023 §22.13.
                    result.push_str(&self.current_line.to_string());
                } else if let Some(def) = self.defines.get(macro_name) {
                    // eprintln!("[PP] expanding macro '{}'", macro_name);
                    let mut p = i;
                    while p < bytes.len() && (bytes[p] == b' ' || bytes[p] == b'\t') {
                        p += 1;
                    }
                    if def.params.is_some() && p < bytes.len() && bytes[p] == b'(' {
                        i = p;
                        // Parameterized macro: find arguments
                        let args = Self::extract_macro_args(line, &mut i);
                        let params = def.params.as_ref().unwrap();
                        // §22.5.1 strict argument-count validation: too many
                        // actuals, or a non-defaulted formal left without one.
                        if crate::strict_checks() {
                            if args.len() > params.len() {
                                self.expansion_errors.borrow_mut().push(format!(
                                    "macro `{}` invoked with {} arguments but only \
                                     {} are declared (IEEE 1800-2017 §22.5.1)",
                                    macro_name, args.len(), params.len()));
                            } else {
                                // §22.5.1: an actual at a position (even empty,
                                // via a trailing/leading comma) is legal — only a
                                // formal *beyond* the supplied positions with no
                                // default is "fewer actual arguments than formals".
                                for (pi, (pname, default)) in params.iter().enumerate() {
                                    if pi >= args.len() && default.is_none() {
                                        self.expansion_errors.borrow_mut().push(format!(
                                            "macro `{}` missing required argument `{}` \
                                             (IEEE 1800-2017 §22.5.1)", macro_name, pname));
                                    }
                                }
                            }
                        }
                        let mut body = def.body.clone();
                        for (pi, (pname, default)) in params.iter().enumerate() {
                            // An actual arg that is missing or blank falls back
                            // to the formal's default (SV LRM 22.5.1). e.g.
                            // `DV_CHECK(expr)` leaves the optional trailing
                            // `WITH_C_=` constraint empty.
                            let arg_owned: String;
                            let arg: Option<&String> = match args.get(pi) {
                                Some(a) if !a.trim().is_empty() => Some(a),
                                _ => match default {
                                    Some(d) => { arg_owned = d.clone(); Some(&arg_owned) }
                                    None => None,
                                },
                            };
                            {
                            if let Some(arg) = arg {
                                // Replace only whole words, and only outside
                                // string literals (so a parameter name that
                                // also appears in a format string in the
                                // body — e.g. `actual` in
                                // `"actual=%0d"` — isn't substituted away,
                                // which would corrupt the string when the
                                // arg itself contains a `"`).
                                let mut new_body = String::with_capacity(body.len());
                                let mut last = 0;
                                let body_bytes = body.as_bytes();
                                let mut string_ranges: Vec<(usize, usize)> = Vec::new();
                                {
                                    let mut i = 0;
                                    while i < body_bytes.len() {
                                        // A `"` preceded by a backtick is the
                                        // preprocessor stringify-quote delimiter
                                        // (`\`"..."\``), NOT a regular string
                                        // literal. Per IEEE 1800-2017 §22.5.1,
                                        // macro formals inside `\`"..."\`` MUST be
                                        // substituted (then stringized), so do not
                                        // open an opaque string range here — else
                                        // `uvm_type_name_decl(\`"T\`")` leaves `T`
                                        // unsubstituted and get_type_name returns
                                        // the literal "T" instead of the class name.
                                        if body_bytes[i] == b'"'
                                            && !(i > 0 && body_bytes[i - 1] == b'`')
                                        {
                                            let start = i;
                                            i += 1;
                                            while i < body_bytes.len() {
                                                if body_bytes[i] == b'\\' && i + 1 < body_bytes.len() { i += 2; continue; }
                                                if body_bytes[i] == b'"' { i += 1; break; }
                                                i += 1;
                                            }
                                            // A `` inside these quotes does NOT
                                            // reopen the region to substitution:
                                            // §22.5.1 says argument substitution
                                            // shall not occur within a string
                                            // literal, and `\`"` is the construct
                                            // for building a string from an
                                            // argument. `"``x``"` therefore stays
                                            // literal (GitHub #62 asked for it to
                                            // expand; a reference simulator
                                            // leaves it alone too, so expanding
                                            // would be a divergence).
                                            string_ranges.push((start, i));
                                        } else {
                                            i += 1;
                                        }
                                    }
                                }
                                let in_string = |pos: usize| -> bool {
                                    string_ranges.iter().any(|(lo, hi)| pos >= *lo && pos < *hi)
                                };
                                for (start, part) in body.match_indices(pname) {
                                    let before = body_bytes.get(start.wrapping_sub(1)).copied().unwrap_or(0);
                                    let after = body_bytes.get(start + part.len()).copied().unwrap_or(0);
                                    new_body.push_str(&body[last..start]);
                                    if !(before.is_ascii_alphanumeric() || before == b'_')
                                        && !(after.is_ascii_alphanumeric() || after == b'_')
                                        && !in_string(start)
                                    {
                                        new_body.push_str(arg);
                                    } else {
                                        new_body.push_str(part);
                                    }
                                    last = start + part.len();
                                }
                                new_body.push_str(&body[last..]);
                                body = new_body;
                            }
                            }
                        }
                        let body_pasted = Self::apply_token_pasting(&body);
                        result.push_str(&body_pasted);
                    } else {
                        // §22.5.1: a macro defined with a formal list must be
                        // invoked with parentheses, even when empty.
                        if crate::strict_checks() && def.params.is_some() {
                            self.expansion_errors.borrow_mut().push(format!(
                                "macro `{}` requires parentheses (it is defined with \
                                 arguments) (IEEE 1800-2017 §22.5.1)", macro_name));
                        }
                        let body_pasted = Self::apply_token_pasting(&def.body);
                        result.push_str(&body_pasted);
                    }
                } else {
                    // §22.5.1: referencing an undefined text macro is an error.
                    // We still pass the text through — an unrecognised compiler
                    // directive or tool pragma has to survive to the lexer — but
                    // the user gets told WHICH name was undefined and where.
                    // Without this, `\`uvm_do_with(req, {req.wr_en==1;})` (a
                    // macro that only exists under UVM_ENABLE_DEPRECATED_API)
                    // reached the parser as literal text and produced ten
                    // "expected RParen, found Comma" errors that named neither
                    // the macro nor the reason.
                    self.note_undefined_macro(macro_name);
                    result.push('`');
                    result.push_str(macro_name);
                }
            } else {
                let ch = line[i..].chars().next().unwrap();
                if ch == '"' {
                    in_string = true;
                }
                result.push(ch);
                i += ch.len_utf8();
            }
        }
        result
    }
}

impl Default for Preprocessor {
    fn default() -> Self {
        Self::new()
    }
}

impl Preprocessor {
    /// Strip (* ... *) Verilog attributes from a line
    /// Extract parenthesized macro arguments, handling nested parens.
    /// `i` should point at the opening '('. After return, `i` is past the closing ')'.
    /// Split a macro formal-parameter list on commas that are not nested inside
    /// parens/brackets/braces or string literals, so a default value like
    /// `ID_=`gfn` (or one containing brackets) stays intact.
    fn split_top_level_commas(s: &str) -> Vec<String> {
        let bytes = s.as_bytes();
        let mut parts = Vec::new();
        let (mut paren, mut brace, mut bracket) = (0i32, 0i32, 0i32);
        let mut in_string = false;
        let mut start = 0;
        let mut i = 0;
        while i < bytes.len() {
            let c = bytes[i];
            if in_string {
                if c == b'\\' { i += 2; continue; }
                if c == b'"' { in_string = false; }
            } else {
                match c {
                    b'"' => in_string = true,
                    b'(' => paren += 1,
                    b')' => paren -= 1,
                    b'{' => brace += 1,
                    b'}' => brace -= 1,
                    b'[' => bracket += 1,
                    b']' => bracket -= 1,
                    b',' if paren == 0 && brace == 0 && bracket == 0 => {
                        parts.push(s[start..i].to_string());
                        start = i + 1;
                    }
                    _ => {}
                }
            }
            i += 1;
        }
        parts.push(s[start..].to_string());
        parts
    }

    fn extract_macro_args(line: &str, i: &mut usize) -> Vec<String> {
        let bytes = line.as_bytes();
        *i += 1; // skip '('
        let mut args = Vec::new();
        let mut paren_depth = 1;
        let mut brace_depth = 0;
        let mut bracket_depth = 0;
        let mut in_string = false;
        let mut arg_start = *i;
        while *i < bytes.len() && paren_depth > 0 {
            match bytes[*i] {
                b'"' if *i == 0 || bytes[*i - 1] != b'\\' => {
                    in_string = !in_string;
                }
                b'(' if !in_string => paren_depth += 1,
                b')' if !in_string => {
                    paren_depth -= 1;
                    if paren_depth == 0 {
                        let arg = line[arg_start..*i].trim().to_string();
                        if !arg.is_empty() || !args.is_empty() {
                            args.push(arg);
                        }
                        *i += 1; // skip ')'
                        return args;
                    }
                }
                b'{' if !in_string => brace_depth += 1,
                b'}' if !in_string => if brace_depth > 0 { brace_depth -= 1; },
                b'[' if !in_string => bracket_depth += 1,
                b']' if !in_string => if bracket_depth > 0 { bracket_depth -= 1; },
                b',' if !in_string && paren_depth == 1 && brace_depth == 0 && bracket_depth == 0 => {
                    args.push(line[arg_start..*i].trim().to_string());
                    arg_start = *i + 1;
                }
                _ => {}
            }
            *i += 1;
        }
        args
    }

    fn strip_attributes(line: &str) -> String {
        let mut result = String::with_capacity(line.len());
        let bytes = line.as_bytes();
        let mut i = 0;
        let mut in_string = false;
        while i < bytes.len() {
            if bytes[i] == b'\"' && (i == 0 || bytes[i - 1] != b'\\') {
                in_string = !in_string;
            }
            if !in_string && i + 1 < bytes.len() && bytes[i] == b'(' && bytes[i + 1] == b'*'
                // `@(*)` is the implicit-sensitivity-list construct, not an
                // attribute. Skip if the byte after `(*` is `)`. Likewise
                // skip `(**` (e.g. an exponent inside parens) where the
                // payload starts with another `*`.
                && bytes.get(i + 2).copied() != Some(b')')
                && bytes.get(i + 2).copied() != Some(b'*')
            {
                // Find matching *)
                let mut j = i + 2;
                let mut found = false;
                while j + 1 < bytes.len() {
                    if bytes[j] == b'*' && bytes[j + 1] == b')' {
                        j += 2;
                        found = true;
                        break;
                    }
                    j += 1;
                }
                if found {
                    // Replace attribute with space to preserve spacing
                    result.push(' ');
                    i = j;
                    continue;
                }
            }
            let ch = line[i..].chars().next().unwrap();
            result.push(ch);
            i += ch.len_utf8();
        }
        result
    }

    fn has_unclosed_paren(line: &str) -> bool {
        let mut depth = 0i32;
        let mut in_string = false;
        let bytes = line.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'"' if i == 0 || bytes[i - 1] != b'\\' => {
                    in_string = !in_string;
                }
                b'(' if !in_string => depth += 1,
                b')' if !in_string => depth -= 1,
                _ => {}
            }
            i += 1;
        }
        depth > 0
    }

    fn contains_preprocessor_directive(text: &str) -> bool {
        text.lines().any(|line| {
            matches!(
                line.trim_start(),
                trimmed if trimmed.starts_with("`ifdef")
                    || trimmed.starts_with("`ifndef")
                    || trimmed.starts_with("`elsif")
                    || trimmed.starts_with("`else")
                    || trimmed.starts_with("`endif")
                    || trimmed.starts_with("`include")
                    || trimmed.starts_with("`undef")
                    || trimmed.starts_with("`define")
            )
        })
    }
}
