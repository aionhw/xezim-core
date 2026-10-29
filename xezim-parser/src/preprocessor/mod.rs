//! SystemVerilog preprocessor (IEEE 1800-2017 §22)
//!
//! Handles `define, `ifdef/`ifndef/`else/`endif, `include, `undef, etc.
//! This is a simplified preprocessor suitable for parsing purposes.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::diagnostics::{self, Location};
use crate::source_map::{LineMap, LineOrigin, MacroColumn, MapFile};

#[derive(Debug, Clone)]
pub struct MacroDef {
    pub name: String,
    /// Formal parameters as (name, default) pairs. `default` is `Some` when the
    /// macro declares a default value (`P=`, `P=expr`); an empty default is
    /// `Some("")`. Actual args that are missing or blank fall back to it.
    pub params: Option<Vec<(String, Option<String>)>>,
    pub body: String,
}

/// Ends a macro usage at a `` paste and is removed once usages expand
/// (`apply_token_pasting`). A character source text rarely holds.
const PASTE_SEPARATOR: char = '\u{1}';

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
    /// `(macro name, message)`, located at the invocation when drained.
    expansion_errors: std::cell::RefCell<Vec<(String, String)>>,
    /// Undefined macro names seen while expanding the current line; reported
    /// (located at the use) when the line is done.
    undefined_seen: std::cell::RefCell<Vec<String>>,
    /// Whether `apply_token_pasting` left a `PASTE_SEPARATOR` that
    /// `expand_macros` must remove; a 0x01 byte of the source is kept.
    paste_separated: std::cell::Cell<bool>,
    /// Files contributing to the text being produced, for its line map.
    map_files: Vec<MapFile>,
    /// Macro names referenced by the line map, and their indices.
    map_macros: Vec<String>,
    map_columns: Vec<Vec<MacroColumn>>,
    map_macro_idx: HashMap<String, u32>,
    /// `map_files` index of `current_file`.
    cur_file_idx: u32,
    /// The source line being processed and its column in the original line
    /// (non-zero for a piece split off it), for diagnostic carets.
    cur_line_text: String,
    cur_col_off: u32,
    /// Line map of the text the last `preprocess_file`/`preprocess` returned.
    last_map: Option<LineMap>,
}

const MAX_INCLUDE_DEPTH: usize = 32;

#[derive(Clone, Copy)]
struct IfdefState {
    parent_active: bool,
    branch_taken: bool,
    active: bool,
}

/// What `resolve_directives` is resolving.
#[derive(Clone, Copy)]
enum Ctx {
    /// A source file (`source_path`), pulled in by the `include at
    /// `(map file, line)` when there is one.
    File { included_from: Option<(u32, u32)> },
    /// Macro-expanded text that still held directives; all of it maps to
    /// the invocation.
    Macro(LineOrigin),
}

/// Collects one origin per output line, in step with the output text.
#[derive(Default)]
struct OriginSink {
    origins: Vec<LineOrigin>,
    /// Bytes of the output already accounted for.
    seen: usize,
}

impl OriginSink {
    /// Give every line completed since the last call the origin `o`.
    fn fill(&mut self, output: &str, o: LineOrigin) {
        let n = output.as_bytes()[self.seen..]
            .iter()
            .filter(|&&b| b == b'\n')
            .count();
        self.origins.extend(std::iter::repeat_n(o, n));
        self.seen = output.len();
    }

    /// Append the origins of text just appended to `output` (which must be
    /// in sync before that text).
    fn extend(&mut self, output: &str, origins: Vec<LineOrigin>) {
        self.origins.extend(origins);
        self.seen = output.len();
    }
}

/// The first position of `needle` in `hay`.
fn find_byte_seq(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

/// Offset of the first byte of `b` equal to one of `targets`, eight bytes at
/// a time; `None` when there is none. The same answer as
/// `b.iter().position(..)` with that predicate.
fn find_byte(b: &[u8], targets: &[u8]) -> Option<usize> {
    const LO: u64 = 0x0101_0101_0101_0101;
    const HI: u64 = 0x8080_8080_8080_8080;
    let mut i = 0;
    while i + 8 <= b.len() {
        let x = u64::from_le_bytes(b[i..i + 8].try_into().unwrap());
        let mut m = 0;
        for &t in targets {
            let v = x ^ (LO * t as u64);
            // Exact for the lowest matching byte: borrows only reach bytes
            // above a true match.
            m |= v.wrapping_sub(LO) & !v & HI;
        }
        if m != 0 {
            return Some(i + (m.trailing_zeros() / 8) as usize);
        }
        i += 8;
    }
    b[i..]
        .iter()
        .position(|&c| targets.contains(&c))
        .map(|p| i + p)
}

/// Whitespace bytes `char::is_whitespace` accepts in ASCII (note VT, which
/// `u8::is_ascii_whitespace` does not).
fn ascii_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\x0B' | b'\x0C' | b'\r')
}

/// `str::trim_start`, skipping ASCII whitespace a byte at a time (lines of
/// blanked comments are long runs of spaces) and deferring to the Unicode
/// definition only when a non-ASCII byte follows.
fn fast_trim_start(s: &str) -> &str {
    let b = s.as_bytes();
    // Eight spaces at a time first: a blanked comment is one long run.
    let mut start = 0;
    while start + 8 <= b.len() && b[start..start + 8] == [b' '; 8] {
        start += 8;
    }
    start += b[start..]
        .iter()
        .position(|&c| !ascii_ws(c))
        .unwrap_or(b.len() - start);
    if start < b.len() && b[start] >= 0x80 {
        return s.trim_start();
    }
    &s[start..]
}

/// `str::trim` with the same ASCII fast path as `fast_trim_start`.
fn fast_trim(s: &str) -> &str {
    let t = fast_trim_start(s);
    let b = t.as_bytes();
    let mut end = b.len();
    while end >= 8 && b[end - 8..end] == [b' '; 8] {
        end -= 8;
    }
    let end = b[..end]
        .iter()
        .rposition(|&c| !ascii_ws(c))
        .map_or(0, |p| p + 1);
    if end > 0 && b[end - 1] >= 0x80 {
        return t.trim_end();
    }
    &t[..end]
}

/// Append `n` spaces.
fn push_spaces(out: &mut String, mut n: usize) {
    const SPACES: &str = "                                                                ";
    while n > 0 {
        let k = n.min(SPACES.len());
        out.push_str(&SPACES[..k]);
        n -= k;
    }
}

/// §22.5.1: a compiler directive matches as a WHOLE word — a user macro is
/// allowed to merely START with a directive keyword (`include_default_...`,
/// `undefined_x`, `ifdef_guard_y`). Prefix matching swallowed such macro
/// invocations as (malformed) directives, failing preprocessing outright.
fn directive_word(line: &str, kw: &str) -> bool {
    line.starts_with(kw)
        && line[kw.len()..]
            .chars()
            .next()
            .is_none_or(|c| !c.is_alphanumeric() && c != '_' && c != '$')
}

pub(crate) const COMPILER_DIRECTIVES: &[&str] = &[
    "define",
    "undef",
    "undefineall",
    "ifdef",
    "ifndef",
    "elsif",
    "else",
    "endif",
    "include",
    "line",
    "pragma",
    "resetall",
    "timescale",
    "begin_keywords",
    "end_keywords",
    "default_nettype",
    "celldefine",
    "endcelldefine",
    "unconnected_drive",
    "nounconnected_drive",
    "protect",
    "endprotect",
    "protected",
    "endprotected",
    "uselib",
    "default_decay_time",
    "default_trireg_strength",
    "delay_mode_distributed",
    "delay_mode_path",
    "delay_mode_unit",
    "delay_mode_zero",
    "accelerate",
    "noaccelerate",
    "autoexpand_vectornets",
    "expand_vectornets",
    "noexpand_vectornets",
    "remove_gatenames",
    "noremove_gatenames",
    "remove_netnames",
    "noremove_netnames",
    "suppress_faults",
    "nosuppress_faults",
    "enable_portfaults",
    "disable_portfaults",
    "signed",
    "unsigned",
];

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
            defines.insert(
                name.to_string(),
                MacroDef {
                    name: name.to_string(),
                    params: None,
                    body: val.to_string(),
                },
            );
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
            undefined_seen: std::cell::RefCell::new(Vec::new()),
            paste_separated: std::cell::Cell::new(false),
            map_files: Vec::new(),
            map_macros: Vec::new(),
            map_columns: Vec::new(),
            map_macro_idx: HashMap::new(),
            cur_file_idx: 0,
            cur_line_text: String::new(),
            cur_col_off: 0,
            last_map: None,
        }
    }

    /// Report a `\`name` that no `\`define` (and no compiler directive) covers,
    /// once per name, naming the file, line and column of the first use.
    ///
    /// Standard compiler directives reach this path too when they appear in a
    /// position `resolve_directives` does not handle, and an unrecognised
    /// tool-specific pragma is legitimate input, so this warns rather than
    /// failing the build. It is written straight to stderr because the
    /// preprocessor's own error list only surfaces on the `--preprocess` path,
    /// and this is most useful precisely when compiling.
    fn note_undefined_macro(&self, name: &str) {
        if name.is_empty() || COMPILER_DIRECTIVES.contains(&name) {
            return;
        }
        self.undefined_seen.borrow_mut().push(name.to_string());
    }

    /// Report the undefined macros seen while expanding the current line,
    /// each once per run (the driver preprocesses a design more than once).
    fn flush_undefined_macros(&self) {
        static REPORTED: std::sync::Mutex<Option<HashSet<String>>> = std::sync::Mutex::new(None);
        let names: Vec<String> = self.undefined_seen.borrow_mut().drain(..).collect();
        for name in names {
            let fresh = REPORTED
                .lock()
                .map(|mut g| g.get_or_insert_with(HashSet::new).insert(name.clone()))
                .unwrap_or(true);
            if !fresh {
                continue;
            }
            let tick = format!("`{}", name);
            let loc = self.here_at(&tick);
            eprintln!(
                "{}",
                diagnostics::render(
                    "warning",
                    &format!(
                        "macro `{} is undefined (IEEE 1800-2017 §22.5.1) — it is left as \
                         literal text, which usually causes a syntax error at the point of use",
                        name
                    ),
                    &loc,
                )
            );
        }
    }

    /// Strict-mode directive errors collected during preprocessing (empty
    /// unless `strict_checks()` is on and an illegal directive was seen), and
    /// fatal `include failures. Each entry is a fully rendered diagnostic
    /// (`file:line:col: error: ...` plus the source line).
    pub fn errors(&self) -> &[String] {
        &self.errors
    }

    /// The location of the line being processed: its first non-blank
    /// character, underlining the first word (the directive).
    fn here(&self) -> Location {
        let text = self.cur_line_text.lines().next().unwrap_or("");
        let lead = text.chars().take_while(|c| c.is_whitespace()).count() as u32;
        let word = text
            .trim_start()
            .chars()
            .take_while(|c| !c.is_whitespace())
            .count() as u32;
        self.location(0, lead, word.max(1))
    }

    /// The location of the first occurrence of `needle` in the (logical)
    /// line being processed; the line start when it does not occur there.
    fn here_at(&self, needle: &str) -> Location {
        let text = self.cur_line_text.as_str();
        let Some(p) = text.find(needle) else {
            return self.here();
        };
        let before = &text[..p];
        let (delta, line_start) = match before.rfind('\n') {
            Some(nl) => (before.matches('\n').count() as u32, nl + 1),
            None => (0, 0),
        };
        let mut loc = self.location(
            delta,
            text[line_start..p].chars().count() as u32,
            needle.chars().count() as u32,
        );
        if delta > 0 {
            // A later physical line of a joined invocation: no split offset.
            loc.col -= self.cur_col_off;
            loc.fallback_text = text[line_start..].lines().next().map(str::to_string);
        }
        loc
    }

    /// `current_file`, `line_delta` lines below `current_line`, at 0-based
    /// column `col` of the line being processed.
    fn location(&self, line_delta: u32, col: u32, len: u32) -> Location {
        let file = if self.current_file.is_empty() {
            "<input>".to_string()
        } else {
            self.current_file.clone()
        };
        let mut included_from = Vec::new();
        let mut f = self.cur_file_idx;
        while let Some((parent, line)) =
            self.map_files.get(f as usize).and_then(|m| m.included_from)
        {
            let Some(p) = self.map_files.get(parent as usize) else {
                break;
            };
            included_from.push((p.path.clone(), line));
            if included_from.len() > MAX_INCLUDE_DEPTH {
                break;
            }
            f = parent;
        }
        Location {
            file,
            line: self.current_line.max(1) + line_delta,
            col: self.cur_col_off + col + 1,
            len,
            macro_name: None,
            included_from,
            fallback_text: self.cur_line_text.lines().next().map(str::to_string),
        }
    }

    fn push_error_here(&mut self, message: String) {
        let loc = self.here();
        self.errors
            .push(diagnostics::render("error", &message, &loc));
    }

    /// Print a preprocessor warning at the line being processed, once per
    /// run for identical text (the driver preprocesses a design more than
    /// once).
    fn warn_here(&self, message: &str) {
        static WARNED: std::sync::Mutex<Option<HashSet<String>>> = std::sync::Mutex::new(None);
        let text = diagnostics::render("warning", message, &self.here());
        let fresh = WARNED
            .lock()
            .map(|mut g| g.get_or_insert_with(HashSet::new).insert(text.clone()))
            .unwrap_or(true);
        if fresh {
            eprintln!("{}", text);
        }
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

    /// Whether a `` `define `` line opens a formal argument list (a `(` right
    /// after the macro name, §22.5.1) that the line does not close.
    fn define_formals_open(line: &str) -> bool {
        let Some(rest) = fast_trim_start(line).strip_prefix("`define") else {
            return false;
        };
        let rest = rest.trim_start();
        let name_len = rest
            .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '$'))
            .unwrap_or(rest.len());
        let Some(list) = rest[name_len..].strip_prefix('(') else {
            return false;
        };
        let mut depth = 1i32;
        let mut in_str = false;
        let mut prev = ' ';
        for c in list.chars() {
            if in_str {
                if c == '"' && prev != '\\' {
                    in_str = false;
                }
            } else {
                match c {
                    '"' => in_str = true,
                    '(' | '[' | '{' => depth += 1,
                    ')' | ']' | '}' => {
                        depth -= 1;
                        if depth == 0 {
                            return false;
                        }
                    }
                    _ => {}
                }
            }
            prev = c;
        }
        true
    }

    fn is_directive(trimmed: &str, name: &str) -> bool {
        if let Some(rest) = trimmed
            .strip_prefix('`')
            .and_then(|rest| rest.strip_prefix(name))
        {
            rest.is_empty() || rest.starts_with(|c: char| c.is_whitespace())
        } else {
            false
        }
    }

    /// Update the design-element nesting depth from one source line. An
    /// opening keyword counts as the line's first word or right after a
    /// closing one (`endmodule module b;`); every closing `end…` keyword on
    /// the line counts (floored at 0), so `module m; endmodule` on one line
    /// opens and closes (§22.3 `\`resetall` after it is legal). Comments and
    /// string literals are skipped; `interface class` is a class (§8.26).
    fn update_design_depth(trimmed: &str, depth: &mut i32) {
        let code = Self::strip_line_comments_and_strings(trimmed);
        let words: Vec<&str> = code
            .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '$'))
            .filter(|w| !w.is_empty())
            .collect();
        let is_open = |w: &str| {
            matches!(
                w,
                "module"
                    | "macromodule"
                    | "interface"
                    | "package"
                    | "program"
                    | "primitive"
                    | "checker"
            )
        };
        let is_close = |w: &str| {
            matches!(
                w,
                "endmodule"
                    | "endinterface"
                    | "endpackage"
                    | "endprogram"
                    | "endprimitive"
                    | "endchecker"
            )
        };
        let mut prev_close = true; // the line start counts as an opener slot
        for (i, w) in words.iter().enumerate() {
            if is_close(w) {
                if *depth > 0 {
                    *depth -= 1;
                }
                prev_close = true;
                continue;
            }
            if prev_close
                && is_open(w)
                && !(*w == "interface" && words.get(i + 1) == Some(&"class"))
            {
                *depth += 1;
            }
            prev_close = false;
        }
    }

    /// `line` without `//` and `/* … */` comments and the contents of string
    /// literals, for keyword scanning.
    fn strip_line_comments_and_strings(line: &str) -> String {
        let mut out = String::with_capacity(line.len());
        let b = line.as_bytes();
        let mut i = 0;
        while i < b.len() {
            match b[i] {
                b'/' if b.get(i + 1) == Some(&b'/') => break,
                b'/' if b.get(i + 1) == Some(&b'*') => {
                    i += 2;
                    while i < b.len() && !(b[i] == b'*' && b.get(i + 1) == Some(&b'/')) {
                        i += 1;
                    }
                    i += 2;
                    out.push(' ');
                }
                b'"' => {
                    i += 1;
                    while i < b.len() && b[i] != b'"' {
                        if b[i] == b'\\' {
                            i += 1;
                        }
                        i += 1;
                    }
                    i += 1;
                    out.push(' ');
                }
                _ => {
                    let ch = line[i..].chars().next().unwrap_or(' ');
                    out.push(ch);
                    i += ch.len_utf8();
                }
            }
        }
        out
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
            bad = true;
            why = format!("number `{}` must be a positive integer", num_tok);
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
                self.warn_here(&format!(
                    "`line level `{}` is not 0/1/2 (IEEE 1800-2017 §22.12) — ignored",
                    level
                ));
            }
        } else {
            bad = true;
            why = "unterminated filename string".into();
        }
        if bad {
            self.push_error_here(format!(
                "illegal `line directive (IEEE 1800-2017 §22.12): {}",
                why
            ));
        }
    }

    /// Parse a `1ns`-style time literal into seconds. Returns None on
    /// malformed input. LRM §22.7 Table 22-5 — units are s/ms/us/ns/ps/fs
    /// and the mantissa must be 1, 10, or 100.
    fn parse_time_literal(s: &str) -> Option<f64> {
        let s = s.trim();
        let (num_str, unit) = if let Some(stripped) = s.strip_suffix("fs") {
            (stripped, 1e-15)
        } else if let Some(stripped) = s.strip_suffix("ps") {
            (stripped, 1e-12)
        } else if let Some(stripped) = s.strip_suffix("ns") {
            (stripped, 1e-9)
        } else if let Some(stripped) = s.strip_suffix("us") {
            (stripped, 1e-6)
        } else if let Some(stripped) = s.strip_suffix("ms") {
            (stripped, 1e-3)
        } else if let Some(stripped) = s.strip_suffix("s") {
            (stripped, 1.0)
        } else {
            return None;
        };
        let mantissa: f64 = num_str.trim().parse().ok()?;
        if mantissa != 1.0 && mantissa != 10.0 && mantissa != 100.0 {
            return None;
        }
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
        let t = fast_trim_start(line);
        for kw in ["macromodule", "module", "interface", "program", "package"] {
            if let Some(rest) = t.strip_prefix(kw) {
                if !rest.starts_with(char::is_whitespace) {
                    continue;
                }
                let mut rest = rest.trim_start();
                // skip an optional lifetime qualifier
                for q in ["static", "automatic"] {
                    if let Some(r2) = rest.strip_prefix(q) {
                        if r2.starts_with(char::is_whitespace) {
                            rest = r2.trim_start();
                        }
                    }
                }
                let name: String = rest
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '$')
                    .collect();
                if name
                    .chars()
                    .next()
                    .map_or(false, |c| c.is_alphabetic() || c == '_')
                {
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
            pp.defines.insert(
                k.clone(),
                MacroDef {
                    name: k,
                    params: None,
                    body: v,
                },
            );
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
        let name = source_path
            .map(|p| p.display().to_string())
            .unwrap_or_default();
        let stripped = self.strip_file_comments(source, &name);
        let (resolved, origins) = self.resolve_directives(
            &stripped,
            source_path,
            Ctx::File {
                included_from: None,
            },
        );
        self.finish_map(&resolved, &origins);
        Self::strip_attributes(&resolved)
    }

    /// Simple preprocessing pass (no file context — `include lines are skipped).
    pub fn preprocess(&mut self, source: &str) -> String {
        // Reset per-source compiler-directive state so a `none`
        // directive from a previous file in the same process doesn't
        // pollute this one.
        crate::set_default_nettype_none_seen(false);
        let stripped = self.strip_file_comments(source, "");
        let (resolved, origins) = self.resolve_directives(
            &stripped,
            None,
            Ctx::File {
                included_from: None,
            },
        );
        self.finish_map(&resolved, &origins);
        Self::strip_attributes(&resolved)
    }

    /// Build the line map of the text just produced. A map that does not
    /// cover the text line for line (a bug) is dropped, so diagnostics fall
    /// back to the preprocessed text's own lines rather than lie.
    fn finish_map(&mut self, text: &str, origins: &[LineOrigin]) {
        let files = std::mem::take(&mut self.map_files);
        let macros = std::mem::take(&mut self.map_macros);
        let columns = std::mem::take(&mut self.map_columns);
        self.map_macro_idx.clear();
        let lines = text.as_bytes().iter().filter(|&&b| b == b'\n').count();
        self.last_map =
            (lines == origins.len()).then(|| LineMap::new(files, macros, origins, columns));
    }

    /// The line map of the text the last `preprocess_file`/`preprocess` call
    /// returned: which file, line and column each of its lines came from.
    pub fn take_line_map(&mut self) -> Option<LineMap> {
        self.last_map.take()
    }

    /// `strip_comments` of one file's text, `path` naming it in warnings,
    /// with the opt-in source relaxations applied: a NUL byte read as a
    /// space (XEZIM_RELAX_NUL_BYTES, #628) and white space between a
    /// backtick and a name removed (XEZIM_RELAX_MACRO_SPACE, #627).
    fn strip_file_comments(&self, source: &str, path: &str) -> String {
        let warn = |n: usize, what: &str, clause: &str, var: &str| {
            eprintln!(
                "{path}: warning: {n} {what} (IEEE 1800-2017 {clause}, {var})",
                path = if path.is_empty() { "<input>" } else { path }
            );
        };
        let nuls = if crate::RELAX_NUL_BYTES.get() {
            source.bytes().filter(|&b| b == 0).count()
        } else {
            0
        };
        let stripped = if nuls > 0 {
            warn(
                nuls,
                "NUL byte(s) read as white space",
                "§5.3",
                "XEZIM_RELAX_NUL_BYTES",
            );
            self.strip_comments(&source.replace('\0', " "))
        } else {
            self.strip_comments(source)
        };
        if !crate::RELAX_MACRO_SPACE.get() || !stripped.contains('`') {
            return stripped;
        }
        let (joined, spaced) = Self::join_spaced_backticks(&stripped);
        if spaced > 0 {
            warn(
                spaced,
                "backtick(s) followed by white space read as a macro usage or directive",
                "§22.5.1",
                "XEZIM_RELAX_MACRO_SPACE",
            );
        }
        joined
    }

    /// The text with the blanks and tabs removed between a backtick and the
    /// name that follows it, outside string literals, and how many there
    /// were. A `` `` `` paste is left as it is.
    fn join_spaced_backticks(text: &str) -> (String, usize) {
        let b = text.as_bytes();
        let mut out = String::with_capacity(text.len());
        let mut count = 0;
        let mut in_str = false;
        let mut seg = 0;
        let mut i = 0;
        while i < b.len() {
            match b[i] {
                b'\\' if in_str => i += 1,
                b'"' if i == 0 || b[i - 1] != b'`' => in_str = !in_str,
                b'\n' => in_str = false,
                b'`' if !in_str => {
                    if b.get(i + 1) == Some(&b'`') {
                        i += 2;
                        continue;
                    }
                    let mut j = i + 1;
                    while matches!(b.get(j), Some(b' ' | b'\t')) {
                        j += 1;
                    }
                    if j > i + 1
                        && b.get(j)
                            .is_some_and(|c| c.is_ascii_alphabetic() || *c == b'_')
                    {
                        out.push_str(&text[seg..=i]);
                        seg = j;
                        count += 1;
                        i = j;
                        continue;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        out.push_str(&text[seg..]);
        (out, count)
    }

    fn strip_comments(&self, source: &str) -> String {
        let mut result = String::with_capacity(source.len());
        let bytes = source.as_bytes();
        let n = bytes.len();
        let mut i = 0;
        while i < n {
            // Ordinary text — any UTF-8, not only ASCII — is copied verbatim;
            // only `/` and `"` need the careful path. Non-ASCII text used to be
            // re-encoded byte by byte (each byte became the Latin-1 char of the
            // same value), which DOUBLE-encoded it: a string literal `"é"`
            // decoded to four bytes instead of its two source bytes (IEEE
            // 1800-2017 §5.9: a string literal is the sequence of its bytes).
            // Stopping only at ASCII bytes keeps every slice on a char boundary.
            let run = find_byte(&bytes[i..], b"/\"").unwrap_or(n - i);
            if run > 0 {
                result.push_str(&source[i..i + run]);
                i += run;
                continue;
            }
            if bytes[i] == b'/' && i + 1 < n {
                if bytes[i + 1] == b'/' {
                    // Line comment: replace with spaces until newline to preserve line numbers
                    // BUT: keep the backslash if it's at the end of the line (continuation)
                    let start = i;
                    i += find_byte(&bytes[i..], b"\n").unwrap_or(n - i);
                    // Check if the line ends with a backslash (ignoring whitespace)
                    let mut j = i;
                    while j > start && bytes[j - 1].is_ascii_whitespace() {
                        j -= 1;
                    }
                    if j > start && bytes[j - 1] == b'\\' {
                        // Preserve the backslash by replacing everything else with spaces
                        push_spaces(&mut result, j - 1 - start);
                        result.push('\\');
                        push_spaces(&mut result, i - j);
                    } else {
                        push_spaces(&mut result, i - start);
                    }
                    continue;
                }
                if bytes[i + 1] == b'*' {
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
                    while i + 1 < n {
                        // One space per byte that is none of the three below.
                        let run = find_byte(&bytes[i..n - 1], b"*\n\\").unwrap_or(n - 1 - i);
                        if run > 0 {
                            push_spaces(&mut result, run);
                            i += run;
                            continue;
                        }
                        if bytes[i] == b'*' && bytes[i + 1] == b'/' {
                            result.push(' ');
                            result.push(' ');
                            i += 2;
                            break;
                        }
                        if bytes[i] == b'\n' {
                            result.push('\n');
                        } else if bytes[i] == b'\\' && bytes[i + 1] == b'\n' {
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
                while i < n {
                    let run = find_byte(&bytes[i..], b"\\\"").unwrap_or(n - i);
                    if run > 0 {
                        result.push_str(&source[i..i + run]);
                        i += run;
                        continue;
                    }
                    if bytes[i] == b'\\' && i + 1 < n {
                        // The escaped character is copied whole (it may be a
                        // multi-byte UTF-8 char).
                        let ch = source[i + 1..].chars().next().unwrap_or('\\');
                        result.push('\\');
                        result.push(ch);
                        i += 1 + ch.len_utf8();
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
            // §22.5.2: `undef names one macro; the text after it on the line
            // is ordinary source, split off like a conditional's (#619).
            ("`undef", true),
        ] {
            if let Some(rest) = s.strip_prefix(kw) {
                // §22: the directive name is an identifier — it ends at the
                // first character that cannot continue one. Requiring
                // WHITESPACE meant `\`endif;` (and `\`endif)`, `\`else,`)
                // was not recognised as a directive here, so it was never
                // split onto its own line and the `\`endif` handler swallowed
                // the whole line — dropping the `;` that terminated the
                // statement the conditional was wrapping. `\`elseif` still
                // does NOT match `\`else`, since `i` continues the identifier.
                if rest.is_empty()
                    || !rest.starts_with(|c: char| c.is_alphanumeric() || c == '_' || c == '$')
                {
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
    fn split_inline_conditionals(source: &str) -> (String, Option<Vec<(u32, u32)>>) {
        if !source.contains('`') {
            return (source.to_string(), None);
        }
        let mut out = String::with_capacity(source.len() + 64);
        // For each output line: (0-based source line, character column in it
        // where the output line starts). Directive pieces are trimmed, so
        // their column is approximate; only text pieces need it exact.
        let mut pos: Vec<(u32, u32)> = Vec::new();
        let mut in_define_cont = false;
        for (ln, line) in source.lines().enumerate() {
            let ln = ln as u32;
            // A line with no backtick outside a `define body passes through
            // unchanged (the last branch below), with no need to trim it.
            if !in_define_cont && !line.as_bytes().contains(&b'`') {
                out.push_str(line);
                out.push('\n');
                pos.push((ln, 0));
                continue;
            }
            let trimmed = fast_trim_start(line);
            if in_define_cont || directive_word(trimmed, "`define") {
                in_define_cont = line.trim_end().ends_with('\\');
                out.push_str(line);
                out.push('\n');
                pos.push((ln, 0));
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
                pos.push((ln, 0));
                continue;
            }
            let col_of = |byte: usize| line[..byte].chars().count() as u32;
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
                    if let Some((dir_len, takes_name)) = Self::conditional_directive_len(&line[i..])
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
                            pos.push((ln, col_of(seg)));
                        }
                        out.push_str(line[i..j].trim());
                        out.push('\n');
                        pos.push((ln, col_of(i)));
                        seg = j;
                        i = j;
                        continue;
                    }
                }
                i += 1;
            }
            out.push_str(&line[seg..]);
            out.push('\n');
            pos.push((ln, col_of(seg)));
        }
        (out, Some(pos))
    }

    /// Resolve directives in `source` and expand macros. Returns the text and
    /// the origin of each of its lines (see `crate::source_map`).
    fn resolve_directives(
        &mut self,
        source: &str,
        source_path: Option<&Path>,
        ctx: Ctx,
    ) -> (String, Vec<LineOrigin>) {
        let (source, split_pos) = Self::split_inline_conditionals(source);
        let source = source.as_str();
        let mut output = String::with_capacity(source.len());
        let mut sink = OriginSink::default();
        let mut lines = source.lines().enumerate().peekable();
        let mut ifdef_stack: Vec<IfdefState> = Vec::new();

        // Directory of the current source file (for relative `include resolution)
        let source_dir = source_path.and_then(|p| p.parent().map(|d| d.to_path_buf()));

        // Save the caller's `__FILE__` / `__LINE__` cursor (so nested
        // `include returns leave it untouched), then point it at this source.
        let saved_file = self.current_file.clone();
        let saved_line = self.current_line;
        let saved_file_idx = self.cur_file_idx;
        let saved_line_text = std::mem::take(&mut self.cur_line_text);
        let saved_col_off = self.cur_col_off;
        // Text re-resolved after a macro expansion stays at the invocation:
        // every line it emits maps there, and the cursor does not move.
        let fixed = match ctx {
            Ctx::Macro(o) => Some(o),
            Ctx::File { included_from } => {
                self.current_file = source_path
                    .map(|p| p.to_string_lossy().into_owned())
                    .unwrap_or_default();
                self.current_line = 0;
                self.map_files.push(MapFile {
                    path: if self.current_file.is_empty() {
                        "<input>".to_string()
                    } else {
                        self.current_file.clone()
                    },
                    included_from,
                });
                self.cur_file_idx = self.map_files.len() as u32 - 1;
                None
            }
        };
        // Source line of output line `li` of the split text, and the column
        // it starts at.
        let src_pos =
            |li: usize| -> (u32, u32) { split_pos.as_ref().map_or((li as u32, 0), |p| p[li]) };
        let mut last_src: i64 = -1;
        // Origin for lines emitted on behalf of the current source line.
        let mut here = fixed.unwrap_or(LineOrigin::plain(self.cur_file_idx, 1, 0));
        let mut joined: Vec<usize> = Vec::new();

        while let Some((li, line)) = lines.next() {
            sink.fill(&output, here);
            let (src, col) = src_pos(li);
            if fixed.is_none() {
                self.current_line += (src as i64 - last_src) as u32;
                last_src = src as i64;
            }
            self.cur_col_off = col;
            self.cur_line_text.clear();
            self.cur_line_text.push_str(line);
            here = fixed.unwrap_or(LineOrigin::plain(self.cur_file_idx, self.current_line, col));
            let trimmed = fast_trim(line);

            // Strip (* ... *) attributes (IEEE 1800-2017 §5.12)
            if trimmed.starts_with("(*") && trimmed.ends_with("*)") {
                output.push('\n');
                continue;
            }

            // A line with no backtick holds no directive and invokes no
            // macro: it is emitted as written. This is the path below for
            // such a line, minus the directive tests (all of which need a
            // leading backtick) and the copies macro expansion would make.
            if !line.as_bytes().contains(&b'`') {
                if !ifdef_stack.iter().all(|s| s.active) {
                    output.push('\n');
                    continue;
                }
                if crate::strict_checks() {
                    Self::update_design_depth(trimmed, &mut self.design_element_depth);
                }
                if !trimmed.is_empty() {
                    self.note_design_elements(line);
                    output.push_str(line);
                }
                output.push('\n');
                sink.fill(&output, here);
                continue;
            }

            if directive_word(trimmed, "`define") {
                // Join backslash-continuation lines (IEEE 1800-2017 §22.5.1)
                let mut consumed_lines = 1;
                let mut continuation: Vec<usize> = Vec::new();

                // For the directive, we want to strip the \ and the newline
                let mut clean_line = String::new();
                let mut current = line.to_string();
                // §22.5.1 / §5.2: the formal argument list may span lines
                // (`\`define M(a,` then `b) body`): white space includes
                // newlines, and no backslash is needed inside the list. The
                // header ended at the first line, so `b)` was read as code
                // (#606). Join lines until the list closes.
                while Self::define_formals_open(&current) && !current.trim_end().ends_with('\\') {
                    let Some((next_li, next)) = lines.next() else {
                        break;
                    };
                    current.push(' ');
                    current.push_str(next);
                    consumed_lines += 1;
                    continuation.push(next_li);
                }

                loop {
                    let text = current.as_str();
                    // Handle trailing comment if any? No, trim_end handles it if it's after \.
                    // But if comment has \, it's tricky. Let's assume clean source after strip_comments.
                    if let Some(pos) = text.trim_end().rfind('\\') {
                        if text[pos + 1..].chars().all(|c| c.is_ascii_whitespace()) {
                            clean_line.push_str(&text[..pos]);
                            if let Some((next_li, next)) = lines.next() {
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
                                continuation.push(next_li);
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
                debug_assert_eq!(consumed_lines, 1 + continuation.len());
                output.push('\n');
                sink.fill(&output, here);
                for lj in continuation {
                    let (src, col) = src_pos(lj);
                    if fixed.is_none() {
                        self.current_line += (src as i64 - last_src) as u32;
                        last_src = src as i64;
                    }
                    here = fixed.unwrap_or(LineOrigin::plain(
                        self.cur_file_idx,
                        self.current_line,
                        col,
                    ));
                    output.push('\n');
                    sink.fill(&output, here);
                }
                continue;
            }

            // IEEE 1800-2023 §22.5.2: `undefineall — clear every user-defined
            // macro. Predefined `SV_COV_*` system constants stay (re-seeded).
            // Check BEFORE `undef so the longer name wins token match.
            if directive_word(trimmed, "`undefineall") {
                if ifdef_stack.iter().all(|s| s.active) {
                    self.defines.clear();
                    Self::seed_predefined(&mut self.defines);
                }
                output.push('\n');
                continue;
            }

            if directive_word(trimmed, "`undef") {
                if ifdef_stack.iter().all(|s| s.active) {
                    let name = trimmed[6..].trim().to_string();
                    self.defines.remove(&name);
                }
                output.push('\n');
                continue;
            }

            if directive_word(trimmed, "`ifdef") {
                let name = trimmed[6..].trim();
                // Strip trailing // comments from ifdef macro name
                let name = name.split_whitespace().next().unwrap_or(name);
                let parent_active = ifdef_stack.iter().all(|s| s.active);
                let active = parent_active && self.is_defined(name);
                ifdef_stack.push(IfdefState {
                    parent_active,
                    branch_taken: active,
                    active,
                });
                output.push('\n');
                continue;
            }

            if directive_word(trimmed, "`ifndef") {
                let name = trimmed[7..].trim();
                let name = name.split_whitespace().next().unwrap_or(name);
                let parent_active = ifdef_stack.iter().all(|s| s.active);
                let active = parent_active && !self.is_defined(name);
                ifdef_stack.push(IfdefState {
                    parent_active,
                    branch_taken: active,
                    active,
                });
                output.push('\n');
                continue;
            }

            if directive_word(trimmed, "`elsif") {
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

            if directive_word(trimmed, "`else") {
                if let Some(last) = ifdef_stack.last_mut() {
                    let active = last.parent_active && !last.branch_taken;
                    last.active = active;
                    last.branch_taken = true;
                }
                output.push('\n');
                continue;
            }

            if directive_word(trimmed, "`endif") {
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
            if directive_word(trimmed, "`include") {
                // §22.4: the filename may come from a text macro
                // (`include `DEFINED_PATH). Silently dropping the line left
                // the file un-included and everything downstream undefined.
                // Expand fully: a function-like macro's body (`` `"f`" ``)
                // only turns into a string literal on a later rescan.
                let parsed = Self::parse_include_path(trimmed).or_else(|| {
                    let expanded = self.expand_macros(trimmed["`include".len()..].trim());
                    Self::parse_include_path(&format!("`include {}", expanded.trim()))
                });
                self.flush_expansion_diagnostics();
                if parsed.is_none() {
                    self.push_error_here(format!("malformed `include directive: {}", trimmed));
                }
                if let Some(inc_file) = parsed {
                    if self.include_depth < MAX_INCLUDE_DEPTH {
                        if let Some(resolved) =
                            self.resolve_include(&inc_file, source_dir.as_deref())
                        {
                            // Lossy decode — tolerate stray non-UTF-8 bytes in
                            // included RTL (replace with U+FFFD, don't fail).
                            match std::fs::read(&resolved).map(|b| {
                                String::from_utf8(b).unwrap_or_else(|e| {
                                    String::from_utf8_lossy(e.as_bytes()).into_owned()
                                })
                            }) {
                                Ok(contents) => {
                                    self.include_depth += 1;
                                    let stripped = self.strip_file_comments(
                                        &contents,
                                        &resolved.display().to_string(),
                                    );
                                    let site = (here.file, here.line);
                                    let (included, origins) = self.resolve_directives(
                                        &stripped,
                                        Some(&resolved),
                                        Ctx::File {
                                            included_from: Some(site),
                                        },
                                    );
                                    self.include_depth -= 1;
                                    output.push_str(&included);
                                    sink.extend(&output, origins);
                                    // Don't push extra newline — included content has its own
                                    continue;
                                }
                                Err(e) => {
                                    // FATAL: the design text that follows may
                                    // silently depend on declarations from this
                                    // file — every mainstream tool errors here.
                                    self.push_error_here(format!(
                                        "cannot read `include file '{}': {}",
                                        resolved.display(),
                                        e
                                    ));
                                }
                            }
                        } else {
                            // FATAL, not a warning: a failed `include used to
                            // continue preprocessing, and the missing
                            // declarations then degraded downstream — an
                            // undeclared port actual became a silent implicit
                            // net and a whole testbench checked garbage. The
                            // reference tooling hard-errors here; so do we.
                            self.push_error_here(format!(
                                "cannot find `include file '{}' (searched the including file's directory and {} include dir(s))",
                                inc_file, self.include_dirs.len()
                            ));
                        }
                    } else {
                        self.push_error_here(format!(
                            "`include depth limit ({}) exceeded for '{}' — recursive include?",
                            MAX_INCLUDE_DEPTH, inc_file
                        ));
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
            if directive_word(trimmed, "`unconnected_drive") {
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
            if directive_word(trimmed, "`nounconnected_drive") {
                self.unconnected_pull = None;
                output.push('\n');
                continue;
            }
            if directive_word(trimmed, "`default_nettype") {
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
            if directive_word(trimmed, "`begin_keywords") {
                if ifdef_stack.iter().all(|s| s.active) {
                    let rest = trimmed.trim_start_matches("`begin_keywords").trim();
                    let ver = rest.trim_matches(|c: char| c == '"' || c.is_whitespace());
                    const VALID: &[&str] = &[
                        "1800-2023",
                        "1800-2017",
                        "1800-2012",
                        "1800-2009",
                        "1800-2005",
                        "1364-2005",
                        "1364-2001",
                        "1364-2001-noconfig",
                        "1364-1995",
                    ];
                    if VALID.contains(&ver) {
                        self.keywords_stack.push(ver.to_string());
                    } else {
                        self.warn_here(&format!(
                            "`begin_keywords \"{}\" — unknown version string \
                             (IEEE 1800-2023 §22.14); accepted set is {}",
                            ver,
                            VALID.join(", ")
                        ));
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
            if directive_word(trimmed, "`end_keywords") {
                if ifdef_stack.iter().all(|s| s.active) {
                    if self.keywords_stack.pop().is_none() {
                        self.warn_here(
                            "`end_keywords without matching `begin_keywords \
                             (IEEE 1800-2023 §22.14)",
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
                    let prec_str = rest[slash + 1..]
                        .trim_end_matches("//")
                        .trim_end_matches("/*")
                        .trim();
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
                    if let Some(end) = after_num.strip_prefix('"').and_then(|r| r.find('"')) {
                        let fname = &after_num[1..1 + end];
                        let level = after_num[1 + end + 1..].trim();
                        if !matches!(level, "0" | "1" | "2") && !crate::strict_checks() {
                            self.warn_here(&format!(
                                "`line level `{}` is not 0/1/2 (IEEE 1800-2017 §22.12) — ignored",
                                level
                            ));
                        }
                        self.current_file = fname.to_string();
                        // The NEXT source line must read as `n`; the loop
                        // increments before use.
                        self.current_line = n.saturating_sub(1);
                        if fixed.is_none() {
                            let included_from = self
                                .map_files
                                .get(self.cur_file_idx as usize)
                                .and_then(|f| f.included_from);
                            self.map_files.push(MapFile {
                                path: fname.to_string(),
                                included_from,
                            });
                            self.cur_file_idx = self.map_files.len() as u32 - 1;
                        }
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
                        "`pragma requires a pragma_name (IEEE 1800-2017 §22.11)".into(),
                    );
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
                    for (lj, skipped) in lines.by_ref() {
                        sink.fill(&output, here);
                        let (src, col) = src_pos(lj);
                        if fixed.is_none() {
                            self.current_line += (src as i64 - last_src) as u32;
                            last_src = src as i64;
                        }
                        here = fixed.unwrap_or(LineOrigin::plain(
                            self.cur_file_idx,
                            self.current_line,
                            col,
                        ));
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
                         (IEEE 1800-2017 §22.3)"
                            .into(),
                    );
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
            if directive_word(trimmed, "`celldefine")
                || directive_word(trimmed, "`endcelldefine")
                || directive_word(trimmed, "`nounconnected_drive")
                || directive_word(trimmed, "`unconnected_drive")
            {
                output.push('\n');
                continue;
            }

            let mut logical_line = line.to_string();
            // Split-text indices of the lines joined into `logical_line`.
            joined.clear();
            joined.push(li);
            // §22.5.1: the actual-argument list of a macro defined with
            // formals may start on a later line than its name (white space
            // and comments between them, §5.3), so a line ending in such a
            // name is joined with the following ones like an open paren.
            while logical_line.contains('`')
                && (Self::has_unclosed_paren(&logical_line)
                    || self.ends_with_parameterized_macro(&logical_line))
            {
                if let Some((lj, next)) = lines.next() {
                    logical_line.push('\n');
                    logical_line.push_str(next);
                    joined.push(lj);
                } else {
                    break;
                }
            }
            if joined.len() > 1 {
                self.cur_line_text.clear();
                self.cur_line_text.push_str(&logical_line);
            }

            let expanded = self.expand_macros(&logical_line);
            self.flush_expansion_diagnostics();
            // Base origins for joined lines and macro text. Exact same-line
            // columns below distinguish each expansion and its following text.
            let joined_origin = |this: &mut Self, k: usize| -> LineOrigin {
                if let Some(o) = fixed {
                    return o;
                }
                let (src, col) = src_pos(joined[k]);
                let (src0, _) = src_pos(joined[0]);
                LineOrigin::plain(this.cur_file_idx, this.current_line + (src - src0), col)
            };
            let macro_origin =
                |this: &mut Self, k: usize, text: &str, out_line: &str| -> Option<LineOrigin> {
                    let base = joined_origin(this, k);
                    if fixed.is_some() {
                        return Some(base);
                    }
                    let (mcol, name) = this.first_expanded_macro(text)?;
                    // Extent of the first expansion: ordinary tokens following
                    // the call on the same line keep their own column (#398).
                    let (mend, mcall) = this
                        .first_macro_extent(text, out_line, mcol)
                        .unwrap_or((0, 0));
                    let columns = this.macro_columns(text, out_line).map_or(0, |columns| {
                        this.map_columns.push(columns);
                        this.map_columns.len() as u32
                    });
                    Some(LineOrigin {
                        mac: this.macro_index(name),
                        mcol,
                        mfirst: true,
                        mend,
                        mcall,
                        columns,
                        ..base
                    })
                };
            let (expanded, sub_origins) = if Self::contains_preprocessor_directive(&expanded) {
                let first_out = expanded.split('\n').next().unwrap_or("");
                let inv = macro_origin(self, 0, &logical_line, first_out)
                    .unwrap_or_else(|| joined_origin(self, 0));
                let (text, origins) =
                    self.resolve_directives(&expanded, source_path, Ctx::Macro(inv));
                (text, Some(origins))
            } else {
                (expanded, None)
            };
            sink.fill(&output, here);
            if fast_trim(&expanded).is_empty() {
                for k in 0..joined.len() {
                    output.push('\n');
                    let o = joined_origin(self, k);
                    sink.fill(&output, o);
                }
            } else {
                self.note_design_elements(&expanded);
                output.push_str(&expanded);
                output.push('\n');
                match sub_origins {
                    Some(mut origins) => {
                        let tail_out = expanded.rsplit('\n').next().unwrap_or("");
                        let tail = macro_origin(self, 0, &logical_line, tail_out)
                            .unwrap_or_else(|| joined_origin(self, 0));
                        origins.push(tail);
                        sink.extend(&output, origins);
                    }
                    // Nothing expanded on a single line (the common case).
                    None if joined.len() == 1 && expanded == logical_line => {
                        let o = joined_origin(self, 0);
                        sink.fill(&output, o);
                    }
                    None => {
                        let out_n = expanded.matches('\n').count() + 1;
                        let mut origins = Vec::with_capacity(out_n);
                        if out_n == joined.len() {
                            // Line-for-line: only lines the expansion changed
                            // are macro text.
                            for (k, (o, src)) in expanded
                                .split('\n')
                                .zip(logical_line.split('\n'))
                                .enumerate()
                            {
                                let org = if o == src {
                                    None
                                } else {
                                    macro_origin(self, k, src, o)
                                };
                                origins.push(org.unwrap_or_else(|| joined_origin(self, k)));
                            }
                        } else {
                            // A multi-line body: every line maps to the
                            // invocation; only the first keeps a prefix of
                            // original text.
                            let first_out = expanded.split('\n').next().unwrap_or("");
                            let first = macro_origin(self, 0, &logical_line, first_out)
                                .unwrap_or_else(|| joined_origin(self, 0));
                            origins.push(first);
                            let rest = LineOrigin {
                                mfirst: false,
                                ..first
                            };
                            origins.resize(out_n, rest);
                        }
                        sink.extend(&output, origins);
                    }
                }
            }
            // Account for additional physical lines consumed by paren-spanning
            // continuations so __LINE__ on subsequent lines stays correct.
            if fixed.is_none() {
                if let Some(&last) = joined.last() {
                    let (src, _) = src_pos(last);
                    self.current_line += (src as i64 - last_src) as u32;
                    last_src = src as i64;
                }
            }
            here = fixed.unwrap_or(LineOrigin::plain(
                self.cur_file_idx,
                self.current_line,
                self.cur_col_off,
            ));
        }
        sink.fill(&output, here);

        // Restore caller's cursor (so a returning `include leaves the outer
        // file's __FILE__/__LINE__ intact).
        self.current_file = saved_file;
        self.current_line = saved_line;
        self.cur_file_idx = saved_file_idx;
        self.cur_line_text = saved_line_text;
        self.cur_col_off = saved_col_off;

        (output, sink.origins)
    }

    /// Capture the timescale in effect for any design element this
    /// (expanded) line declares, so its scope's delays can later be scaled
    /// by the right timeunit. `module foo`, `interface bar`, `program baz`,
    /// `package p` — name is the first identifier after the keyword.
    /// Standard one-declaration-per-line form (which black-parrot uses); good
    /// enough for timescale association.
    fn note_design_elements(&mut self, expanded: &str) {
        if let Some(name) = Self::design_element_name(expanded) {
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
        // Compilation-unit ($unit) tasks and functions have no design
        // element name; they take the first `timescale in effect
        // before them, recorded once under the synthetic name "$unit".
        if let Some(ts) = self.timescale {
            if !self.module_timescales.contains_key("$unit") {
                self.module_timescales.insert("$unit".to_string(), ts);
            }
        }
    }

    /// Report what expanding the current line collected behind `&self`:
    /// strict macro-invocation errors (into the error list) and undefined
    /// macro warnings, each located at the invocation.
    fn flush_expansion_diagnostics(&mut self) {
        if !self.expansion_errors.borrow().is_empty() {
            let drained: Vec<(String, String)> =
                self.expansion_errors.borrow_mut().drain(..).collect();
            for (name, msg) in drained {
                let loc = self.here_at(&format!("`{}", name));
                self.errors.push(diagnostics::render("error", &msg, &loc));
            }
        }
        if !self.undefined_seen.borrow().is_empty() {
            self.flush_undefined_macros();
        }
    }

    /// Column (relative to the line start) and name of the first user macro
    /// invoked in `text`; `__FILE__`/`__LINE__` do not count.
    fn first_expanded_macro<'a>(&self, text: &'a str) -> Option<(u32, &'a str)> {
        let mut in_str = false;
        let b = text.as_bytes();
        let mut i = 0;
        while i < b.len() {
            match b[i] {
                b'"' if i == 0 || b[i - 1] != b'\\' => in_str = !in_str,
                b'`' if !in_str => {
                    let start = i + 1;
                    let mut j = start;
                    while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                        j += 1;
                    }
                    let name = &text[start..j];
                    if !name.is_empty()
                        && (self.defines.contains_key(name)
                            || matches!(name, "__FILE__" | "__LINE__"))
                    {
                        return Some((text[..i].chars().count() as u32, name));
                    }
                    i = j.max(i + 1);
                    continue;
                }
                _ => {}
            }
            i += 1;
        }
        None
    }

    /// Length of a complete macro invocation in `text` starting at the
    /// backtick at byte `i` (which `first_expanded_macro` reported). The call is
    /// `` `NAME `` optionally followed by a balanced `(...)` actual list.
    fn macro_call_len(text: &str, i: usize) -> usize {
        let b = text.as_bytes();
        let mut k = i + 1;
        while k < b.len() && (b[k].is_ascii_alphanumeric() || b[k] == b'_') {
            k += 1;
        }
        // The list may follow on a later line (§22.5.1), as in the lookahead.
        let mut j = Self::skip_space_and_comments(b, k);
        if b.get(j) == Some(&b'(') {
            let mut depth = 0usize;
            while j < b.len() {
                match b[j] {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            k = j + 1;
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
        }
        k - i
    }

    fn macro_invocation_end(&self, text: &str, start: usize, name: &str) -> usize {
        if self
            .defines
            .get(name)
            .is_some_and(|def| def.params.is_some())
        {
            start + Self::macro_call_len(text, start)
        } else {
            start + name.len() + 1
        }
    }

    /// Exact columns for several expansions on one source line. The common
    /// single-expansion case uses its prefix/suffix extent without re-expanding.
    /// Multiline or directive-producing expansions retain their existing map.
    fn macro_columns(&mut self, source: &str, expanded: &str) -> Option<Vec<MacroColumn>> {
        if source.contains('\n') || expanded.contains('\n') {
            return None;
        }
        let (column, name) = self.first_expanded_macro(source)?;
        let start = source.char_indices().nth(column as usize)?.0;
        let end = self.macro_invocation_end(source, start, name);
        self.first_expanded_macro(&source[end..])?;

        let mut columns = Vec::new();
        let mut input = 0;
        let mut output = 0;
        while let Some((column, name)) = self.first_expanded_macro(&source[input..]) {
            let start = input + source[input..].char_indices().nth(column as usize)?.0;
            let end = self.macro_invocation_end(source, start, name);
            let prefix = &source[input..start];
            if !expanded[output..].starts_with(prefix) {
                return None;
            }
            output += prefix.len();
            // Expansion diagnostics were already emitted for the complete
            // line. Reconstruct only its map, without reporting them twice.
            let errors = self.expansion_errors.borrow().len();
            let undefined = self.undefined_seen.borrow().len();
            let replacement = self.expand_macros(&source[start..end]);
            self.expansion_errors.borrow_mut().truncate(errors);
            self.undefined_seen.borrow_mut().truncate(undefined);
            if !expanded[output..].starts_with(&replacement) {
                return None;
            }
            let out_start = expanded[..output].chars().count() as u32;
            output += replacement.len();
            columns.push(MacroColumn {
                start: out_start,
                end: expanded[..output].chars().count() as u32,
                source_start: source[..start].chars().count() as u32,
                source_end: source[..end].chars().count() as u32,
                mac: self.macro_index(name),
            });
            input = end;
        }
        (expanded[output..] == source[input..]).then_some(columns)
    }

    /// Extent and original length of the FIRST macro invocation on a line.
    /// Returns `(mend, mcall)`:
    /// - `mend`: number of output characters substituted at the invocation;
    ///   ordinary tokens that FOLLOW it on the same line sit at/after this and
    ///   are original text, so the line map must not attribute them to the
    ///   macro.
    /// - `mcall`: character length of the invocation (`` `NAME `` plus any
    ///   balanced `(...)`) in `in_line`.
    /// `mcol` is the char column of the invocation's backtick in `in_line`.
    /// Returns `None` when the unchanged suffix cannot be found at the end;
    /// multiple expansions use `macro_columns` instead.
    fn first_macro_extent(&self, in_line: &str, out_line: &str, mcol: u32) -> Option<(u32, u32)> {
        let mbytes = in_line.char_indices().nth(mcol as usize).map(|(i, _)| i)?;
        let (_, name) = self.first_expanded_macro(in_line)?;
        let call_len = self.macro_invocation_end(in_line, mbytes, name) - mbytes;
        if call_len == 0 {
            return None;
        }
        let after_call = &in_line[mbytes + call_len..];
        let obytes = out_line.char_indices().nth(mcol as usize)?.0;
        let rest = &out_line[obytes..];
        if !rest.ends_with(after_call) {
            return None;
        }
        let at = rest.len() - after_call.len();
        // mend is a count of chars from the invocation backtick to where the
        // ordinary text resumes; mcall is the input call's char length.
        Some((
            rest[..at].chars().count() as u32,
            in_line[mbytes..mbytes + call_len].chars().count() as u32,
        ))
    }

    /// Index of `name` in the line map's macro table, plus one.
    fn macro_index(&mut self, name: &str) -> u32 {
        if let Some(&k) = self.map_macro_idx.get(name) {
            return k;
        }
        self.map_macros.push(name.to_string());
        let k = self.map_macros.len() as u32;
        self.map_macro_idx.insert(name.to_string(), k);
        k
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
        let found = self.resolve_include_first(filename, source_dir);
        if let Some(chosen) = &found {
            self.warn_shadowed_include(filename, chosen, source_dir);
        }
        found
    }

    /// A same-named header in a LATER search directory with DIFFERENT
    /// contents is silently shadowed by the search order; a stale copy that
    /// lacks declarations the design calls then elaborates with no clue why.
    /// Warn once per include name.
    fn warn_shadowed_include(&self, filename: &str, chosen: &Path, source_dir: Option<&Path>) {
        // One report per include name for the whole run: each source file
        // gets its own preprocessor, and the same header is included by many.
        static WARNED: std::sync::Mutex<Option<std::collections::HashSet<String>>> =
            std::sync::Mutex::new(None);
        if Path::new(filename).is_absolute() {
            return;
        }
        {
            let guard = WARNED.lock().unwrap();
            if guard.as_ref().is_some_and(|w| w.contains(filename)) {
                return;
            }
        }
        let chosen_bytes = std::fs::read(chosen).ok();
        let mut dirs: Vec<PathBuf> = Vec::new();
        if let Some(d) = source_dir {
            dirs.push(d.to_path_buf());
        }
        dirs.extend(self.include_dirs.iter().cloned());
        for dir in dirs {
            let other = dir.join(filename);
            if !other.exists() || same_file(&other, chosen) {
                continue;
            }
            if std::fs::read(&other).ok() == chosen_bytes {
                continue;
            }
            WARNED
                .lock()
                .unwrap()
                .get_or_insert_with(Default::default)
                .insert(filename.to_string());
            eprintln!(
                "[PP] warning: `include \"{}\" resolved to '{}'; a different copy in '{}' is shadowed by the search order",
                filename,
                chosen.display(),
                other.display()
            );
            return;
        }
    }

    fn resolve_include_first(&self, filename: &str, source_dir: Option<&Path>) -> Option<PathBuf> {
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
        if !directive_word(trimmed, "`define") {
            return;
        }
        let rest = trimmed[7..].trim(); // after `define
        // Find name
        let name_end = rest
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(rest.len());
        let name = rest[..name_end].to_string();
        let after_name = rest[name_end..].trim_start();

        // Check for parameterized macro: `define NAME(param1, param2) body
        // Note: LRM says NO space between NAME and '('
        let (params, body) = if rest[name_end..].starts_with('(') {
            // Find closing paren (handling nested parens)
            let mut depth = 0;
            let mut close_pos = None;
            for (idx, c) in rest[name_end..].char_indices() {
                if c == '(' {
                    depth += 1;
                } else if c == ')' {
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
                    "define",
                    "undef",
                    "undefineall",
                    "ifdef",
                    "ifndef",
                    "elsif",
                    "else",
                    "endif",
                    "include",
                    "line",
                    "pragma",
                    "resetall",
                    "timescale",
                    "begin_keywords",
                    "end_keywords",
                    "default_nettype",
                    "celldefine",
                    "endcelldefine",
                    "unconnected_drive",
                    "nounconnected_drive",
                    "__FILE__",
                    "__LINE__",
                ];
                if DIRECTIVES.contains(&name.as_str()) {
                    self.push_error_here(format!(
                        "`{}` is a compiler directive and cannot be redefined as \
                         a macro (IEEE 1800-2017 §22.5.1)",
                        name
                    ));
                }
                // §22.5.1: the macro text shall not contain an unterminated
                // string literal (a `"` opened in the body and never closed).
                let (mut quotes, mut esc) = (0u32, false);
                for c in body.chars() {
                    if esc {
                        esc = false;
                        continue;
                    }
                    match c {
                        '\\' => esc = true,
                        '"' => quotes += 1,
                        _ => {}
                    }
                }
                if quotes % 2 == 1 {
                    self.push_error_here(format!(
                        "macro `{}` text has an unterminated string literal \
                         (IEEE 1800-2017 §22.5.1)",
                        name
                    ));
                }
            }
            // eprintln!("[PP] defining macro '{}'", name);
            self.defines
                .insert(name.clone(), MacroDef { name, params, body });
        }
    }

    fn expand_macros(&self, source: &str) -> String {
        // Every expansion starts at a backtick; text without one is its own
        // expansion.
        if !source.contains('`') {
            return source.to_string();
        }
        let mut result = self.expand_macros_once(source);
        // Recursively expand up to 128 times to handle deeply nested macros.
        // C906's aq_idu_cfig.h chains 25+ DIS_VEC_* defines (DIS_VEC_WIDTH →
        // DIS_VEC_FUNC → DIS_VEC_EU → … → DIS_VEC_SRC1_DATA), each requiring
        // one expansion iteration. The earlier 16-step cap silently truncated
        // expansion mid-chain, leaving residual `IDENT directives that the
        // tokenizer then reported as parse errors. We stop early on
        // fixed-point so the cap only matters for pathological cases.
        for _ in 0..128 {
            if !result.contains('`') {
                break;
            }
            let next = self.expand_macros_once(&result);
            if next == result {
                break;
            }
            result = next;
        }
        if self.paste_separated.replace(false) {
            result.retain(|c| c != PASTE_SEPARATOR);
        }
        result
    }

    fn apply_token_pasting(&self, text: &str) -> String {
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
                // A usage of a defined macro ends at the `` (`` unit_`TAG``_n ``
                // is `TAG then _n): keep a separator so the name does not run
                // on into `TAG_n; `expand_macros` drops it after expansion,
                // gluing the result (#616). A name the paste itself forms
                // (`` `ID_``n `` with `ID_` no macro) is still pasted whole.
                let ident_len = result
                    .bytes()
                    .rev()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == b'_' || *c == b'$')
                    .count();
                if ident_len > 0 {
                    let head = &result[..result.len() - ident_len];
                    let name = &result[result.len() - ident_len..];
                    if head.ends_with('`')
                        && !head.ends_with("``")
                        && self.defines.contains_key(name)
                        && !self.paste_forms_macro(name, &text[i..])
                    {
                        result.push(PASTE_SEPARATOR);
                        self.paste_separated.set(true);
                    }
                }
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

    /// Whether the names a paste chain joins onto `name` form a macro, so the
    /// usage is pasted whole: `` `x``y `` with `AB` defined is `AB`, and
    /// `` `P``A``B `` with `PAB` defined is `PAB` (§22.5.1). `rest` is the
    /// text after the first ``.
    fn paste_forms_macro(&self, name: &str, mut rest: &str) -> bool {
        let mut joined = name.to_string();
        loop {
            let seg = rest
                .bytes()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == b'_' || *c == b'$')
                .count();
            // Nothing more to glue: the paste ends the name, so it is a
            // usage of whatever `joined` names (`` `uvm_pack_``da``(x) `` is
            // `uvm_pack_da(x)`, its arguments kept).
            if seg == 0 {
                return self.defines.contains_key(&joined);
            }
            joined.push_str(&rest[..seg]);
            if self.defines.contains_key(&joined) {
                return true;
            }
            match rest[seg..].strip_prefix("``") {
                Some(r) => rest = r,
                None => return false,
            }
        }
    }

    /// Whether `text` holds a `` `define `` of `name`.
    fn line_defines(text: &str, name: &str) -> bool {
        text.match_indices("`define").any(|(i, d)| {
            let rest = text[i + d.len()..].trim_start();
            rest.strip_prefix(name).is_some_and(|after| {
                !after.starts_with(|c: char| c.is_alphanumeric() || c == '_' || c == '$')
            })
        })
    }

    fn expand_macros_once(&self, line: &str) -> String {
        let line_pasted;
        let line: &str = if line.contains("``") {
            line_pasted = self.apply_token_pasting(line);
            &line_pasted
        } else {
            line
        };
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
            // Copy ordinary text in bulk: inside a string only `\\` and `"`
            // matter, outside it only `` ` `` and `"`.
            let run = if in_string {
                find_byte(&bytes[i..], b"\\\"")
            } else {
                find_byte(&bytes[i..], b"`\"")
            }
            .unwrap_or(bytes.len() - i);
            if run > 0 {
                result.push_str(&line[i..i + run]);
                i += run;
                continue;
            }
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
                if i + 1 < bytes.len() && bytes[i + 1] == b'`' {
                    // Concatenation: skip both backticks
                    i += 2;
                    continue;
                }
                if i + 1 < bytes.len() && bytes[i + 1] == b'\"' {
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
                            '\\' => {
                                result.push('\\');
                                result.push('\\');
                            }
                            '\"' => {
                                result.push('\\');
                                result.push('\"');
                            }
                            _ => result.push(ch),
                        }
                    }
                    result.push('\"');
                } else if macro_name == "__LINE__" {
                    // IEEE 1800-2023 §22.13.
                    result.push_str(&self.current_line.to_string());
                } else if let Some(def) = self.defines.get(macro_name) {
                    // eprintln!("[PP] expanding macro '{}'", macro_name);
                    // §22.5.1/§5.3: white space, newlines and comments may
                    // separate the name from its actual-argument list.
                    let p = if def.params.is_some() {
                        Self::skip_space_and_comments(bytes, i)
                    } else {
                        i
                    };
                    if def.params.is_some() && p < bytes.len() && bytes[p] == b'(' {
                        i = p;
                        // Parameterized macro: find arguments
                        let args = Self::extract_macro_args(line, &mut i);
                        let params = def.params.as_ref().unwrap();
                        // §22.5.1 strict argument-count validation: too many
                        // actuals, or a non-defaulted formal left without one.
                        if crate::strict_checks() {
                            if args.len() > params.len() {
                                self.expansion_errors.borrow_mut().push((
                                    macro_name.to_string(),
                                    format!(
                                        "macro `{}` invoked with {} arguments but only \
                                     {} are declared (IEEE 1800-2017 §22.5.1)",
                                        macro_name,
                                        args.len(),
                                        params.len()
                                    ),
                                ));
                            } else {
                                // §22.5.1: an actual at a position (even empty,
                                // via a trailing/leading comma) is legal — only a
                                // formal *beyond* the supplied positions with no
                                // default is "fewer actual arguments than formals".
                                for (pi, (pname, default)) in params.iter().enumerate() {
                                    if pi >= args.len() && default.is_none() {
                                        self.expansion_errors.borrow_mut().push((
                                            macro_name.to_string(),
                                            format!(
                                                "macro `{}` missing required argument `{}` \
                                             (IEEE 1800-2017 §22.5.1)",
                                                macro_name, pname
                                            ),
                                        ));
                                    }
                                }
                            }
                        }
                        let mut actuals: Vec<(&str, String)> = Vec::with_capacity(params.len());
                        for (pi, (pname, default)) in params.iter().enumerate() {
                            // An actual arg that is missing or blank falls back
                            // to the formal's default (SV LRM 22.5.1). e.g.
                            // `DV_CHECK(expr)` leaves the optional trailing
                            // `WITH_C_=` constraint empty.
                            let arg = match args.get(pi) {
                                Some(a) if !a.trim().is_empty() => a.clone(),
                                // §22.5.1: an empty (or white-space) actual
                                // with no default substitutes NOTHING.
                                // Leaving the formal name in the body
                                // corrupted the expansion (`F(1,)` of
                                // `a b` produced `1 b`, a parse error)
                                // and stringified as the formal's own
                                // name (`` `"b`" `` gave "b", the
                                // reference gives "").
                                _ => default.clone().unwrap_or_default(),
                            };
                            actuals.push((pname.as_str(), arg));
                        }
                        let body = Self::substitute_formals(&def.body, &actuals);
                        let body_pasted = self.apply_token_pasting(&body);
                        result.push_str(&body_pasted);
                    } else {
                        // §22.5.1: a macro defined with a formal list must be
                        // invoked with parentheses, even when empty.
                        if crate::strict_checks() && def.params.is_some() {
                            self.expansion_errors.borrow_mut().push((
                                macro_name.to_string(),
                                format!(
                                    "macro `{}` requires parentheses (it is defined with \
                                 arguments) (IEEE 1800-2017 §22.5.1)",
                                    macro_name
                                ),
                            ));
                        }
                        let body_pasted = self.apply_token_pasting(&def.body);
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
                    // A macro an expansion on this line defines (`` `define CUR n
                    // `CUR `undef CUR ``) is defined once the expansion's
                    // directives run; it is expanded then, not undefined.
                    if !Self::line_defines(line, macro_name) {
                        self.note_undefined_macro(macro_name);
                    }
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

impl Preprocessor {
    /// Replace every formal of a macro body with its actual text, in ONE pass
    /// over the body as written: substituting the formals one after another
    /// rescanned text an earlier actual had inserted, so a quote in that
    /// actual (`STOP_``a1` with `"hello"`) shifted the string-literal ranges
    /// and a later formal (`a2`) was left in the expansion.
    ///
    /// Only whole words outside string literals are replaced, so a formal
    /// name that also appears in a format string in the body — e.g. `actual`
    /// in `"actual=%0d"` — is kept.
    fn substitute_formals(body: &str, actuals: &[(&str, String)]) -> String {
        let b = body.as_bytes();
        // A `"` preceded by a backtick is the preprocessor stringify-quote
        // delimiter (`\`"..."\``), NOT a regular string literal. Per IEEE
        // 1800-2017 §22.5.1, macro formals inside `\`"..."\`` MUST be
        // substituted (then stringized), so it opens no opaque range — else
        // `uvm_type_name_decl(\`"T\`")` leaves `T` unsubstituted and
        // get_type_name returns the literal "T" instead of the class name.
        //
        // A `` inside ordinary quotes does NOT reopen the region to
        // substitution: §22.5.1 says argument substitution shall not occur
        // within a string literal, and `\`"` is the construct for building a
        // string from an argument. `"``x``"` therefore stays literal (GitHub
        // #62 asked for it to expand; a reference simulator leaves it alone
        // too, so expanding would be a divergence).
        let mut string_ranges: Vec<(usize, usize)> = Vec::new();
        let mut i = 0;
        while i < b.len() {
            if b[i] == b'"' && !(i > 0 && b[i - 1] == b'`') {
                let start = i;
                i += 1;
                while i < b.len() {
                    if b[i] == b'\\' && i + 1 < b.len() {
                        i += 2;
                        continue;
                    }
                    if b[i] == b'"' {
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                string_ranges.push((start, i));
            } else {
                i += 1;
            }
        }
        let in_string = |pos: usize| string_ranges.iter().any(|(lo, hi)| pos >= *lo && pos < *hi);
        let is_word = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
        let mut out = String::with_capacity(body.len());
        let mut last = 0;
        let mut i = 0;
        while i < b.len() {
            if !is_word(b[i]) {
                i += 1;
                continue;
            }
            let start = i;
            while i < b.len() && is_word(b[i]) {
                i += 1;
            }
            let word = &body[start..i];
            if in_string(start) {
                continue;
            }
            if let Some((_, arg)) = actuals.iter().find(|(name, _)| *name == word) {
                out.push_str(&body[last..start]);
                out.push_str(arg);
                last = i;
            }
        }
        out.push_str(&body[last..]);
        out
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
                if c == b'\\' {
                    i += 2;
                    continue;
                }
                if c == b'"' {
                    in_string = false;
                }
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
                b'}' if !in_string => {
                    if brace_depth > 0 {
                        brace_depth -= 1;
                    }
                }
                b'[' if !in_string => bracket_depth += 1,
                b']' if !in_string => {
                    if bracket_depth > 0 {
                        bracket_depth -= 1;
                    }
                }
                b',' if !in_string
                    && paren_depth == 1
                    && brace_depth == 0
                    && bracket_depth == 0 =>
                {
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
        // Start of the text not yet copied to `result`.
        let mut copied = 0;
        let mut in_string = false;
        // Only `"` (string state) and `(` (attribute start) matter; every
        // other byte is copied through unchanged, in bulk.
        while let Some(off) = find_byte(&bytes[i..], b"\"(") {
            i += off;
            if bytes[i] == b'\"' {
                if i == 0 || bytes[i - 1] != b'\\' {
                    in_string = !in_string;
                }
                i += 1;
                continue;
            }
            if !in_string && i + 1 < bytes.len() && bytes[i + 1] == b'*'
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
                    // Blank the attribute out character for character, so
                    // line and column numbers after it are unchanged.
                    result.push_str(&line[copied..i]);
                    for ch in line[i..j].chars() {
                        result.push(if ch == '\n' { '\n' } else { ' ' });
                    }
                    i = j;
                    copied = j;
                    continue;
                }
            }
            i += 1;
        }
        result.push_str(&line[copied..]);
        result
    }

    /// The first byte at or after `i` that is not white space or part of a
    /// comment (`// ...` to the end of its line, `/* ... */`).
    fn skip_space_and_comments(bytes: &[u8], mut i: usize) -> usize {
        loop {
            while i < bytes.len() && matches!(bytes[i], b' ' | b'\t' | b'\n' | b'\r' | b'\x0c') {
                i += 1;
            }
            if bytes[i..].starts_with(b"//") {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            if bytes[i..].starts_with(b"/*") {
                match find_byte_seq(&bytes[i + 2..], b"*/") {
                    Some(k) => {
                        i += 2 + k + 2;
                        continue;
                    }
                    None => return bytes.len(),
                }
            }
            return i;
        }
    }

    /// Whether `line` ends, outside a string, with the use of a macro defined
    /// with formal arguments followed only by white space and comments: its
    /// argument list must still come (§22.5.1).
    fn ends_with_parameterized_macro(&self, line: &str) -> bool {
        let bytes = line.as_bytes();
        let mut in_string = false;
        let mut last: Option<usize> = None;
        let mut i = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'\\' if in_string => i += 1,
                b'"' => in_string = !in_string,
                b'/' if !in_string && bytes[i..].starts_with(b"//") => {
                    while i < bytes.len() && bytes[i] != b'\n' {
                        i += 1;
                    }
                    continue;
                }
                b'`' if !in_string => last = Some(i),
                _ => {}
            }
            i += 1;
        }
        let Some(at) = last else {
            return false;
        };
        let start = at + 1;
        let mut end = start;
        while end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
            end += 1;
        }
        if end == start || Self::skip_space_and_comments(bytes, end) != bytes.len() {
            return false;
        }
        self.defines
            .get(&line[start..end])
            .is_some_and(|d| d.params.is_some())
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
        // Every directive below starts with a backtick.
        if !text.contains('`') {
            return false;
        }
        text.lines().any(|line| {
            matches!(
                fast_trim_start(line),
                trimmed if directive_word(trimmed, "`ifdef")
                    || directive_word(trimmed, "`ifndef")
                    || directive_word(trimmed, "`elsif")
                    || directive_word(trimmed, "`else")
                    || directive_word(trimmed, "`endif")
                    || directive_word(trimmed, "`include")
                    || directive_word(trimmed, "`undef")
                    || directive_word(trimmed, "`define")
            )
        })
    }
}

/// Two paths name the same file (after canonicalization), so a directory
/// listed twice never counts as a shadowing copy.
fn same_file(a: &Path, b: &Path) -> bool {
    match (a.canonicalize(), b.canonicalize()) {
        (Ok(x), Ok(y)) => x == y,
        _ => a == b,
    }
}
