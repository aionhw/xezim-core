//! SystemVerilog preprocessor (IEEE 1800-2017 §22)
//!
//! Handles `define, `ifdef/`ifndef/`else/`endif, `include, `undef, etc.
//! This is a simplified preprocessor suitable for parsing purposes.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
pub struct MacroDef {
    pub name: String,
    pub params: Option<Vec<String>>,
    pub body: String,
}

pub struct Preprocessor {
    defines: HashMap<String, MacroDef>,
    /// Directories to search for `include files (in order).
    /// The directory of the current source file is always searched first.
    include_dirs: Vec<PathBuf>,
    /// Current include depth (to prevent infinite recursion).
    include_depth: usize,
}

const MAX_INCLUDE_DEPTH: usize = 32;

#[derive(Clone, Copy)]
struct IfdefState {
    parent_active: bool,
    branch_taken: bool,
    active: bool,
}

impl Preprocessor {
    pub fn new() -> Self {
        let mut defines = HashMap::new();
        // IEEE 1800-2017 §39.6: predefined $coverage_control control constants.
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
        Self {
            defines,
            include_dirs: Vec::new(),
            include_depth: 0,
        }
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
        self.defines.contains_key(name)
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
                    // Block comment: replace with spaces and newlines
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

    fn resolve_directives(&mut self, source: &str, source_path: Option<&Path>) -> String {
        let mut output = String::with_capacity(source.len());
        let mut lines = source.lines().peekable();
        let mut ifdef_stack: Vec<IfdefState> = Vec::new();

        // Directory of the current source file (for relative `include resolution)
        let source_dir = source_path.and_then(|p| p.parent().map(|d| d.to_path_buf()));

        while let Some(line) = lines.next() {
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
                                consumed_lines += 1;
                                current = next.to_string();
                                continue;
                            }
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

            // Handle `include — read and recursively preprocess the included file
            if trimmed.starts_with("`include") {
                if let Some(inc_file) = Self::parse_include_path(trimmed) {
                    if self.include_depth < MAX_INCLUDE_DEPTH {
                        if let Some(resolved) = self.resolve_include(&inc_file, source_dir.as_deref()) {
                            match std::fs::read_to_string(&resolved) {
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
                                    eprintln!("[PP] warning: cannot read `include file '{}': {}", resolved.display(), e);
                                }
                            }
                        } else {
                            eprintln!("[PP] warning: cannot find `include file '{}'", inc_file);
                        }
                    } else {
                        eprintln!("[PP] warning: `include depth limit ({}) exceeded for '{}'", MAX_INCLUDE_DEPTH, inc_file);
                    }
                }
                output.push('\n');
                continue;
            }

            // Skip `timescale and other compiler directives
            // that don't affect simulation semantics
            if trimmed.starts_with("`timescale")
                || trimmed.starts_with("`default_nettype")
                || trimmed.starts_with("`celldefine") || trimmed.starts_with("`endcelldefine")
                || trimmed.starts_with("`resetall")
                || trimmed.starts_with("`nounconnected_drive") || trimmed.starts_with("`unconnected_drive")
                || trimmed.starts_with("`pragma")
                || trimmed.starts_with("`begin_keywords") || trimmed.starts_with("`end_keywords")
                || trimmed.starts_with("`line")
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
                output.push_str(&expanded);
                output.push('\n');
            }
        }

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
                let params: Vec<String> = param_str.split(',')
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty())
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
        // Recursively expand up to 16 times to handle nested macros
        for _ in 0..16 {
            if !result.contains('`') { break; }
            let next = self.expand_macros_once(&result);
            if next == result { break; }
            result = next;
        }
        result
    }

    fn expand_macros_once(&self, line: &str) -> String {
        let mut result = String::with_capacity(line.len());
        let bytes = line.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
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
                
                i += 1;
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let macro_name = &line[start..i];
                if macro_name == "__FILE__" {
                    result.push('\"');
                    result.push_str("file"); // Placeholder
                    result.push('\"');
                } else if macro_name == "__LINE__" {
                    result.push_str("0"); // Placeholder
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
                        let mut body = def.body.clone();
                        for (pi, pname) in params.iter().enumerate() {
                            if let Some(arg) = args.get(pi) {
                                // Replace only whole words
                                let mut new_body = String::with_capacity(body.len());
                                let mut last = 0;
                                for (start, part) in body.match_indices(pname) {
                                    // Check if surrounding characters are word characters
                                    let before = body.as_bytes().get(start.wrapping_sub(1)).copied().unwrap_or(0);
                                    let after = body.as_bytes().get(start + part.len()).copied().unwrap_or(0);
                                    
                                    new_body.push_str(&body[last..start]);
                                    if !(before.is_ascii_alphanumeric() || before == b'_') &&
                                       !(after.is_ascii_alphanumeric() || after == b'_') {
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
                        result.push_str(&body);
                    } else {
                        result.push_str(&def.body);
                    }
                } else {
                    result.push('`');
                    result.push_str(macro_name);
                }
            } else {
                let ch = line[i..].chars().next().unwrap();
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
