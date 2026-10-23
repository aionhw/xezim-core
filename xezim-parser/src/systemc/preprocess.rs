//! Token-level C preprocessor for the SystemC front end (ISO/IEC
//! 14882:2017 §19).
//!
//! Works on the tokens of [`super::lexer`] rather than on text, so every
//! token keeps the file and byte range it came from; a token produced by a
//! macro expansion carries the span of the macro's invocation.
//!
//! The SystemC and TLM library headers are not read: `#include <systemc>`
//! (and every other header that cannot be found in angle brackets, or a
//! quoted SystemC/TLM header) is skipped, and the parser recognizes the
//! SystemC macros (`SC_MODULE`, `SC_CTOR`, …) as syntax of their own. A
//! design's own headers are included normally.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use super::lexer::lex;
use super::token::{ScSpan, ScToken, ScTokenKind};
use super::{ScDiagnostic, ScFile};

/// Nesting limit for `#include`, so a header that includes itself without a
/// guard is diagnosed instead of exhausting the stack.
const MAX_INCLUDE_DEPTH: usize = 200;

#[derive(Debug, Clone)]
struct Macro {
    /// `None` for an object-like macro.
    params: Option<Vec<String>>,
    /// The last parameter is `__VA_ARGS__` (or a named `args...`).
    variadic: bool,
    body: Vec<ScToken>,
}

/// One `#if` group on the conditional stack.
struct Cond {
    /// Tokens in the current branch are kept.
    active: bool,
    /// Some branch of the group has already been taken.
    taken: bool,
    /// `#else` has been seen (a later `#elif`/`#else` is an error).
    seen_else: bool,
    /// The enclosing region is active.
    parent: bool,
    span: ScSpan,
}

/// A token on the expansion work list with its hide set: the macros whose
/// expansion produced it, which must not expand it again (§19.3.4).
#[derive(Clone)]
struct PTok {
    tok: ScToken,
    hide: Rc<BTreeSet<String>>,
}

pub struct Preprocessor {
    pub files: Vec<ScFile>,
    pub diags: Vec<ScDiagnostic>,
    include_dirs: Vec<PathBuf>,
    macros: BTreeMap<String, Macro>,
    pragma_once: BTreeSet<PathBuf>,
    depth: usize,
    /// `__cplusplus` and the `-D` definitions, defined when [`Self::run`]
    /// starts so the main file is always file 0.
    predefined: Vec<(String, String)>,
}

/// Headers of the SystemC/TLM libraries, which a design may name in
/// quotes. Skipped like any unresolvable `<…>` header.
fn is_library_header(name: &str) -> bool {
    let base = name.trim_start_matches("./");
    matches!(
        base,
        "systemc" | "systemc.h" | "tlm" | "tlm.h" | "tlm_h" | "systemc-ams" | "systemc-ams.h"
    ) || ["sysc/", "tlm_core/", "tlm_utils/", "tlm_h/", "scv"]
        .iter()
        .any(|p| base.starts_with(p))
}

impl Preprocessor {
    pub fn new(include_dirs: &[&str], defines: &[(&str, &str)]) -> Self {
        let mut pp = Preprocessor {
            files: Vec::new(),
            diags: Vec::new(),
            include_dirs: include_dirs.iter().map(PathBuf::from).collect(),
            macros: BTreeMap::new(),
            pragma_once: BTreeSet::new(),
            depth: 0,
            predefined: Vec::new(),
        };
        pp.predefined
            .push(("__cplusplus".to_string(), "201703L".to_string()));
        for (name, value) in defines {
            pp.predefined.push((name.to_string(), value.to_string()));
        }
        pp
    }

    /// Define an object-like macro from the command line (`-D name=value`).
    fn define_text(&mut self, name: &str, value: &str) {
        // Command-line definitions live in a pseudo-file so their tokens
        // still have a valid span.
        let id = self.add_file(format!("<command line {}>", name), value.to_string());
        let mut d = Vec::new();
        let body = lex(value, id, &mut d);
        self.diags.extend(d);
        self.macros.insert(
            name.to_string(),
            Macro {
                params: None,
                variadic: false,
                body,
            },
        );
    }

    fn add_file(&mut self, path: String, text: String) -> u32 {
        self.files.push(ScFile { path, text });
        (self.files.len() - 1) as u32
    }

    /// Preprocess `text` (named `path`, possibly a pseudo-name such as
    /// `<input>`) and everything it includes.
    pub fn run(&mut self, path: &str, text: String) -> Vec<ScToken> {
        let id = self.add_file(path.to_string(), text);
        for (name, value) in std::mem::take(&mut self.predefined) {
            self.define_text(&name, &value);
        }
        let mut out = Vec::new();
        self.process_file(id, &mut out);
        out
    }

    fn process_file(&mut self, file: u32, out: &mut Vec<ScToken>) {
        let mut lex_diags = Vec::new();
        let toks = lex(&self.files[file as usize].text, file, &mut lex_diags);
        self.diags.extend(lex_diags);

        let mut conds: Vec<Cond> = Vec::new();
        let active = |conds: &Vec<Cond>| conds.last().is_none_or(|c| c.active);
        let mut i = 0;
        while i < toks.len() {
            if toks[i].line_start && toks[i].is_punct("#") {
                let mut j = i + 1;
                while j < toks.len() && !toks[j].line_start {
                    j += 1;
                }
                self.directive(file, &toks[i], &toks[i + 1..j], &mut conds, out);
                i = j;
                continue;
            }
            // A run of ordinary text up to the next directive line. A
            // function-like macro's arguments may span lines, never a
            // directive.
            let mut j = i;
            while j < toks.len() && !(toks[j].line_start && toks[j].is_punct("#")) {
                j += 1;
            }
            if active(&conds) {
                let expanded = self.expand(toks[i..j].to_vec());
                out.extend(expanded);
            }
            i = j;
        }
        for c in conds {
            self.diags.push(ScDiagnostic::error(
                "unterminated conditional directive",
                c.span,
            ));
        }
    }

    fn directive(
        &mut self,
        file: u32,
        hash: &ScToken,
        line: &[ScToken],
        conds: &mut Vec<Cond>,
        out: &mut Vec<ScToken>,
    ) {
        let active = conds.last().is_none_or(|c| c.active);
        let Some(name_tok) = line.first() else {
            return; // null directive
        };
        let name = name_tok.text.as_str();
        let rest = &line[1..];
        let span = hash.span.to(line.last().map_or(hash.span, |t| t.span));
        match name {
            "if" | "ifdef" | "ifndef" => {
                let value = if !active {
                    false
                } else if name == "if" {
                    self.eval_condition(rest, span)
                } else {
                    match rest.first() {
                        Some(t) if matches!(t.kind, ScTokenKind::Ident | ScTokenKind::Keyword) => {
                            self.macros.contains_key(&t.text) == (name == "ifdef")
                        }
                        _ => {
                            self.diags.push(ScDiagnostic::error(
                                format!("macro name missing after #{}", name),
                                span,
                            ));
                            false
                        }
                    }
                };
                conds.push(Cond {
                    active: active && value,
                    taken: value,
                    seen_else: false,
                    parent: active,
                    span,
                });
            }
            "elif" | "else" => {
                let Some(c) = conds.last_mut() else {
                    self.diags
                        .push(ScDiagnostic::error(format!("#{} without #if", name), span));
                    return;
                };
                if c.seen_else {
                    self.diags
                        .push(ScDiagnostic::error(format!("#{} after #else", name), span));
                }
                let parent = c.parent;
                let taken = c.taken;
                let value = if !parent || taken {
                    false
                } else if name == "elif" {
                    self.eval_condition(rest, span)
                } else {
                    true
                };
                let c = conds.last_mut().expect("checked above");
                c.active = parent && value;
                c.taken |= value;
                c.seen_else |= name == "else";
            }
            "endif" => {
                if conds.pop().is_none() {
                    self.diags
                        .push(ScDiagnostic::error("#endif without #if", span));
                }
            }
            _ if !active => {} // other directives in a skipped group are ignored
            "define" => self.define(rest, span),
            "undef" => match rest.first() {
                Some(t) if matches!(t.kind, ScTokenKind::Ident | ScTokenKind::Keyword) => {
                    self.macros.remove(&t.text);
                }
                _ => self
                    .diags
                    .push(ScDiagnostic::error("macro name missing after #undef", span)),
            },
            "include" | "include_next" => self.include(file, rest, span, out),
            "error" | "warning" => {
                let msg = format!("#{} {}", name, spell(rest));
                let d = if name == "error" {
                    ScDiagnostic::error(msg, span)
                } else {
                    ScDiagnostic::warning(msg, span)
                };
                self.diags.push(d);
            }
            "pragma" => {
                if rest.first().is_some_and(|t| t.text == "once") {
                    let path = canonical(&self.files[file as usize].path);
                    self.pragma_once.insert(path);
                }
            }
            "line" | "ident" | "sccs" => {}
            _ if name_tok.kind == ScTokenKind::IntLit => {} // `# 12 "file"` line marker
            _ => self.diags.push(ScDiagnostic::error(
                format!("unknown preprocessing directive #{}", name),
                span,
            )),
        }
    }

    fn define(&mut self, rest: &[ScToken], span: ScSpan) {
        let Some(name) = rest
            .first()
            .filter(|t| matches!(t.kind, ScTokenKind::Ident | ScTokenKind::Keyword))
        else {
            self.diags.push(ScDiagnostic::error(
                "macro name missing after #define",
                span,
            ));
            return;
        };
        if name.text == "defined" {
            self.diags.push(ScDiagnostic::error(
                "'defined' cannot be used as a macro name",
                name.span,
            ));
            return;
        }
        let mut k = 1;
        let mut params = None;
        let mut variadic = false;
        if rest
            .get(1)
            .is_some_and(|t| t.is_punct("(") && !t.space_before)
        {
            let mut list = Vec::new();
            k = 2;
            loop {
                match rest.get(k) {
                    Some(t) if t.is_punct(")") && !variadic && list.is_empty() => {
                        k += 1;
                        break;
                    }
                    Some(t) if t.is_punct("...") => {
                        list.push("__VA_ARGS__".to_string());
                        variadic = true;
                        k += 1;
                    }
                    Some(t) if matches!(t.kind, ScTokenKind::Ident | ScTokenKind::Keyword) => {
                        list.push(t.text.clone());
                        k += 1;
                        if rest.get(k).is_some_and(|t| t.is_punct("...")) {
                            variadic = true;
                            k += 1;
                        }
                    }
                    _ => {
                        self.diags.push(ScDiagnostic::error(
                            format!("malformed parameter list in definition of '{}'", name.text),
                            span,
                        ));
                        return;
                    }
                }
                match rest.get(k) {
                    Some(t) if t.is_punct(")") => {
                        k += 1;
                        break;
                    }
                    Some(t) if t.is_punct(",") && !variadic => k += 1,
                    _ => {
                        self.diags.push(ScDiagnostic::error(
                            format!("malformed parameter list in definition of '{}'", name.text),
                            span,
                        ));
                        return;
                    }
                }
            }
            params = Some(list);
        }
        let body = rest[k..].to_vec();
        if let (Some(first), Some(last)) = (body.first(), body.last())
            && (first.is_punct("##") || last.is_punct("##"))
        {
            self.diags.push(ScDiagnostic::error(
                "'##' cannot appear at either end of a macro expansion",
                span,
            ));
            return;
        }
        self.macros.insert(
            name.text.clone(),
            Macro {
                params,
                variadic,
                body,
            },
        );
    }

    fn include(&mut self, file: u32, rest: &[ScToken], span: ScSpan, out: &mut Vec<ScToken>) {
        let rest = if rest.first().is_some_and(|t| t.kind == ScTokenKind::Ident) {
            self.expand(rest.to_vec())
        } else {
            rest.to_vec()
        };
        let Some((name, angled)) = header_name(&rest, &self.files) else {
            self.diags.push(ScDiagnostic::error(
                "expected \"FILENAME\" or <FILENAME>",
                span,
            ));
            return;
        };
        let Some(path) = self.resolve(file, &name, angled) else {
            if !angled && !is_library_header(&name) {
                self.diags.push(ScDiagnostic::warning(
                    format!("cannot find include file '{}'; skipped", name),
                    span,
                ));
            }
            return;
        };
        if self
            .pragma_once
            .contains(&canonical(&path.to_string_lossy()))
        {
            return;
        }
        if self.depth >= MAX_INCLUDE_DEPTH {
            self.diags
                .push(ScDiagnostic::error("#include nested too deeply", span));
            return;
        }
        let text = match std::fs::read(&path) {
            Ok(b) => String::from_utf8_lossy(&b).into_owned(),
            Err(e) => {
                self.diags.push(ScDiagnostic::error(
                    format!("cannot read '{}': {}", path.display(), e),
                    span,
                ));
                return;
            }
        };
        let id = self.add_file(path.to_string_lossy().into_owned(), text);
        self.depth += 1;
        self.process_file(id, out);
        self.depth -= 1;
    }

    /// Where `#include "name"` / `<name>` in `file` refers to: the including
    /// file's directory first for the quoted form, then each `-I` directory.
    fn resolve(&self, file: u32, name: &str, angled: bool) -> Option<PathBuf> {
        if Path::new(name).is_absolute() {
            return Path::new(name).is_file().then(|| PathBuf::from(name));
        }
        let mut dirs: Vec<PathBuf> = Vec::new();
        if !angled {
            let cur = Path::new(&self.files[file as usize].path);
            if let Some(parent) = cur.parent() {
                dirs.push(if parent.as_os_str().is_empty() {
                    PathBuf::from(".")
                } else {
                    parent.to_path_buf()
                });
            }
        }
        dirs.extend(self.include_dirs.iter().cloned());
        dirs.into_iter().map(|d| d.join(name)).find(|p| p.is_file())
    }

    // ---- macro expansion ------------------------------------------------

    /// Fully macro-expand `toks`.
    fn expand(&mut self, toks: Vec<ScToken>) -> Vec<ScToken> {
        let empty = Rc::new(BTreeSet::new());
        let work: Vec<PTok> = toks
            .into_iter()
            .map(|tok| PTok {
                tok,
                hide: empty.clone(),
            })
            .collect();
        self.expand_ptoks(work).into_iter().map(|p| p.tok).collect()
    }

    fn expand_ptoks(&mut self, input: Vec<PTok>) -> Vec<PTok> {
        // The work list is kept reversed so the next token is at the end.
        let mut work: Vec<PTok> = input;
        work.reverse();
        let mut out = Vec::new();
        while let Some(pt) = work.pop() {
            let t = &pt.tok;
            let expandable = matches!(t.kind, ScTokenKind::Ident | ScTokenKind::Keyword)
                && !pt.hide.contains(&t.text);
            if !expandable {
                out.push(pt);
                continue;
            }
            if let Some(builtin) = self.builtin_macro(t) {
                out.push(PTok {
                    tok: builtin,
                    hide: pt.hide.clone(),
                });
                continue;
            }
            let Some(mac) = self.macros.get(&t.text).cloned() else {
                out.push(pt);
                continue;
            };
            let call_span = t.span;
            let mut hide = (*pt.hide).clone();
            hide.insert(t.text.clone());
            let hide = Rc::new(hide);
            let replaced = match &mac.params {
                None => self.substitute(&mac, &[], call_span),
                Some(params) => {
                    if !work.last().is_some_and(|n| n.tok.is_punct("(")) {
                        // A function-like macro name not followed by `(` is
                        // an ordinary identifier.
                        out.push(pt);
                        continue;
                    }
                    work.pop();
                    let Some((args, close_span)) = collect_args(&mut work) else {
                        self.diags.push(ScDiagnostic::error(
                            format!("unterminated argument list invoking macro '{}'", t.text),
                            call_span,
                        ));
                        break;
                    };
                    let args = match fit_args(args, params.len(), mac.variadic) {
                        Ok(a) => a,
                        Err(n) => {
                            self.diags.push(ScDiagnostic::error(
                                format!(
                                    "macro '{}' requires {} argument(s), but {} given",
                                    t.text,
                                    params.len(),
                                    n
                                ),
                                call_span.to(close_span),
                            ));
                            continue;
                        }
                    };
                    self.substitute(&mac, &args, call_span)
                }
            };
            for tok in replaced.into_iter().rev() {
                work.push(PTok {
                    tok,
                    hide: hide.clone(),
                });
            }
        }
        out
    }

    /// `__LINE__`, `__FILE__` and friends at `t`.
    fn builtin_macro(&self, t: &ScToken) -> Option<ScToken> {
        let (kind, text) = match t.text.as_str() {
            "__LINE__" => {
                let src = &self.files.get(t.span.file as usize)?.text;
                let line = 1 + src.as_bytes()[..(t.span.start as usize).min(src.len())]
                    .iter()
                    .filter(|&&b| b == b'\n')
                    .count();
                (ScTokenKind::IntLit, line.to_string())
            }
            "__FILE__" => {
                let path = &self.files.get(t.span.file as usize)?.path;
                (ScTokenKind::StringLit, quote(path))
            }
            "__DATE__" => (ScTokenKind::StringLit, "\"Jan  1 1970\"".to_string()),
            "__TIME__" => (ScTokenKind::StringLit, "\"00:00:00\"".to_string()),
            _ => return None,
        };
        Some(ScToken {
            kind,
            text,
            span: t.span,
            line_start: false,
            space_before: t.space_before,
        })
    }

    /// The replacement list of `mac` with `args` substituted, `#` applied and
    /// `##` pasted; every token placed at `call`.
    fn substitute(&mut self, mac: &Macro, args: &[Vec<PTok>], call: ScSpan) -> Vec<ScToken> {
        let params: &[String] = mac.params.as_deref().unwrap_or(&[]);
        let param_index = |t: &ScToken| -> Option<usize> {
            if matches!(t.kind, ScTokenKind::Ident | ScTokenKind::Keyword) {
                params.iter().position(|p| *p == t.text)
            } else {
                None
            }
        };
        let body = &mac.body;
        let mut res: Vec<ScToken> = Vec::new();
        // The left operand of a pending `##` came from an empty argument.
        let mut last_empty = false;
        let mut paste_next = false;
        let mut k = 0;
        while k < body.len() {
            let bt = &body[k];
            let next_is_paste = body.get(k + 1).is_some_and(|n| n.is_punct("##"));
            let piece: Vec<ScToken>;
            let mut from_va_args = false;
            if bt.is_punct("##") {
                paste_next = true;
                k += 1;
                continue;
            } else if mac.params.is_some() && bt.is_punct("#") {
                match body.get(k + 1).and_then(param_index) {
                    Some(p) => {
                        piece = vec![ScToken {
                            kind: ScTokenKind::StringLit,
                            text: stringize(&args[p]),
                            span: call,
                            line_start: false,
                            space_before: bt.space_before,
                        }];
                        k += 2;
                    }
                    None => {
                        self.diags.push(ScDiagnostic::error(
                            "'#' is not followed by a macro parameter",
                            call,
                        ));
                        piece = vec![bt.clone()];
                        k += 1;
                    }
                }
            } else if let Some(p) = param_index(bt) {
                from_va_args = params[p] == "__VA_ARGS__";
                let raw = paste_next || next_is_paste;
                let toks = if raw {
                    args[p].clone()
                } else {
                    self.expand_ptoks(args[p].clone())
                };
                piece = toks
                    .into_iter()
                    .enumerate()
                    .map(|(n, pt)| ScToken {
                        span: call,
                        line_start: false,
                        space_before: if n == 0 {
                            bt.space_before
                        } else {
                            pt.tok.space_before
                        },
                        ..pt.tok
                    })
                    .collect();
                k += 1;
            } else {
                piece = vec![ScToken {
                    span: call,
                    line_start: false,
                    ..bt.clone()
                }];
                k += 1;
            }

            if paste_next {
                paste_next = false;
                if piece.is_empty() {
                    // GNU `, ## __VA_ARGS__`: an empty variadic argument
                    // swallows the comma before it.
                    if from_va_args && !last_empty && res.last().is_some_and(|t| t.is_punct(",")) {
                        res.pop();
                    }
                    continue;
                }
                // A non-empty `, ## __VA_ARGS__` keeps the comma: GNU
                // defines no paste there.
                let gnu_comma = from_va_args && res.last().is_some_and(|t| t.is_punct(","));
                if last_empty || res.is_empty() || gnu_comma {
                    last_empty = false;
                    res.extend(piece);
                    continue;
                }
                let lhs = res.pop().expect("checked non-empty");
                let mut rest = piece.into_iter();
                let rhs = rest.next().expect("checked non-empty");
                res.push(self.paste(lhs, rhs, call));
                res.extend(rest);
                last_empty = false;
            } else {
                last_empty = piece.is_empty();
                res.extend(piece);
            }
        }
        res
    }

    /// `lhs ## rhs`: one token spelled as the two concatenated (§19.3.3).
    fn paste(&mut self, lhs: ScToken, rhs: ScToken, call: ScSpan) -> ScToken {
        let joined = format!("{}{}", lhs.text, rhs.text);
        let mut d = Vec::new();
        let toks = lex(&joined, call.file, &mut d);
        if d.is_empty() && toks.len() == 1 {
            let t = toks.into_iter().next().expect("one token");
            return ScToken {
                span: call,
                line_start: false,
                space_before: lhs.space_before,
                ..t
            };
        }
        self.diags.push(ScDiagnostic::error(
            format!(
                "pasting \"{}\" and \"{}\" does not give a valid preprocessing token",
                lhs.text, rhs.text
            ),
            call,
        ));
        ScToken {
            kind: lhs.kind,
            text: joined,
            span: call,
            line_start: false,
            space_before: lhs.space_before,
        }
    }

    // ---- #if evaluation -------------------------------------------------

    fn eval_condition(&mut self, toks: &[ScToken], span: ScSpan) -> bool {
        // `defined X` / `defined(X)` and `__has_include(…)` are resolved
        // before expansion so their operands are not expanded (§19.1).
        let mut pre: Vec<ScToken> = Vec::new();
        let mut i = 0;
        while i < toks.len() {
            let t = &toks[i];
            if t.is_ident("defined") || t.is_ident("__has_include") {
                let is_defined = t.text == "defined";
                let (inner, next) = if toks.get(i + 1).is_some_and(|n| n.is_punct("(")) {
                    match toks[i + 2..].iter().position(|n| n.is_punct(")")) {
                        Some(p) => (&toks[i + 2..i + 2 + p], i + 3 + p),
                        None => (&toks[i + 2..], toks.len()),
                    }
                } else {
                    (
                        &toks[(i + 1).min(toks.len())..(i + 2).min(toks.len())],
                        i + 2,
                    )
                };
                let value = if is_defined {
                    inner.len() == 1 && self.macros.contains_key(&inner[0].text)
                } else {
                    match header_name(inner, &self.files) {
                        Some((name, angled)) => {
                            is_library_header(&name)
                                || self.resolve(t.span.file, &name, angled).is_some()
                        }
                        None => false,
                    }
                };
                pre.push(int_token(value as i64, t.span));
                i = next;
                continue;
            }
            pre.push(t.clone());
            i += 1;
        }
        let expanded = self.expand(pre);
        // Identifiers left after expansion evaluate as 0 (§19.1/11).
        let vals: Vec<ScToken> = expanded
            .into_iter()
            .map(|t| match t.kind {
                ScTokenKind::Ident | ScTokenKind::Keyword => {
                    int_token((t.text == "true") as i64, t.span)
                }
                _ => t,
            })
            .collect();
        let mut ev = CondEval {
            toks: &vals,
            pos: 0,
            err: None,
        };
        let v = ev.ternary();
        if ev.err.is_none() && ev.pos < vals.len() {
            ev.err = Some(format!(
                "unexpected '{}' in preprocessor expression",
                vals[ev.pos].text
            ));
        }
        if let Some(e) = ev.err {
            self.diags.push(ScDiagnostic::error(e, span));
            return false;
        }
        v != 0
    }
}

fn int_token(v: i64, span: ScSpan) -> ScToken {
    ScToken {
        kind: ScTokenKind::IntLit,
        text: v.to_string(),
        span,
        line_start: false,
        space_before: true,
    }
}

fn canonical(path: &str) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| PathBuf::from(path))
}

/// The tokens' spelling, single-spaced where the source had whitespace.
fn spell(toks: &[ScToken]) -> String {
    let mut s = String::new();
    for (n, t) in toks.iter().enumerate() {
        if n > 0 && t.space_before {
            s.push(' ');
        }
        s.push_str(&t.text);
    }
    s
}

fn quote(s: &str) -> String {
    let mut q = String::from("\"");
    for c in s.chars() {
        if c == '"' || c == '\\' {
            q.push('\\');
        }
        q.push(c);
    }
    q.push('"');
    q
}

/// `#arg`: the argument's spelling as a string literal (§19.3.2).
fn stringize(arg: &[PTok]) -> String {
    let mut s = String::from("\"");
    for (n, pt) in arg.iter().enumerate() {
        if n > 0 && pt.tok.space_before {
            s.push(' ');
        }
        let lit = matches!(pt.tok.kind, ScTokenKind::StringLit | ScTokenKind::CharLit);
        for c in pt.tok.text.chars() {
            if lit && (c == '"' || c == '\\') {
                s.push('\\');
            }
            s.push(c);
        }
    }
    s.push('"');
    s
}

/// The header an `#include` (or `__has_include`) names: `"x"` or `<x>`.
fn header_name(toks: &[ScToken], files: &[ScFile]) -> Option<(String, bool)> {
    let first = toks.first()?;
    if first.kind == ScTokenKind::StringLit && first.text.starts_with('"') && first.text.len() >= 2
    {
        return Some((first.text[1..first.text.len() - 1].to_string(), false));
    }
    if first.is_punct("<") {
        let close = toks.iter().position(|t| t.is_punct(">"))?;
        let last = &toks[close];
        // Spell the name from the source between the brackets when both
        // come from the same place, so `<tlm_utils/simple_target_socket.h>`
        // keeps its exact text; otherwise join the token spellings.
        if first.span.file == last.span.file
            && first.span.end <= last.span.start
            && let Some(f) = files.get(first.span.file as usize)
            && let Some(s) = f
                .text
                .get(first.span.end as usize..last.span.start as usize)
        {
            return Some((s.trim().to_string(), true));
        }
        let name: String = toks[1..close].iter().map(|t| t.text.as_str()).collect();
        return Some((name, true));
    }
    None
}

/// Collect the arguments of a function-like macro invocation from the
/// reversed work list, whose `(` was just taken. Returns the arguments
/// (split at top-level commas) and the span of the closing `)`.
fn collect_args(work: &mut Vec<PTok>) -> Option<(Vec<Vec<PTok>>, ScSpan)> {
    let mut args = vec![Vec::new()];
    let mut depth = 0usize;
    while let Some(pt) = work.pop() {
        if pt.tok.is_punct("(") {
            depth += 1;
        } else if pt.tok.is_punct(")") {
            if depth == 0 {
                return Some((args, pt.tok.span));
            }
            depth -= 1;
        } else if pt.tok.is_punct(",") && depth == 0 {
            args.push(Vec::new());
            continue;
        }
        args.last_mut().expect("never empty").push(pt);
    }
    None
}

/// Match the collected arguments to `n` parameters: `F()` is one empty
/// argument; a variadic macro gathers the extra arguments, commas included,
/// into its last one. `Err` carries the number of arguments given.
fn fit_args(mut args: Vec<Vec<PTok>>, n: usize, variadic: bool) -> Result<Vec<Vec<PTok>>, usize> {
    if n == 0 {
        return if args.len() == 1 && args[0].is_empty() {
            Ok(Vec::new())
        } else {
            Err(args.len())
        };
    }
    if variadic {
        if args.len() + 1 == n {
            args.push(Vec::new()); // empty variadic part
            return Ok(args);
        }
        if args.len() < n {
            return Err(args.len());
        }
        let extra: Vec<Vec<PTok>> = args.split_off(n - 1);
        let mut va = Vec::new();
        for (k, a) in extra.into_iter().enumerate() {
            if k > 0 {
                let span = a.first().map_or(ScSpan::default(), |p| p.tok.span);
                va.push(PTok {
                    tok: ScToken {
                        kind: ScTokenKind::Punct,
                        text: ",".to_string(),
                        span,
                        line_start: false,
                        space_before: false,
                    },
                    hide: Rc::new(BTreeSet::new()),
                });
            }
            va.extend(a);
        }
        args.push(va);
        return Ok(args);
    }
    if args.len() == n {
        Ok(args)
    } else {
        Err(args.len())
    }
}

/// Integer constant-expression evaluator for `#if` (§19.1).
struct CondEval<'a> {
    toks: &'a [ScToken],
    pos: usize,
    err: Option<String>,
}

impl CondEval<'_> {
    fn peek(&self) -> Option<&str> {
        self.toks
            .get(self.pos)
            .filter(|t| t.kind == ScTokenKind::Punct)
            .map(|t| t.text.as_str())
    }

    fn fail(&mut self, msg: String) -> i128 {
        if self.err.is_none() {
            self.err = Some(msg);
        }
        0
    }

    fn ternary(&mut self) -> i128 {
        let c = self.binary(0);
        if self.peek() == Some("?") {
            self.pos += 1;
            let a = self.ternary();
            if self.peek() != Some(":") {
                return self.fail("expected ':' in preprocessor expression".into());
            }
            self.pos += 1;
            let b = self.ternary();
            return if c != 0 { a } else { b };
        }
        c
    }

    fn binary(&mut self, min_prec: u8) -> i128 {
        let mut lhs = self.unary();
        while let Some(op) = self.peek() {
            let prec = match op {
                "||" => 1,
                "&&" => 2,
                "|" => 3,
                "^" => 4,
                "&" => 5,
                "==" | "!=" => 6,
                "<" | ">" | "<=" | ">=" => 7,
                "<<" | ">>" => 8,
                "+" | "-" => 9,
                "*" | "/" | "%" => 10,
                _ => break,
            };
            if prec <= min_prec {
                break;
            }
            let op = op.to_string();
            self.pos += 1;
            let rhs = self.binary(prec);
            lhs = match op.as_str() {
                "||" => ((lhs != 0) || (rhs != 0)) as i128,
                "&&" => ((lhs != 0) && (rhs != 0)) as i128,
                "|" => lhs | rhs,
                "^" => lhs ^ rhs,
                "&" => lhs & rhs,
                "==" => (lhs == rhs) as i128,
                "!=" => (lhs != rhs) as i128,
                "<" => (lhs < rhs) as i128,
                ">" => (lhs > rhs) as i128,
                "<=" => (lhs <= rhs) as i128,
                ">=" => (lhs >= rhs) as i128,
                "<<" => lhs.checked_shl(rhs.clamp(0, 127) as u32).unwrap_or(0),
                ">>" => lhs >> rhs.clamp(0, 127),
                "+" => lhs.wrapping_add(rhs),
                "-" => lhs.wrapping_sub(rhs),
                "*" => lhs.wrapping_mul(rhs),
                "/" | "%" if rhs == 0 => {
                    self.fail("division by zero in preprocessor expression".into())
                }
                "/" => lhs.wrapping_div(rhs),
                _ => lhs.wrapping_rem(rhs),
            };
        }
        lhs
    }

    fn unary(&mut self) -> i128 {
        let Some(t) = self.toks.get(self.pos) else {
            return self.fail("expected value in preprocessor expression".into());
        };
        self.pos += 1;
        match (t.kind, t.text.as_str()) {
            (ScTokenKind::Punct, "-") => self.unary().wrapping_neg(),
            (ScTokenKind::Punct, "+") => self.unary(),
            (ScTokenKind::Punct, "!") => (self.unary() == 0) as i128,
            (ScTokenKind::Punct, "~") => !self.unary(),
            (ScTokenKind::Punct, "(") => {
                let v = self.ternary();
                if self.peek() != Some(")") {
                    return self.fail("expected ')' in preprocessor expression".into());
                }
                self.pos += 1;
                v
            }
            (ScTokenKind::IntLit, s) => match parse_int(s) {
                Some(v) => v as i128,
                None => self.fail(format!(
                    "invalid integer '{}' in preprocessor expression",
                    s
                )),
            },
            (ScTokenKind::CharLit, s) => {
                let body = s.trim_start_matches(['L', 'u', 'U', '8']);
                let inner = body.trim_matches('\'');

                match inner.strip_prefix('\\') {
                    Some("n") => 10,
                    Some("t") => 9,
                    Some("0") => 0,
                    Some(c) => c.chars().next().map_or(0, |c| c as i128),
                    None => inner.chars().next().map_or(0, |c| c as i128),
                }
            }
            _ => {
                let text = t.text.clone();
                self.fail(format!("unexpected '{}' in preprocessor expression", text))
            }
        }
    }
}

/// The value of a C++ integer literal (any base, separators and suffixes
/// allowed); `None` when it does not fit in 64 bits or is malformed.
pub fn parse_int(text: &str) -> Option<u64> {
    let s: String = text.chars().filter(|&c| c != '\'').collect();
    let s = s.trim_end_matches(['u', 'U', 'l', 'L', 'z', 'Z']);
    let (digits, radix) = if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        (h, 16)
    } else if let Some(b) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
        (b, 2)
    } else if s.len() > 1 && s.starts_with('0') {
        (&s[1..], 8)
    } else {
        (s, 10)
    };
    u64::from_str_radix(digits, radix).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pp(src: &str) -> (String, Vec<ScDiagnostic>) {
        let mut p = Preprocessor::new(&[], &[]);
        let toks = p.run("<test>", src.to_string());
        let text: Vec<String> = toks.into_iter().map(|t| t.text).collect();
        (text.join(" "), p.diags)
    }

    #[test]
    fn object_and_function_macros() {
        let (s, d) =
            pp("#define W 8\n#define MAX(a,b) ((a) > (b) ? (a) : (b))\nint x = MAX(W, 3);");
        assert!(d.is_empty(), "{:?}", d);
        assert_eq!(s, "int x = ( ( 8 ) > ( 3 ) ? ( 8 ) : ( 3 ) ) ;");
    }

    #[test]
    fn stringize_paste_and_variadic() {
        let (s, d) = pp(
            "#define STR(x) #x\n#define CAT(a,b) a##b\n#define LOG(fmt, ...) printf(fmt, ## __VA_ARGS__)\n\
             STR(a + \"b\") CAT(sc_, uint) LOG(\"x\") LOG(\"y\", 1, 2)",
        );
        assert!(d.is_empty(), "{:?}", d);
        assert_eq!(
            s,
            r#""a + \"b\"" sc_uint printf ( "x" ) printf ( "y" , 1 , 2 )"#
        );
    }

    #[test]
    fn self_reference_does_not_loop() {
        let (s, _) = pp("#define foo foo + 1\n#define F(x) F(x) * 2\nfoo F(3)");
        assert_eq!(s, "foo + 1 F ( 3 ) * 2");
    }

    #[test]
    fn rescan_picks_up_following_parens() {
        let (s, _) = pp("#define G(x) x*2\n#define F G\nF(4)");
        assert_eq!(s, "4 * 2");
    }

    #[test]
    fn conditionals() {
        let (s, d) = pp(
            "#define A 3\n#if defined(A) && A > 2\nyes\n#elif 1\nno1\n#else\nno2\n#endif\n\
             #ifdef B\nno3\n#else\n#if __cplusplus >= 201103L\nok\n#endif\n#endif\n#ifndef A\nno4\n#endif",
        );
        assert!(d.is_empty(), "{:?}", d);
        assert_eq!(s, "yes ok");
    }

    #[test]
    fn errors_and_library_headers() {
        let (s, d) = pp(
            "#include <systemc>\n#include \"tlm_utils/simple_target_socket.h\"\n#error stop here\n#if 1\nx",
        );
        assert_eq!(s, "x");
        let msgs: Vec<_> = d.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(
            msgs,
            ["#error stop here", "unterminated conditional directive"]
        );
    }

    #[test]
    fn line_macro() {
        let (s, _) = pp("a\nb __LINE__");
        assert_eq!(s, "a b 2");
    }

    #[test]
    fn int_literals() {
        assert_eq!(parse_int("0x1F"), Some(31));
        assert_eq!(parse_int("0b1'0000"), Some(16));
        assert_eq!(parse_int("017"), Some(15));
        assert_eq!(parse_int("201703L"), Some(201703));
        assert_eq!(parse_int("0"), Some(0));
    }
}
