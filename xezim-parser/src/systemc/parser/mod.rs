//! Recursive-descent parser for the SystemC front end.
//!
//! C++ cannot be parsed without knowing which names are types and which
//! are templates. The parser approximates that with two name sets, seeded
//! with the SystemC, TLM-2.0 and standard-library names a design uses and
//! grown with every class, enum, typedef and template the source declares.
//! Where the sets cannot decide, the parser tries one reading and backs
//! up ([`Parser::checkpoint`]/[`Parser::restore`]).

mod decl;
mod expr;
mod stmt;

use std::collections::BTreeSet;

use super::ScDiagnostic;
use super::ast::*;
use super::token::{ScSpan, ScToken, ScTokenKind};

/// A parse failure whose diagnostic has already been recorded; the caller
/// recovers at the next declaration or statement boundary.
#[derive(Debug)]
pub struct Fail;

pub type PResult<T> = Result<T, Fail>;

#[derive(Clone, Copy)]
pub(crate) struct Checkpoint {
    pos: usize,
    diags: usize,
    splits: usize,
}

/// Class templates of the SystemC, TLM-2.0 and C++ standard libraries.
/// Each is also a type name.
const LIBRARY_CLASS_TEMPLATES: &[&str] = &[
    // SystemC (IEEE 1666-2023 §5–§8)
    "sc_in",
    "sc_out",
    "sc_inout",
    "sc_signal",
    "sc_signal_in_if",
    "sc_signal_out_if",
    "sc_signal_inout_if",
    "sc_signal_write_if",
    "sc_buffer",
    "sc_fifo",
    "sc_fifo_in",
    "sc_fifo_out",
    "sc_fifo_in_if",
    "sc_fifo_out_if",
    "sc_fifo_blocking_in_if",
    "sc_fifo_nonblocking_in_if",
    "sc_port",
    "sc_export",
    "sc_vector",
    "sc_vector_assembly",
    "sc_int",
    "sc_uint",
    "sc_bigint",
    "sc_biguint",
    "sc_bv",
    "sc_lv",
    "sc_fixed",
    "sc_ufixed",
    "sc_fixed_fast",
    "sc_ufixed_fast",
    "sc_in_rv",
    "sc_out_rv",
    "sc_inout_rv",
    "sc_signal_rv",
    "sc_attribute",
    // TLM-2.0 (§10–§17)
    "tlm_initiator_socket",
    "tlm_target_socket",
    "tlm_base_initiator_socket",
    "tlm_base_target_socket",
    "tlm_base_initiator_socket_b",
    "tlm_base_target_socket_b",
    "tlm_fw_transport_if",
    "tlm_bw_transport_if",
    "tlm_fw_nonblocking_transport_if",
    "tlm_bw_nonblocking_transport_if",
    "tlm_blocking_transport_if",
    "tlm_fw_direct_mem_if",
    "tlm_transport_dbg_if",
    "tlm_fifo",
    "tlm_analysis_port",
    "tlm_analysis_fifo",
    "tlm_analysis_if",
    "tlm_put_if",
    "tlm_get_if",
    "tlm_peek_if",
    "tlm_blocking_put_if",
    "tlm_blocking_get_if",
    "tlm_blocking_peek_if",
    "tlm_nonblocking_put_if",
    "tlm_nonblocking_get_if",
    "tlm_nonblocking_peek_if",
    "tlm_get_peek_if",
    "tlm_transport_if",
    "tlm_extension",
    "tlm_req_rsp_channel",
    "tlm_transport_channel",
    "tlm_master_if",
    "tlm_slave_if",
    "simple_initiator_socket",
    "simple_target_socket",
    "simple_initiator_socket_tagged",
    "simple_target_socket_tagged",
    "passthrough_target_socket",
    "passthrough_target_socket_tagged",
    "multi_passthrough_initiator_socket",
    "multi_passthrough_target_socket",
    "peq_with_get",
    "peq_with_cb_and_phase",
    "instance_specific_extension",
    // C++ standard library
    "vector",
    "map",
    "multimap",
    "unordered_map",
    "set",
    "multiset",
    "unordered_set",
    "deque",
    "list",
    "forward_list",
    "array",
    "pair",
    "tuple",
    "unique_ptr",
    "shared_ptr",
    "weak_ptr",
    "function",
    "optional",
    "variant",
    "queue",
    "stack",
    "priority_queue",
    "initializer_list",
    "atomic",
    "numeric_limits",
    "basic_string",
    "basic_ostream",
    "basic_istream",
    "hash",
    "less",
    "greater",
    "equal_to",
    "bitset",
    "complex",
    "enable_if",
    "enable_if_t",
    "conditional",
    "conditional_t",
    "is_same",
    "remove_reference",
    "decay",
    "decay_t",
    "underlying_type",
    "underlying_type_t",
    "integral_constant",
    "lock_guard",
    "unique_lock",
    "reference_wrapper",
];

/// Function templates commonly called with explicit template arguments.
const LIBRARY_FUNCTION_TEMPLATES: &[&str] = &[
    "make_unique",
    "make_shared",
    "static_pointer_cast",
    "dynamic_pointer_cast",
    "const_pointer_cast",
    "get",
    "get_if",
    "holds_alternative",
    "declval",
    "forward",
    "move",
    "sc_spawn",
    "sc_bind",
    "DCAST",
    "is_same_v",
    "is_integral_v",
    "is_signed_v",
];

/// Non-template types of the SystemC, TLM-2.0 and C++ standard libraries.
const LIBRARY_TYPES: &[&str] = &[
    // SystemC
    "sc_module",
    "sc_module_name",
    "sc_object",
    "sc_time",
    "sc_time_unit",
    "sc_event",
    "sc_event_or_list",
    "sc_event_and_list",
    "sc_event_finder",
    "sc_clock",
    "sc_in_clk",
    "sc_out_clk",
    "sc_inout_clk",
    "sc_in_resolved",
    "sc_out_resolved",
    "sc_inout_resolved",
    "sc_signal_resolved",
    "sc_logic",
    "sc_logic_value_t",
    "sc_bit",
    "sc_int_base",
    "sc_uint_base",
    "sc_signed",
    "sc_unsigned",
    "sc_bv_base",
    "sc_lv_base",
    "sc_fix",
    "sc_ufix",
    "sc_fxval",
    "sc_fxnum",
    "sc_mutex",
    "sc_semaphore",
    "sc_process_handle",
    "sc_spawn_options",
    "sc_trace_file",
    "sc_report",
    "sc_actions",
    "sc_severity",
    "sc_verbosity",
    "sc_interface",
    "sc_prim_channel",
    "sc_channel",
    "sc_behavior",
    "sc_sensitive",
    "sc_length_context",
    "sc_simcontext",
    "sc_attr_base",
    "sc_port_base",
    "sc_export_base",
    "sc_vector_base",
    "sc_status",
    "sc_stop_mode",
    "sc_starvation_policy",
    "sc_unwind_exception",
    "sc_writer_policy",
    "sc_port_policy",
    "sc_string",
    "int64",
    "uint64",
    "sc_dt",
    "sc_q_mode",
    "sc_o_mode",
    "sc_numrep",
    // TLM-2.0
    "tlm_generic_payload",
    "tlm_phase",
    "tlm_phase_enum",
    "tlm_sync_enum",
    "tlm_command",
    "tlm_response_status",
    "tlm_gp_option",
    "tlm_byte_enable_mask",
    "tlm_dmi",
    "tlm_extension_base",
    "tlm_mm_interface",
    "tlm_global_quantum",
    "tlm_quantumkeeper",
    "tlm_endianness",
    "tlm_base_protocol_types",
    "tlm_bw_direct_mem_if",
    // C++ standard library
    "string",
    "string_view",
    "ostream",
    "istream",
    "iostream",
    "ostringstream",
    "istringstream",
    "stringstream",
    "ofstream",
    "ifstream",
    "fstream",
    "size_t",
    "ssize_t",
    "ptrdiff_t",
    "uint8_t",
    "uint16_t",
    "uint32_t",
    "uint64_t",
    "int8_t",
    "int16_t",
    "int32_t",
    "int64_t",
    "uintptr_t",
    "intptr_t",
    "uint_fast8_t",
    "uint_least8_t",
    "FILE",
    "nullptr_t",
    "mutex",
    "thread",
    "exception",
    "runtime_error",
    "logic_error",
    "out_of_range",
    "invalid_argument",
    "type_info",
    "byte",
    "streamsize",
    "ios_base",
    "va_list",
    "time_t",
    "clock_t",
];

pub struct Parser {
    toks: Vec<ScToken>,
    pos: usize,
    pub diags: Vec<ScDiagnostic>,
    /// `>>`-family tokens split into `>` + rest while closing template
    /// argument lists: (index of the first half, original token), undone by
    /// [`Parser::restore`].
    splits: Vec<(usize, ScToken)>,
    type_names: BTreeSet<String>,
    class_templates: BTreeSet<String>,
    fn_templates: BTreeSet<String>,
    /// Nonzero while parsing a template argument at bracket depth zero: a
    /// `>` there closes the argument list instead of comparing.
    no_gt: usize,
    /// The declaration being parsed follows a `template<…>` header, so the
    /// class or function it declares is a template name.
    pending_template: bool,
    /// Names of the classes whose bodies are being parsed, innermost last.
    class_stack: Vec<String>,
}

impl Parser {
    pub fn new(mut toks: Vec<ScToken>) -> Self {
        let end = toks.last().map_or(ScSpan::default(), |t| ScSpan {
            file: t.span.file,
            start: t.span.end,
            end: t.span.end,
        });
        toks.push(ScToken {
            kind: ScTokenKind::Eof,
            text: String::new(),
            span: end,
            line_start: true,
            space_before: true,
        });
        let set = |names: &[&str]| names.iter().map(|s| s.to_string()).collect::<BTreeSet<_>>();
        Parser {
            toks,
            pos: 0,
            diags: Vec::new(),
            splits: Vec::new(),
            type_names: set(LIBRARY_TYPES),
            class_templates: set(LIBRARY_CLASS_TEMPLATES),
            fn_templates: set(LIBRARY_FUNCTION_TEMPLATES),
            no_gt: 0,
            pending_template: false,
            class_stack: Vec::new(),
        }
    }

    pub fn parse_translation_unit(&mut self) -> TranslationUnit {
        let items = self.parse_items(false);
        let mut unit = TranslationUnit { items };
        mark_derived_modules(&mut unit);
        unit
    }

    // ---- token access ---------------------------------------------------

    fn peek(&self) -> &ScToken {
        &self.toks[self.pos]
    }

    fn nth(&self, n: usize) -> &ScToken {
        &self.toks[(self.pos + n).min(self.toks.len() - 1)]
    }

    fn at_eof(&self) -> bool {
        self.peek().kind == ScTokenKind::Eof
    }

    fn bump(&mut self) -> ScToken {
        let t = self.toks[self.pos].clone();
        if t.kind != ScTokenKind::Eof {
            self.pos += 1;
        }
        t
    }

    fn at(&self, p: &str) -> bool {
        self.peek().is_punct(p)
    }

    fn at_kw(&self, k: &str) -> bool {
        self.peek().is_keyword(k)
    }

    fn at_ident(&self) -> bool {
        self.peek().kind == ScTokenKind::Ident
    }

    fn eat(&mut self, p: &str) -> bool {
        if self.at(p) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, k: &str) -> bool {
        if self.at_kw(k) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// A contextual keyword (`override`, `final`) — an identifier elsewhere.
    fn eat_contextual(&mut self, word: &str) -> bool {
        if self.peek().is_ident(word) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, p: &str) -> PResult<ScSpan> {
        if self.at(p) {
            Ok(self.bump().span)
        } else {
            Err(self.err_expected(&format!("'{}'", p)))
        }
    }

    fn expect_ident(&mut self) -> PResult<Ident> {
        if self.at_ident() {
            let t = self.bump();
            Ok(Ident {
                name: t.text,
                span: t.span,
            })
        } else {
            Err(self.err_expected("identifier"))
        }
    }

    fn error(&mut self, msg: impl Into<String>, span: ScSpan) -> Fail {
        self.diags.push(ScDiagnostic::error(msg, span));
        Fail
    }

    fn err_expected(&mut self, what: &str) -> Fail {
        let t = self.peek();
        let found = if t.kind == ScTokenKind::Eof {
            "end of input".to_string()
        } else {
            format!("'{}'", t.text)
        };
        let span = t.span;
        self.error(format!("expected {}, found {}", what, found), span)
    }

    fn cur_span(&self) -> ScSpan {
        self.peek().span
    }

    fn prev_span(&self) -> ScSpan {
        self.toks[self.pos.saturating_sub(1)].span
    }

    /// From `start` to the end of the last consumed token.
    fn span_from(&self, start: ScSpan) -> ScSpan {
        if self.pos == 0 {
            return start;
        }
        start.to(self.prev_span())
    }

    fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            pos: self.pos,
            diags: self.diags.len(),
            splits: self.splits.len(),
        }
    }

    fn restore(&mut self, cp: Checkpoint) {
        while self.splits.len() > cp.splits {
            let (i, orig) = self.splits.pop().expect("len checked");
            self.toks[i] = orig;
            self.toks.remove(i + 1);
        }
        self.pos = cp.pos;
        self.diags.truncate(cp.diags);
    }

    /// Consume a `>` closing a template argument list, splitting `>>`,
    /// `>=` or `>>=` when the list ends inside one (§13.2/3).
    fn expect_template_close(&mut self) -> PResult<()> {
        let t = self.peek().clone();
        if t.is_punct(">") {
            self.pos += 1;
            return Ok(());
        }
        if t.kind == ScTokenKind::Punct && t.text.len() > 1 && t.text.starts_with('>') {
            let first = ScToken {
                text: ">".to_string(),
                span: ScSpan {
                    end: t.span.start + 1,
                    ..t.span
                },
                ..t.clone()
            };
            let rest = ScToken {
                text: t.text[1..].to_string(),
                span: ScSpan {
                    start: t.span.start + 1,
                    ..t.span
                },
                line_start: false,
                space_before: false,
                ..t.clone()
            };
            self.toks[self.pos] = first;
            self.toks.insert(self.pos + 1, rest);
            self.splits.push((self.pos, t));
            self.pos += 1;
            return Ok(());
        }
        Err(self.err_expected("'>'"))
    }

    /// Skip to the end of the current declaration or statement after an
    /// error: past a `;` or a balanced `{…}` at depth zero, or up to a `}`
    /// that closes the enclosing scope. Always makes progress unless at a
    /// closing brace or the end of input.
    fn recover(&mut self) {
        let start = self.pos;
        let mut depth = 0usize;
        loop {
            let t = self.peek();
            if t.kind == ScTokenKind::Eof {
                break;
            }
            if t.kind == ScTokenKind::Punct {
                match t.text.as_str() {
                    "{" | "(" | "[" => depth += 1,
                    ")" | "]" => depth = depth.saturating_sub(1),
                    "}" => {
                        if depth == 0 {
                            break;
                        }
                        depth -= 1;
                        if depth == 0 {
                            self.pos += 1;
                            self.eat(";");
                            break;
                        }
                    }
                    ";" if depth == 0 => {
                        self.pos += 1;
                        break;
                    }
                    _ => {}
                }
            }
            self.pos += 1;
        }
        if self.pos == start && !self.at("}") {
            self.bump();
        }
    }

    // ---- name knowledge -------------------------------------------------

    fn is_template_name(&self, name: &str) -> bool {
        self.class_templates.contains(name) || self.fn_templates.contains(name)
    }

    fn is_type_name(&self, name: &str) -> bool {
        self.type_names.contains(name) || self.class_templates.contains(name)
    }

    fn add_type_name(&mut self, name: &str) {
        self.type_names.insert(name.to_string());
    }

    /// Whether `q` names a type as far as the parser knows.
    fn names_type(&self, q: &QualifiedName) -> bool {
        self.is_type_name(q.last_name())
    }

    /// The source spelling of tokens `from..self.pos`, single-spaced where
    /// the source had whitespace.
    fn spell_from(&self, from: usize) -> String {
        let mut s = String::new();
        for (n, t) in self.toks[from..self.pos].iter().enumerate() {
            if n > 0 && t.space_before {
                s.push(' ');
            }
            s.push_str(&t.text);
        }
        s
    }
}

/// Mark every class deriving (directly or through other classes of the
/// unit) from a module class as a module itself (IEEE 1666-2023 §5.2.1).
fn mark_derived_modules(unit: &mut TranslationUnit) {
    loop {
        let mut modules = BTreeSet::new();
        for_each_class(&unit.items, &mut |c| {
            if c.sc_module
                && let Some(n) = c.name_str()
            {
                modules.insert(n.to_string());
            }
        });
        let mut changed = false;
        for_each_class_mut(&mut unit.items, &mut |c| {
            if !c.sc_module && c.bases.iter().any(|b| modules.contains(b.name.last_name())) {
                c.sc_module = true;
                changed = true;
            }
        });
        if !changed {
            break;
        }
    }
}

pub(crate) fn for_each_class<'a>(items: &'a [Item], f: &mut impl FnMut(&'a ClassDecl)) {
    fn member<'a>(m: &'a Member, f: &mut impl FnMut(&'a ClassDecl)) {
        match m {
            Member::NestedClass(c) => class(c, f),
            Member::Template { member: inner, .. } => member(inner, f),
            _ => {}
        }
    }
    fn class<'a>(c: &'a ClassDecl, f: &mut impl FnMut(&'a ClassDecl)) {
        f(c);
        for m in &c.members {
            member(m, f);
        }
    }
    fn item<'a>(i: &'a Item, f: &mut impl FnMut(&'a ClassDecl)) {
        match i {
            Item::Class(c) => class(c, f),
            Item::Namespace { items, .. } | Item::ExternBlock { items, .. } => {
                for i in items {
                    item(i, f);
                }
            }
            Item::Template { item: inner, .. } => item(inner, f),
            _ => {}
        }
    }
    for i in items {
        item(i, f);
    }
}

fn for_each_class_mut(items: &mut [Item], f: &mut impl FnMut(&mut ClassDecl)) {
    fn member(m: &mut Member, f: &mut impl FnMut(&mut ClassDecl)) {
        match m {
            Member::NestedClass(c) => class(c, f),
            Member::Template { member: inner, .. } => member(inner, f),
            _ => {}
        }
    }
    fn class(c: &mut ClassDecl, f: &mut impl FnMut(&mut ClassDecl)) {
        f(c);
        for m in &mut c.members {
            member(m, f);
        }
    }
    fn item(i: &mut Item, f: &mut impl FnMut(&mut ClassDecl)) {
        match i {
            Item::Class(c) => class(c, f),
            Item::Namespace { items, .. } | Item::ExternBlock { items, .. } => {
                for i in items {
                    item(i, f);
                }
            }
            Item::Template { item: inner, .. } => item(inner, f),
            _ => {}
        }
    }
    for i in items {
        item(i, f);
    }
}
