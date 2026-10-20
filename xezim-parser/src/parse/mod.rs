//! Recursive descent parser for SystemVerilog IEEE 1800-2017/2023.

mod declarations;
mod expressions;
mod helpers;
mod items;
mod lets;
mod statements;
mod types;

use crate::ast::decl::{ModuleItem, PackageItem};
use crate::ast::*;
use crate::diagnostics::Diagnostic;
use crate::lexer::token::{Token, TokenKind};
use items::ConstraintPos;

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    diagnostics: Vec<Diagnostic>,
    /// IEEE 1800-2017 §12.6: `.name` pattern bindings collected while parsing a
    /// pattern (`tagged X '{… , .v}` / `expr matches tagged a '{.v}`). The
    /// enclosing `if`/`case … matches` consumes these to synthesize local
    /// variable declarations so the binding is in scope in the matched
    /// statement. Drained at each consumption point.
    pending_pattern_bindings: Vec<Identifier>,
    /// Indices of the generate loops of the design element being parsed that
    /// do not declare `genvar` in their header.
    pub(super) plain_loop_vars: Vec<Identifier>,
    /// IEEE 1800-2017 §16.9: true while parsing a property/sequence body, so
    /// the keyword sequence operators `and`/`or` are recognised as binary SVA
    /// operators. Outside this context `or` stays an event-list separator
    /// (`@(a or b)`) and `and` a gate primitive, so the flag is essential.
    in_sva_seq: bool,
    /// The classes of this file so far, for the strict inheritance checks.
    pub(super) class_infos: Vec<ClassInfo>,
    /// `pure constraint` names of the class being parsed.
    pub(super) pure_constraints: Vec<String>,
    /// True while parsing the expression of a CONSTRAINT item, so the
    /// parenthesized-primary parser accepts the nonstandard-but-tolerated
    /// `( expr dist { ... } )` form (§18.5.4; a reference simulator warns
    /// `Illegal use of parenthesis around 'dist' constraint` and accepts it).
    pub(super) in_constraint: bool,
    /// The dist body captured by that paren form, handed back to
    /// `parse_constraint_item` once the enclosing expression finishes.
    pub(super) pending_paren_dist: Vec<(
        Vec<crate::ast::decl::ConstraintRange>,
        Vec<Option<crate::ast::decl::DistWeight>>,
    )>,
    /// Extra module items produced while parsing another one (a `specparam`
    /// inside a specify block), appended right after it by the item loops.
    pub(super) pending_module_items: Vec<ModuleItem>,
    /// Nesting depth of generate regions/blocks being parsed. A generate item
    /// is a `module_or_generate_item` (§A.1.4), which excludes `specparam`
    /// and module declarations.
    pub(super) generate_depth: u32,
    /// Port expressions of the non-ANSI port list just parsed (`.a(b[3:0])`,
    /// `{a, b}`, `a[7:0]`), by position in that list. The enclosing module
    /// declaration lowers them once its body is parsed.
    pub(super) port_exprs: Vec<(usize, crate::ast::expr::Expression)>,
    /// §11.13: the enclosing scopes and the lets each declares, innermost
    /// last (see `lets.rs`), and how many lets they hold in all.
    pub(super) let_scopes: Vec<lets::LetScope>,
    pub(super) let_live: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        crate::record_reference_census(&tokens);
        Self {
            tokens,
            pos: 0,
            diagnostics: Vec::new(),
            pending_pattern_bindings: Vec::new(),
            plain_loop_vars: Vec::new(),
            in_sva_seq: false,
            class_infos: Vec::new(),
            pure_constraints: Vec::new(),
            in_constraint: false,
            pending_paren_dist: Vec::new(),
            pending_module_items: Vec::new(),
            generate_depth: 0,
            port_exprs: Vec::new(),
            let_scopes: Vec::new(),
            let_live: 0,
        }
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity == crate::diagnostics::Severity::Error)
    }

    /// source_text ::= { description }
    pub fn parse_source_text(&mut self) -> SourceText {
        let start = self.current().span.start;
        let mut descriptions = Vec::new();
        while !self.at(TokenKind::Eof) {
            let before = self.pos;
            if let Some(desc) = self.parse_description() {
                descriptions.push(desc);
            } else if self.pos == before {
                // No progress AND nothing produced — genuinely stuck.
                self.error(format!("unexpected token: {:?}", self.current().text));
                self.bump();
            }
            // A None that advanced (e.g. a stray top-level `;` consumed by the
            // Semicolon arm) is a clean skip, not an error.
        }
        if crate::strict_checks() {
            self.check_pure_constraints();
        }
        SourceText {
            descriptions,
            span: self.span_from(start),
        }
    }

    /// §18.5.2: a non-virtual class implements every pure constraint it
    /// inherits. A chain through a class of another file is not followed.
    fn check_pure_constraints(&mut self) {
        let find = |n: &str| self.class_infos.iter().find(|c| c.name.name == n);
        let mut errs = Vec::new();
        for c in self
            .class_infos
            .iter()
            .filter(|c| !c.is_virtual && !c.is_interface)
        {
            let mut pure: Vec<&str> = Vec::new();
            let mut defined: Vec<&str> = c.constraints.iter().map(|s| s.as_str()).collect();
            let mut cur = c.bases.first().map(|b| b.0.as_str());
            let mut complete = true;
            for _ in 0..32 {
                let Some(b) = cur else { break };
                let Some(bi) = find(b) else {
                    complete = false;
                    break;
                };
                pure.extend(bi.pure_constraints.iter().map(|s| s.as_str()));
                defined.extend(bi.constraints.iter().map(|s| s.as_str()));
                cur = bi.bases.first().map(|b| b.0.as_str());
            }
            if complete && let Some(n) = pure.iter().find(|n| !defined.contains(n)) {
                errs.push(Diagnostic::error(
                    format!(
                        "class '{}' does not implement the inherited pure constraint '{n}' \
                         (IEEE 1800-2017 §18.5.2)",
                        c.name.name
                    ),
                    c.name.span,
                ));
            }
        }
        self.diagnostics.extend(errs);
    }

    /// Parse the simple `bind <target> <bind_mod> <inst>(<ports>);` form
    /// (IEEE 1800-2023 §23.11). The `bind` keyword must already have been
    /// consumed. Used at both compilation-unit scope (→ `Description::Bind`)
    /// and as a module item (→ `ModuleItem::Bind`). On a shape the heuristic
    /// doesn't handle (instance selector, multi-target, etc.) it rewinds and
    /// swallows to the next `;`, returning `None`.
    pub(super) fn try_bind_directive(&mut self) -> Option<crate::ast::decl::BindDirective> {
        let start_byte = self.current().span.start;
        let restart = self.pos;
        let target = self.parse_identifier();
        // §23.11 bind_target_instance: a dotted instance path selects ONE
        // instance instead of every instance of a module. The colon form
        // (`bind <mod> : <path> [, <path>]* <binder> ...`) lists explicit
        // target instances of that module.
        let mut target_path: Vec<crate::ast::Identifier> = Vec::new();
        let mut extra_paths: Vec<Vec<crate::ast::Identifier>> = Vec::new();
        if self.at(TokenKind::Dot) {
            target_path.push(target.clone());
            while self.eat(TokenKind::Dot).is_some() {
                target_path.push(self.parse_identifier());
            }
        } else if self.at(TokenKind::Colon) {
            self.bump();
            loop {
                let mut path: Vec<crate::ast::Identifier> = Vec::new();
                path.push(self.parse_identifier());
                while self.eat(TokenKind::Dot).is_some() {
                    path.push(self.parse_identifier());
                }
                if target_path.is_empty() {
                    target_path = path;
                } else {
                    extra_paths.push(path);
                }
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        let bind_mod = self.parse_identifier();
        // `bind dut harness #(.N(N)) v_h (.*);` — the parameter value
        // assignment used to make this routine give up, and the caller
        // turned the whole directive into a silent `Null` item: the harness
        // was never instantiated and every hierarchical call into it was a
        // no-op.
        let bind_params = self.parse_instantiation_params();
        if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
            let inst_start = self.current().span.start;
            let iname = self.parse_identifier();
            let dims = self.parse_unpacked_dimensions();
            let conns = self.parse_port_connections();
            if self.at(TokenKind::Semicolon) {
                self.bump();
                let span = self.span_from(start_byte);
                let instance = crate::ast::decl::HierarchicalInstance {
                    name: iname,
                    dimensions: dims,
                    connections: conns,
                    span: self.span_from(inst_start),
                };
                let instantiation = crate::ast::decl::ModuleInstantiation {
                    module_name: bind_mod,
                    params: bind_params,
                    instances: vec![instance],
                    span,
                };
                return Some(crate::ast::decl::BindDirective {
                    target_module: target,
                    target_path,
                    extra_paths,
                    instantiation,
                    span,
                });
            }
        }
        // Heuristic parse failed — rewind and swallow until the next ';'.
        self.pos = restart;
        let mut depth_paren = 0i32;
        while !self.at(TokenKind::Eof) {
            match self.current_kind() {
                TokenKind::LParen => {
                    depth_paren += 1;
                    self.bump();
                }
                TokenKind::RParen => {
                    depth_paren -= 1;
                    self.bump();
                }
                TokenKind::Semicolon if depth_paren <= 0 => {
                    self.bump();
                    break;
                }
                _ => {
                    self.bump();
                }
            }
        }
        None
    }

    fn parse_description(&mut self) -> Option<Description> {
        match self.current_kind() {
            // §23.5: `extern module <name> [#(params)] (ports);` — a PROTOTYPE
            // for a module defined elsewhere. The definition itself is what
            // gets elaborated; consume the prototype through its `;` and move
            // on. (Also covers `extern primitive` and `extern interface`.)
            TokenKind::KwExtern
                if matches!(
                    self.peek_kind(),
                    TokenKind::KwModule
                        | TokenKind::KwMacromodule
                        | TokenKind::KwPrimitive
                        | TokenKind::KwInterface
                ) =>
            {
                self.bump(); // extern
                self.bump(); // module/primitive/interface
                while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                self.expect(TokenKind::Semicolon);
                self.parse_description()
            }
            TokenKind::KwModule | TokenKind::KwMacromodule => {
                Some(Description::Module(self.parse_module_declaration()))
            }
            // IEEE 1800-2017 §8.26: `interface class …` is a class, not a
            // module-style interface — route it to the class parser.
            TokenKind::KwInterface if self.peek_kind() == TokenKind::KwClass => {
                Some(Description::Class(self.parse_class_declaration()))
            }
            TokenKind::KwInterface => {
                Some(Description::Interface(self.parse_interface_declaration()))
            }
            TokenKind::KwProgram => Some(Description::Program(self.parse_program_declaration())),
            // IEEE 1800-2017 §29 User-Defined Primitive. Parsed into a real
            // `Description::Udp` carrying the truth table; on any table-row it
            // cannot parse, `parse_primitive` emits a loud warning and falls
            // back to the historical empty-module stub for that UDP only.
            TokenKind::KwPrimitive => Some(self.parse_primitive()),
            TokenKind::KwPackage => Some(Description::Package(self.parse_package_declaration())),
            TokenKind::KwNettype => {
                if let Some(ModuleItem::NettypeDeclaration(n)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Nettype(n)))
                } else {
                    None
                }
            }
            TokenKind::KwClass => Some(Description::Class(self.parse_class_declaration())),
            // §19.3: a covergroup declared at file ($unit) scope.
            TokenKind::KwCovergroup => Some(Description::PackageItem(PackageItem::Covergroup(
                self.parse_covergroup_declaration(),
            ))),
            TokenKind::KwChecker => {
                if let Some(ModuleItem::CheckerDeclaration(c)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Checker(c)))
                } else {
                    None
                }
            }
            TokenKind::KwVirtual if self.peek_kind() == TokenKind::KwClass => {
                Some(Description::Class(self.parse_class_declaration()))
            }
            TokenKind::KwLet => {
                if let Some(ModuleItem::LetDeclaration(l)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Let(l)))
                } else {
                    None
                }
            }
            TokenKind::KwTypedef => {
                Some(Description::TypedefDecl(self.parse_typedef_declaration()))
            }
            // IEEE 1800-2017 §3.12 / §6.20: compilation-unit ($unit) scope
            // `parameter`/`localparam` declarations. Surface them as a
            // PackageItem::Parameter so elaboration can hoist them into every
            // module (like $unit functions/tasks). Without this the top-level
            // `parameter int N = 1;` form was an "unexpected token".
            TokenKind::KwParameter | TokenKind::KwLocalparam => Some(Description::PackageItem(
                PackageItem::Parameter(self.parse_parameter_decl_stmt()),
            )),
            TokenKind::KwImport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(Description::DPIImport(self.parse_dpi_import()))
                } else {
                    Some(Description::ImportDecl(self.parse_import_declaration()))
                }
            }
            TokenKind::KwExport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(Description::DPIExport(self.parse_dpi_export()))
                } else {
                    self.bump();
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
                    self.expect(TokenKind::Semicolon);
                    self.parse_description()
                }
            }
            TokenKind::KwExtern => {
                self.bump();
                self.parse_description()
            }
            TokenKind::KwBind => {
                // IEEE 1800-2023 §23.11: `bind <target> <bind_mod> <inst>(<ports>);`
                // at compilation-unit scope. Surface a BindDirective so
                // elaboration appends the bound instantiation to every instance
                // of <target>; unhandled selectors fall back to skip-parse.
                self.bump();
                match self.try_bind_directive() {
                    Some(b) => Some(Description::Bind(b)),
                    None => self.parse_description(),
                }
            }
            TokenKind::KwConstraint => {
                // §18.5.1 out-of-class constraint definition at $unit scope:
                // `constraint ClassName::name { ... }[;]`. Capture the
                // (class, constraint) pair so elaboration can satisfy the
                // class's `extern constraint name;`; the body is consumed.
                self.bump();
                let hid = self.parse_hierarchical_identifier();
                let (class_name, constraint_name) = if hid.path.len() >= 2 {
                    (
                        hid.path[hid.path.len() - 2].name.name.clone(),
                        hid.path[hid.path.len() - 1].name.name.clone(),
                    )
                } else {
                    (
                        String::new(),
                        hid.path
                            .last()
                            .map(|s| s.name.name.clone())
                            .unwrap_or_default(),
                    )
                };
                let mut items = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        items.push(self.parse_constraint_item(ConstraintPos::BlockItem));
                    }
                    self.expect(TokenKind::RBrace);
                }
                if self.at(TokenKind::Semicolon) {
                    self.bump();
                }
                if class_name.is_empty() {
                    self.parse_description()
                } else {
                    Some(Description::OutOfClassConstraint {
                        class_name,
                        constraint_name,
                        items,
                    })
                }
            }
            TokenKind::KwTimeunit | TokenKind::KwTimeprecision => Some(Description::TimeunitsDecl(
                self.parse_timeunits_declaration(),
            )),
            TokenKind::KwFunction => {
                Some(Description::PackageItem(self.parse_package_item().unwrap()))
            }
            TokenKind::KwTask => Some(Description::PackageItem(self.parse_package_item().unwrap())),
            TokenKind::Directive => {
                self.bump();
                self.parse_description()
            }
            // Stray top-level `;` — e.g. `endmodule;` (an empty
            // compilation-unit item, §A.1.2). Skip and continue.
            TokenKind::Semicolon => {
                self.bump();
                self.parse_description()
            }
            _ => {
                // Compilation-unit ($unit) scope data declaration like
                // `string label = "...";`. Surface it as a PackageItem::Data so
                // elaboration can hoist it into modules (and thus make it
                // visible to class methods that reference it — UVM code does
                // `string label = "X"; … \`uvm_info(label, …)`).
                //
                // Also accept a USER-DEFINED type (class/typedef name): at
                // $unit scope a leading Identifier is always a data
                // declaration (module instances cannot exist at $unit scope,
                // LRM §23.3), e.g. `rw_tr q[$];` or `pkg::T x;`. Without this
                // the guard only admitted builtin type keywords, leaving
                // `rw_tr q[$];` as an unexpected token.
                let is_user_type_decl = self.at(TokenKind::Identifier)
                    && matches!(
                        self.peek_kind(),
                        TokenKind::Identifier
                            | TokenKind::DoubleColon
                            | TokenKind::Hash
                            | TokenKind::LBracket
                    );
                // §A.2.1.3: a data_declaration may carry an explicit LIFETIME
                // (`static int n = 0;`). `parse_data_declaration` already eats
                // it, but this guard did not admit one, so a $unit-scope
                // `static`/`automatic` declaration — the usual way a testbench
                // keeps a shared failure counter — died as "unexpected token".
                if self.is_data_type_keyword()
                    || self.at(TokenKind::KwVar)
                    || self.at(TokenKind::KwConst)
                    || is_user_type_decl
                    || self.at(TokenKind::KwStatic)
                    || self.at(TokenKind::KwAutomatic)
                {
                    let before = self.pos;
                    let decl = self.parse_data_declaration();
                    // Guard against a parse that made no progress (avoid a
                    // hang): fall back to the brute-force skip.
                    if self.pos > before {
                        return Some(Description::PackageItem(PackageItem::Data(decl)));
                    }
                    let mut depth = 0i32;
                    while !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => {
                                depth += 1
                            }
                            TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket => {
                                depth -= 1
                            }
                            TokenKind::Semicolon if depth <= 0 => {
                                self.bump();
                                break;
                            }
                            _ => {}
                        }
                        self.bump();
                    }
                    return self.parse_description();
                }
                None
            }
        }
    }

    /// IEEE 1800-2017 §29 user-defined primitive. Produces a real
    /// `Description::Udp` with the parsed truth table. If the header or any
    /// table row cannot be understood, emits a loud multi-line warning and
    /// falls back to the historical empty-module stub for THIS udp only, so a
    /// malformed table never crashes the parse nor silently mis-simulates.
    fn parse_primitive(&mut self) -> Description {
        use crate::ast::decl::{UdpDecl, UdpOut, UdpSym, UdpTableRow};
        let start = self.current().span.start;
        self.bump(); // `primitive`
        let name = self.parse_identifier();

        // --- Header: collect port names (depth-1 identifiers, in order) and
        // detect an ANSI `output reg` (=> sequential). Works for ANSI and
        // non-ANSI headers alike since port names are always identifiers.
        let mut ports: Vec<crate::ast::Identifier> = Vec::new();
        let mut is_sequential = false;
        if self.eat(TokenKind::LParen).is_some() {
            let mut depth = 1i32;
            while depth > 0 && !self.at(TokenKind::Eof) {
                match self.current_kind() {
                    TokenKind::LParen => {
                        depth += 1;
                        self.bump();
                    }
                    TokenKind::RParen => {
                        depth -= 1;
                        self.bump();
                    }
                    TokenKind::KwReg if depth == 1 => {
                        is_sequential = true;
                        self.bump();
                    }
                    TokenKind::Identifier | TokenKind::EscapedIdentifier if depth == 1 => {
                        ports.push(self.parse_identifier());
                    }
                    _ => {
                        self.bump();
                    }
                }
            }
        }
        self.eat(TokenKind::Semicolon);

        // --- Body declarations up to `table`: pick up `reg` (=> sequential)
        // and `initial out = 1'bX;` (start state).
        let mut init: Option<char> = None;
        while !self.at(TokenKind::KwTable)
            && !self.at(TokenKind::KwEndprimitive)
            && !self.at(TokenKind::Eof)
        {
            match self.current_kind() {
                TokenKind::KwReg => {
                    is_sequential = true;
                    self.skip_udp_to_semi();
                }
                TokenKind::KwInitial => {
                    self.bump(); // `initial`
                    // out = <value> ;  — collect value tokens after `=`.
                    let mut seen_eq = false;
                    let mut val = String::new();
                    while !self.at(TokenKind::Semicolon)
                        && !self.at(TokenKind::Eof)
                        && !self.at(TokenKind::KwTable)
                    {
                        let k = self.current_kind();
                        if k == TokenKind::Assign || k == TokenKind::Eq {
                            seen_eq = true;
                        } else if seen_eq {
                            val.push_str(&self.current().text);
                        }
                        self.bump();
                    }
                    self.eat(TokenKind::Semicolon);
                    let low = val.to_ascii_lowercase();
                    init = Some(if low.contains('x') || low.contains('z') {
                        'x'
                    } else if low.ends_with('1') {
                        '1'
                    } else if low.ends_with('0') {
                        '0'
                    } else {
                        'x'
                    });
                }
                _ => {
                    self.skip_udp_to_semi();
                }
            }
        }

        // --- Table.
        let n_inputs = ports.len().saturating_sub(1);
        let mut rows: Vec<UdpTableRow> = Vec::new();
        let mut table_ok = true;
        let mut fail_detail = String::new();
        // Where the warning points: the row that failed, else the table.
        let mut fail_span = self.current().span;
        if self.eat(TokenKind::KwTable).is_some() {
            // Gather raw table tokens up to `endtable`.
            let mut toks: Vec<Token> = Vec::new();
            while !self.at(TokenKind::KwEndtable)
                && !self.at(TokenKind::Eof)
                && !self.at(TokenKind::KwEndprimitive)
            {
                toks.push(self.current().clone());
                self.bump();
            }
            self.eat(TokenKind::KwEndtable);
            // Split into rows on `;`.
            let mut row_start = 0usize;
            for i in 0..=toks.len() {
                let at_end = i == toks.len();
                if at_end || toks[i].kind == TokenKind::Semicolon {
                    let slice = &toks[row_start..i];
                    row_start = i + 1;
                    if slice.iter().all(|t| t.kind == TokenKind::Semicolon) || slice.is_empty() {
                        continue;
                    }
                    if crate::strict_checks()
                        && !ports.is_empty()
                        && let Some(msg) = Self::udp_row_shape_error(slice, n_inputs)
                    {
                        let span = Span::new(slice[0].span.start, slice[slice.len() - 1].span.end);
                        self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                            format!("in primitive '{}': {}", name.name, msg),
                            span,
                        ));
                    }
                    match Self::parse_udp_row(slice, n_inputs) {
                        Some(r) => rows.push(r),
                        None => {
                            table_ok = false;
                            let txt: String = slice
                                .iter()
                                .map(|t| t.text.clone())
                                .collect::<Vec<_>>()
                                .join(" ");
                            fail_detail = txt;
                            if let (Some(f), Some(l)) = (slice.first(), slice.last()) {
                                fail_span = Span::new(f.span.start, l.span.end);
                            }
                            break;
                        }
                    }
                }
            }
        } else {
            table_ok = false;
            fail_detail = "missing `table` … `endtable`".to_string();
        }

        // Consume `endprimitive` and optional `: label`.
        while !self.at(TokenKind::KwEndprimitive) && !self.at(TokenKind::Eof) {
            self.bump();
        }
        self.expect(TokenKind::KwEndprimitive);
        if self.eat(TokenKind::Colon).is_some() {
            let _ = self.parse_identifier();
        }

        let span = self.span_from(start);
        let _ = UdpOut::NoChange; // (variant use silence if unused paths)
        let _ = UdpSym::AnyQ;

        if table_ok && !rows.is_empty() {
            Description::Udp(UdpDecl {
                name,
                ports,
                is_sequential,
                init,
                rows,
                span,
            })
        } else {
            // FAIL LOUD: name exactly what could not be parsed and the
            // consequence, then fall back to an empty-module stub (output
            // net left undriven) for this UDP only. The driver prints parser
            // warnings with their source location.
            self.diagnostics
                .push(crate::diagnostics::Diagnostic::warning(
                    format!(
                        "UNSUPPORTED UDP TABLE in primitive '{}': could not parse the \
                         row `{}`; the primitive is treated as an EMPTY module, so every \
                         instance's output net is left undriven (IEEE 1800-2017 §29)",
                        name.name, fail_detail
                    ),
                    fail_span,
                ));
            Description::Module(crate::ast::module::ModuleDeclaration {
                attrs: Vec::new(),
                kind: crate::ast::module::ModuleKind::Module,
                lifetime: None,
                name,
                params: Vec::new(),
                ports: crate::ast::module::PortList::NonAnsi(ports),
                items: Vec::new(),
                endlabel: None,
                span,
            })
        }
    }

    /// Consume tokens up to and including the next `;` (UDP body decls).
    fn skip_udp_to_semi(&mut self) {
        while !self.at(TokenKind::Semicolon)
            && !self.at(TokenKind::Eof)
            && !self.at(TokenKind::KwTable)
            && !self.at(TokenKind::KwEndprimitive)
        {
            self.bump();
        }
        self.eat(TokenKind::Semicolon);
    }

    /// §29.3.6: a combinational table entry is `inputs : output`, a sequential
    /// one `inputs : state : output`, with one symbol per input and a single
    /// state and output symbol. Symbols are counted per character (the lexer
    /// may join adjacent ones into one token) and a parenthesized edge counts
    /// once.
    fn udp_row_shape_error(slice: &[Token], n_inputs: usize) -> Option<String> {
        let mut fields: Vec<usize> = vec![0];
        let mut in_edge = false;
        for t in slice {
            match t.kind {
                TokenKind::Colon if !in_edge => fields.push(0),
                TokenKind::LParen => {
                    in_edge = true;
                    *fields.last_mut().unwrap() += 1;
                }
                TokenKind::RParen => in_edge = false,
                _ if !in_edge => *fields.last_mut().unwrap() += t.text.chars().count(),
                _ => {}
            }
        }
        if !(2..=3).contains(&fields.len()) {
            return Some(format!(
                "a UDP table entry has two or three ':'-separated fields, found {} \
                 (IEEE 1800-2017 §29.3.6)",
                fields.len()
            ));
        }
        if fields[0] != n_inputs {
            return Some(format!(
                "UDP table entry has {} input symbol(s) but the primitive has {n_inputs} \
                 input(s) (IEEE 1800-2017 §29.3.6)",
                fields[0]
            ));
        }
        if fields[1..].iter().any(|&n| n != 1) {
            return Some(
                "the current-state and output fields of a UDP table entry take a single \
                 symbol (IEEE 1800-2017 §29.3.6)"
                    .to_string(),
            );
        }
        None
    }

    /// 1-based source line of the current token (best-effort).
    /// Parse one truth-table row from a raw token slice (columns are
    /// `:`-separated; combinational = 2 fields, sequential = 3). Returns
    /// `None` on any unrecognised symbol or shape so the caller can fall back.
    fn parse_udp_row(slice: &[Token], n_inputs: usize) -> Option<crate::ast::decl::UdpTableRow> {
        use crate::ast::decl::{UdpOut, UdpTableRow};
        // Split fields on `:`.
        let mut fields: Vec<&[Token]> = Vec::new();
        let mut fs = 0usize;
        for i in 0..=slice.len() {
            if i == slice.len() || slice[i].kind == TokenKind::Colon {
                fields.push(&slice[fs..i]);
                fs = i + 1;
            }
        }
        let (input_f, state_f, out_f) = match fields.len() {
            2 => (fields[0], None, fields[1]),
            3 => (fields[0], Some(fields[1]), fields[2]),
            _ => return None,
        };
        let inputs = Self::parse_udp_syms(input_f)?;
        if inputs.len() != n_inputs {
            return None;
        }
        let state = match state_f {
            Some(f) => {
                let mut s = Self::parse_udp_syms(f)?;
                if s.len() != 1 {
                    return None;
                }
                Some(s.remove(0))
            }
            None => None,
        };
        // Output field: single symbol 0/1/x, or `-` (sequential no-change).
        if out_f.len() != 1 {
            return None;
        }
        let output = match out_f[0].text.as_str() {
            "0" => UdpOut::Level('0'),
            "1" => UdpOut::Level('1'),
            "x" | "X" => UdpOut::Level('x'),
            "-" => UdpOut::NoChange,
            _ => return None,
        };
        let span = slice
            .first()
            .map(|t| t.span)
            .unwrap_or(crate::ast::Span::dummy());
        Some(UdpTableRow {
            inputs,
            state,
            output,
            span,
        })
    }

    /// Parse a sequence of input/state symbols from a token slice.
    fn parse_udp_syms(field: &[Token]) -> Option<Vec<crate::ast::decl::UdpSym>> {
        use crate::ast::decl::UdpSym;
        let mut out = Vec::new();
        let mut i = 0usize;
        while i < field.len() {
            let t = &field[i];
            match t.kind {
                TokenKind::LParen => {
                    // Edge `(vw)` — concatenate token text until `)`.
                    let mut j = i + 1;
                    let mut txt = String::new();
                    while j < field.len() && field[j].kind != TokenKind::RParen {
                        txt.push_str(&field[j].text);
                        j += 1;
                    }
                    if j >= field.len() {
                        return None;
                    } // unmatched `(`
                    i = j + 1;
                    let chars: Vec<char> = txt.chars().filter(|c| !c.is_whitespace()).collect();
                    if chars.len() != 2 {
                        return None;
                    }
                    let from = Self::udp_norm_level(chars[0])?;
                    let to = Self::udp_norm_level(chars[1])?;
                    out.push(UdpSym::Edge { from, to });
                }
                _ => {
                    let sym = match t.text.as_str() {
                        "0" => UdpSym::Level('0'),
                        "1" => UdpSym::Level('1'),
                        "x" | "X" => UdpSym::Level('x'),
                        "z" | "Z" => UdpSym::Level('x'), // input z ⇒ x
                        "?" => UdpSym::AnyQ,
                        "b" | "B" => UdpSym::B,
                        "r" | "R" => UdpSym::EdgeShort('r'),
                        "f" | "F" => UdpSym::EdgeShort('f'),
                        "p" | "P" => UdpSym::EdgeShort('p'),
                        "n" | "N" => UdpSym::EdgeShort('n'),
                        "*" => UdpSym::EdgeShort('*'),
                        _ => return None,
                    };
                    out.push(sym);
                    i += 1;
                }
            }
        }
        Some(out)
    }

    fn udp_norm_level(c: char) -> Option<char> {
        match c {
            '0' => Some('0'),
            '1' => Some('1'),
            'x' | 'X' => Some('x'),
            'z' | 'Z' => Some('x'),
            '?' => Some('?'),
            _ => None,
        }
    }
}

/// What the strict inheritance checks need to know about one class.
pub(super) struct ClassInfo {
    pub name: Identifier,
    pub is_virtual: bool,
    pub is_interface: bool,
    /// Base classes with the text of their parameter value lists.
    pub bases: Vec<(String, String)>,
    /// Parameter and typedef names the class declares.
    pub type_names: Vec<String>,
    pub pure_constraints: Vec<String>,
    pub constraints: Vec<String>,
}
