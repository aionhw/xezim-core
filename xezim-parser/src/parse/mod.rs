//! Recursive descent parser for SystemVerilog IEEE 1800-2017/2023.

mod helpers;
mod types;
mod expressions;
mod statements;
mod declarations;
mod items;

use crate::ast::*;
use crate::ast::decl::{ModuleItem, PackageItem};
use crate::lexer::token::{Token, TokenKind};
use crate::diagnostics::Diagnostic;

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
    /// IEEE 1800-2017 §16.9: true while parsing a property/sequence body, so
    /// the keyword sequence operators `and`/`or` are recognised as binary SVA
    /// operators. Outside this context `or` stays an event-list separator
    /// (`@(a or b)`) and `and` a gate primitive, so the flag is essential.
    in_sva_seq: bool,
    /// True while parsing the expression of a CONSTRAINT item, so the
    /// parenthesized-primary parser accepts the nonstandard-but-tolerated
    /// `( expr dist { ... } )` form (§18.5.4; a reference simulator warns
    /// `Illegal use of parenthesis around 'dist' constraint` and accepts it).
    pub(super) in_constraint: bool,
    /// The dist body captured by that paren form, handed back to
    /// `parse_constraint_item` once the enclosing expression finishes.
    pub(super) pending_paren_dist:
        Vec<(Vec<crate::ast::decl::ConstraintRange>, Vec<Option<crate::ast::decl::DistWeight>>)>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0, diagnostics: Vec::new(),
               pending_pattern_bindings: Vec::new(),
               in_sva_seq: false,
               in_constraint: false,
               pending_paren_dist: Vec::new() }
    }

    pub fn diagnostics(&self) -> &[Diagnostic] { &self.diagnostics }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == crate::diagnostics::Severity::Error)
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
        SourceText { descriptions, span: self.span_from(start) }
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
                    params: None,
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
                TokenKind::LParen => { depth_paren += 1; self.bump(); }
                TokenKind::RParen => { depth_paren -= 1; self.bump(); }
                TokenKind::Semicolon if depth_paren <= 0 => { self.bump(); break; }
                _ => { self.bump(); }
            }
        }
        None
    }

    /// AMS §3.4 `nature <name> [: <parent>] ; <attr> = <expr>; … endnature`.
    /// `nature` is only a keyword under `--ams`, so this is unreachable
    /// otherwise.
    fn parse_nature_declaration(&mut self) -> crate::ast::decl::NatureDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwNature);
        let name = self.parse_identifier();
        // `nature derived : base;` — a nature refining another.
        let parent = if self.eat(TokenKind::Colon).is_some() {
            Some(self.parse_identifier())
        } else {
            None
        };
        let _ = self.eat(TokenKind::Semicolon);
        let mut attributes = Vec::new();
        while !self.at(TokenKind::KwEndnature) && !self.at(TokenKind::Eof) {
            // `<attr> = <expr> ;`. Attribute names are NOT reserved words, so
            // they arrive as identifiers; anything else in the body is skipped
            // to the next `;` rather than failing the file, keeping the parser
            // permissive on the standard's open attribute set.
            if !self.at(TokenKind::Identifier) {
                self.bump();
                continue;
            }
            let attr = self.parse_identifier();
            if self.eat(TokenKind::Assign).is_none() {
                while !self.at(TokenKind::Semicolon)
                    && !self.at(TokenKind::KwEndnature)
                    && !self.at(TokenKind::Eof)
                {
                    self.bump();
                }
                let _ = self.eat(TokenKind::Semicolon);
                continue;
            }
            let value = self.parse_expression();
            let _ = self.eat(TokenKind::Semicolon);
            attributes.push((attr, value));
        }
        self.expect(TokenKind::KwEndnature);
        crate::ast::decl::NatureDeclaration { name, parent, attributes, span: self.span_from(start) }
    }

    /// AMS §3.5 `discipline <name>; [potential N;] [flow N;] [domain D;]
    /// enddiscipline`.
    fn parse_discipline_declaration(&mut self) -> crate::ast::decl::DisciplineDeclaration {
        use crate::ast::decl::DisciplineDomain;
        let start = self.current().span.start;
        self.expect(TokenKind::KwDiscipline);
        let name = self.parse_identifier();
        let _ = self.eat(TokenKind::Semicolon);
        let mut potential = None;
        let mut flow = None;
        let mut domain = None;
        while !self.at(TokenKind::KwEnddiscipline) && !self.at(TokenKind::Eof) {
            match self.current_kind() {
                TokenKind::KwPotential => {
                    self.bump();
                    potential = Some(self.parse_identifier());
                    let _ = self.eat(TokenKind::Semicolon);
                }
                TokenKind::KwFlow => {
                    self.bump();
                    flow = Some(self.parse_identifier());
                    let _ = self.eat(TokenKind::Semicolon);
                }
                TokenKind::KwDomain => {
                    self.bump();
                    domain = match self.current_kind() {
                        TokenKind::KwContinuous => { self.bump(); Some(DisciplineDomain::Continuous) }
                        TokenKind::KwDiscrete => { self.bump(); Some(DisciplineDomain::Discrete) }
                        _ => {
                            self.error("expected `continuous` or `discrete` after `domain` (Verilog-AMS 2.4.0 3.5)");
                            None
                        }
                    };
                    let _ = self.eat(TokenKind::Semicolon);
                }
                // Anything else in the body (binding an attribute override,
                // a vendor extension): skip to the next `;` and keep going.
                _ => {
                    while !self.at(TokenKind::Semicolon)
                        && !self.at(TokenKind::KwEnddiscipline)
                        && !self.at(TokenKind::Eof)
                    {
                        self.bump();
                    }
                    let _ = self.eat(TokenKind::Semicolon);
                }
            }
        }
        self.expect(TokenKind::KwEnddiscipline);
        crate::ast::decl::DisciplineDeclaration { name, potential, flow, domain, span: self.span_from(start) }
    }

    fn parse_description(&mut self) -> Option<Description> {
        match self.current_kind() {
            // Verilog-AMS §3.4 / §3.5. These token kinds only exist under
            // `--ams`; the words lex as ordinary identifiers otherwise.
            TokenKind::KwNature => {
                return Some(Description::Nature(self.parse_nature_declaration()));
            }
            TokenKind::KwDiscipline => {
                return Some(Description::Discipline(self.parse_discipline_declaration()));
            }
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
            TokenKind::KwModule | TokenKind::KwMacromodule =>
                Some(Description::Module(self.parse_module_declaration())),
            // IEEE 1800-2017 §8.26: `interface class …` is a class, not a
            // module-style interface — route it to the class parser.
            TokenKind::KwInterface if self.peek_kind() == TokenKind::KwClass =>
                Some(Description::Class(self.parse_class_declaration())),
            TokenKind::KwInterface =>
                Some(Description::Interface(self.parse_interface_declaration())),
            TokenKind::KwProgram =>
                Some(Description::Program(self.parse_program_declaration())),
            // IEEE 1800-2017 §29 User-Defined Primitive. Parsed into a real
            // `Description::Udp` carrying the truth table; on any table-row it
            // cannot parse, `parse_primitive` emits a loud warning and falls
            // back to the historical empty-module stub for that UDP only.
            TokenKind::KwPrimitive => Some(self.parse_primitive()),
            TokenKind::KwPackage =>
                Some(Description::Package(self.parse_package_declaration())),
            TokenKind::KwNettype => {
                if let Some(ModuleItem::NettypeDeclaration(n)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Nettype(n)))
                } else { None }
            }
            TokenKind::KwClass =>
                Some(Description::Class(self.parse_class_declaration())),
            // IEEE 1800-2023 §19: a top-level (\$unit-scope) covergroup is
            // legal. We parse it for syntax acceptance but don't surface it
            // as a Description (no covergroup runtime hosted outside a
            // class/module). The body is fully consumed up through
            // `endgroup` plus optional label.
            TokenKind::KwCovergroup => {
                let _ = self.parse_covergroup_declaration();
                self.parse_description()
            }
            TokenKind::KwChecker => {
                if let Some(ModuleItem::CheckerDeclaration(c)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Checker(c)))
                } else { None }
            }
            TokenKind::KwVirtual if self.peek_kind() == TokenKind::KwClass =>
                Some(Description::Class(self.parse_class_declaration())),
            TokenKind::KwLet => {
                if let Some(ModuleItem::LetDeclaration(l)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Let(l)))
                } else { None }
            }
            TokenKind::KwTypedef =>
                Some(Description::TypedefDecl(self.parse_typedef_declaration())),
            // IEEE 1800-2017 §3.12 / §6.20: compilation-unit ($unit) scope
            // `parameter`/`localparam` declarations. Surface them as a
            // PackageItem::Parameter so elaboration can hoist them into every
            // module (like $unit functions/tasks). Without this the top-level
            // `parameter int N = 1;` form was an "unexpected token".
            TokenKind::KwParameter | TokenKind::KwLocalparam =>
                Some(Description::PackageItem(PackageItem::Parameter(
                    self.parse_parameter_decl_stmt()))),
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
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
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
                    (hid.path[hid.path.len() - 2].name.name.clone(),
                     hid.path[hid.path.len() - 1].name.name.clone())
                } else {
                    (String::new(),
                     hid.path.last().map(|s| s.name.name.clone()).unwrap_or_default())
                };
                let mut items = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        items.push(self.parse_constraint_item());
                    }
                    self.expect(TokenKind::RBrace);
                }
                if self.at(TokenKind::Semicolon) { self.bump(); }
                if class_name.is_empty() {
                    self.parse_description()
                } else {
                    Some(Description::OutOfClassConstraint { class_name, constraint_name, items })
                }
            }
            TokenKind::KwTimeunit | TokenKind::KwTimeprecision =>
                Some(Description::TimeunitsDecl(self.parse_timeunits_declaration())),
            TokenKind::KwFunction =>
                Some(Description::PackageItem(self.parse_package_item().unwrap())),
            TokenKind::KwTask =>
                Some(Description::PackageItem(self.parse_package_item().unwrap())),
            TokenKind::Directive => { self.bump(); self.parse_description() }
            // Stray top-level `;` — e.g. `endmodule;` (an empty
            // compilation-unit item, §A.1.2). Skip and continue.
            TokenKind::Semicolon => { self.bump(); self.parse_description() }
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
                    && matches!(self.peek_kind(),
                        TokenKind::Identifier | TokenKind::DoubleColon
                        | TokenKind::Hash | TokenKind::LBracket);
                // §A.2.1.3: a data_declaration may carry an explicit LIFETIME
                // (`static int n = 0;`). `parse_data_declaration` already eats
                // it, but this guard did not admit one, so a $unit-scope
                // `static`/`automatic` declaration — the usual way a testbench
                // keeps a shared failure counter — died as "unexpected token".
                if self.is_data_type_keyword() || self.at(TokenKind::KwVar)
                    || self.at(TokenKind::KwConst) || is_user_type_decl
                    || self.at(TokenKind::KwStatic) || self.at(TokenKind::KwAutomatic)
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
                            TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => depth += 1,
                            TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket => depth -= 1,
                            TokenKind::Semicolon if depth <= 0 => { self.bump(); break; }
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
        use crate::ast::decl::{UdpDecl, UdpTableRow, UdpSym, UdpOut};
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
                    TokenKind::LParen => { depth += 1; self.bump(); }
                    TokenKind::RParen => { depth -= 1; self.bump(); }
                    TokenKind::KwReg if depth == 1 => { is_sequential = true; self.bump(); }
                    TokenKind::Identifier | TokenKind::EscapedIdentifier if depth == 1 => {
                        ports.push(self.parse_identifier());
                    }
                    _ => { self.bump(); }
                }
            }
        }
        self.eat(TokenKind::Semicolon);

        // --- Body declarations up to `table`: pick up `reg` (=> sequential)
        // and `initial out = 1'bX;` (start state).
        let mut init: Option<char> = None;
        while !self.at(TokenKind::KwTable) && !self.at(TokenKind::KwEndprimitive)
            && !self.at(TokenKind::Eof)
        {
            match self.current_kind() {
                TokenKind::KwReg => { is_sequential = true; self.skip_udp_to_semi(); }
                TokenKind::KwInitial => {
                    self.bump(); // `initial`
                    // out = <value> ;  — collect value tokens after `=`.
                    let mut seen_eq = false;
                    let mut val = String::new();
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof)
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
                _ => { self.skip_udp_to_semi(); }
            }
        }

        // --- Table.
        let n_inputs = ports.len().saturating_sub(1);
        let mut rows: Vec<UdpTableRow> = Vec::new();
        let mut table_ok = true;
        let mut fail_detail = String::new();
        let table_line = self.current_line();
        if self.eat(TokenKind::KwTable).is_some() {
            // Gather raw table tokens up to `endtable`.
            let mut toks: Vec<Token> = Vec::new();
            while !self.at(TokenKind::KwEndtable) && !self.at(TokenKind::Eof)
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
                    match Self::parse_udp_row(slice, n_inputs) {
                        Some(r) => rows.push(r),
                        None => {
                            table_ok = false;
                            let txt: String = slice.iter()
                                .map(|t| t.text.clone())
                                .collect::<Vec<_>>()
                                .join(" ");
                            fail_detail = txt;
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
        if self.eat(TokenKind::Colon).is_some() { let _ = self.parse_identifier(); }

        let span = self.span_from(start);
        let _ = UdpOut::NoChange; // (variant use silence if unused paths)
        let _ = UdpSym::AnyQ;

        if table_ok && !rows.is_empty() {
            Description::Udp(UdpDecl {
                name, ports, is_sequential, init, rows, span,
            })
        } else {
            // FAIL LOUD: name exactly what could not be parsed and the
            // consequence, then fall back to an empty-module stub (output
            // net left undriven) for this UDP only.
            eprintln!(
                "\n========================================================================\n\
                 Warning: UNSUPPORTED UDP TABLE — primitive '{}' (near source byte {})\n\
                 xezim could not parse the truth-table row: `{}`\n\
                 Consequence: this primitive is treated as an EMPTY module; every\n\
                 instance's output net is left UNDRIVEN (floats to x/z).\n\
                 (IEEE 1800-2017 §29 — please report this table to the xezim authors.)\n\
                 ========================================================================\n",
                name.name, table_line, fail_detail
            );
            self.diagnostics.push(crate::diagnostics::Diagnostic::warning(
                format!("unsupported UDP truth-table in primitive '{}' (row: {}); \
                         instances left undriven", name.name, fail_detail),
                span,
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
        while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof)
            && !self.at(TokenKind::KwTable) && !self.at(TokenKind::KwEndprimitive)
        {
            self.bump();
        }
        self.eat(TokenKind::Semicolon);
    }

    /// 1-based source line of the current token (best-effort).
    fn current_line(&self) -> usize {
        let off = self.current().span.start;
        // We don't have the source here; approximate with byte offset so the
        // message is still actionable. Kept small to avoid pulling source in.
        off
    }

    /// Parse one truth-table row from a raw token slice (columns are
    /// `:`-separated; combinational = 2 fields, sequential = 3). Returns
    /// `None` on any unrecognised symbol or shape so the caller can fall back.
    fn parse_udp_row(slice: &[Token], n_inputs: usize) -> Option<crate::ast::decl::UdpTableRow> {
        use crate::ast::decl::{UdpTableRow, UdpOut};
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
        if inputs.len() != n_inputs { return None; }
        let state = match state_f {
            Some(f) => {
                let mut s = Self::parse_udp_syms(f)?;
                if s.len() != 1 { return None; }
                Some(s.remove(0))
            }
            None => None,
        };
        // Output field: single symbol 0/1/x, or `-` (sequential no-change).
        if out_f.len() != 1 { return None; }
        let output = match out_f[0].text.as_str() {
            "0" => UdpOut::Level('0'),
            "1" => UdpOut::Level('1'),
            "x" | "X" => UdpOut::Level('x'),
            "-" => UdpOut::NoChange,
            _ => return None,
        };
        let span = slice.first().map(|t| t.span).unwrap_or(crate::ast::Span::dummy());
        Some(UdpTableRow { inputs, state, output, span })
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
                    if j >= field.len() { return None; } // unmatched `(`
                    i = j + 1;
                    let chars: Vec<char> =
                        txt.chars().filter(|c| !c.is_whitespace()).collect();
                    if chars.len() != 2 { return None; }
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
