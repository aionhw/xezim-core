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
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0, diagnostics: Vec::new(),
               pending_pattern_bindings: Vec::new(),
               in_sva_seq: false }
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

    fn parse_description(&mut self) -> Option<Description> {
        match self.current_kind() {
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
            // §28.3 User-Defined Primitive. xezim doesn't model UDP truth
            // tables; surface it as an empty module with the same port list so
            // instantiations resolve and simulation completes (the output net
            // is simply left undriven). Robust against combinational and
            // sequential (`reg`/`table`) UDP bodies alike.
            TokenKind::KwPrimitive => {
                let start = self.current().span.start;
                self.bump();
                let name = self.parse_identifier();
                // Collect bare port identifiers from the header `(...)`,
                // skipping ANSI direction keywords / punctuation.
                let mut ports: Vec<crate::ast::Identifier> = Vec::new();
                if self.eat(TokenKind::LParen).is_some() {
                    let mut depth = 1i32;
                    while depth > 0 && !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LParen => { depth += 1; self.bump(); }
                            TokenKind::RParen => { depth -= 1; self.bump(); }
                            TokenKind::Identifier | TokenKind::EscapedIdentifier
                                if depth == 1 => { ports.push(self.parse_identifier()); }
                            _ => { self.bump(); }
                        }
                    }
                }
                self.eat(TokenKind::Semicolon);
                // Skip the body up to `endprimitive`.
                while !self.at(TokenKind::KwEndprimitive) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                self.expect(TokenKind::KwEndprimitive);
                if self.eat(TokenKind::Colon).is_some() { let _ = self.parse_identifier(); }
                Some(Description::Module(crate::ast::module::ModuleDeclaration {
                    attrs: Vec::new(),
                    kind: crate::ast::module::ModuleKind::Module,
                    lifetime: None,
                    name,
                    params: Vec::new(),
                    ports: crate::ast::module::PortList::NonAnsi(ports),
                    items: Vec::new(),
                    endlabel: None,
                    span: self.span_from(start),
                }))
            }
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
                // visible to class methods that reference it — UVM tests do
                // `string label = "X"; … \`uvm_info(label, …)`).
                if self.is_data_type_keyword() || self.at(TokenKind::KwVar) || self.at(TokenKind::KwConst) {
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
}
