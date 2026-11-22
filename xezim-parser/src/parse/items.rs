//! Module-level item parsing (IEEE 1800-2017 §A.1)

use super::ClassInfo;
use super::{Parser, compact_syntax_list};
use crate::ast::Identifier;
use crate::ast::decl::*;
use crate::ast::expr::*;
use crate::ast::module::*;
use crate::ast::types::*;
use crate::lexer::stream::TokenStream;
use crate::lexer::token::{Token, TokenKind};

mod assertions;
mod classes;
mod constraints;
mod covergroups;
mod generate;
mod instances;
mod module_items;
mod nets_gates;
mod ports;
mod specify;

/// Which constraint production the caller is inside, which is what decides
/// whether a leading `{` can open a nested block at all (IEEE 1800-2023
/// §18.5.2):
///
/// * `constraint_block ::= { { constraint_block_item } }` and
///   `constraint_block_item ::= solve ... | constraint_expression` — a bare
///   `{...}` block is not a block item, so here `{` can only begin an
///   expression (a concatenation, §11.4.12).
/// * `constraint_set ::= constraint_expression | { { constraint_expression } }`
///   — after `if (...)`, `else`, `foreach (...)` and `->` both readings are
///   legal, so that position needs a lookahead.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstraintPos {
    /// Inside a `constraint_block`: `{` starts an expression only.
    BlockItem,
    /// A `constraint_set` position (`if`/`else`/`foreach`/`->`): `{` may open
    /// a nested set or begin a concatenation expression.
    ConstraintSet,
}

impl<'a> Parser<'a> {
    /// The `edge_identifier` that may open a §14.3 `clocking_skew`.
    fn parse_clocking_skew_edge(&mut self) -> Option<crate::ast::stmt::Edge> {
        let edge = match self.current_kind() {
            TokenKind::KwPosedge => crate::ast::stmt::Edge::Posedge,
            TokenKind::KwNegedge => crate::ast::stmt::Edge::Negedge,
            TokenKind::KwEdge => crate::ast::stmt::Edge::Edge,
            _ => return None,
        };
        self.bump();
        Some(edge)
    }

    /// IEEE 1800-2023 §14.4 clocking skew value after the `#`: `1step`, a
    /// number or time literal, a parameter name, or a parenthesized
    /// expression. `1step` lexes as the integer `1` followed by the
    /// identifier `step` with no space between; it used to be read as `#1`
    /// and the rest of the `default` item (`output #2`) was skipped.
    fn parse_clocking_skew_value(&mut self) -> Option<crate::ast::expr::Expression> {
        if self.at(TokenKind::IntegerLiteral)
            && self.current_text() == "1"
            && self.peek_kind() == TokenKind::Identifier
        {
            let one = self.current_span();
            let step = self.tokens.span_at(self.pos + 1);
            if self.tokens.text_at(self.pos + 1) == "step" && step.start == one.end {
                self.bump();
                self.bump();
                let sp = crate::ast::Span {
                    start: one.start,
                    end: step.end,
                };
                let hier = HierarchicalIdentifier {
                    root: None,
                    path: vec![HierPathSegment {
                        name: Identifier {
                            name: crate::ast::decl::CLOCKING_ONE_STEP.to_string(),
                            span: sp,
                        },
                        selects: Vec::new(),
                    }],
                    span: sp,
                    cached_signal_id: crate::ast::cache::SignalCache::new(None),
                    cached_resolved_name: crate::ast::cache::NameCache::new(),
                    bound: crate::ast::binding::Bound::UNSET,
                };
                return Some(Expression::new(ExprKind::Ident(hier), sp));
            }
        }
        if self.at(TokenKind::LParen) {
            self.bump();
            let e = self.parse_expression();
            self.expect(TokenKind::RParen);
            return Some(e);
        }
        if matches!(
            self.current_kind(),
            TokenKind::IntegerLiteral | TokenKind::TimeLiteral | TokenKind::RealLiteral
        ) {
            return Some(self.parse_expr_bp(3));
        }
        if self.at(TokenKind::Identifier) {
            let id = self.parse_identifier();
            let sp = id.span;
            let hier = HierarchicalIdentifier {
                root: None,
                path: vec![HierPathSegment {
                    name: id,
                    selects: Vec::new(),
                }],
                span: sp,
                cached_signal_id: crate::ast::cache::SignalCache::new(None),
                cached_resolved_name: crate::ast::cache::NameCache::new(),
                bound: crate::ast::binding::Bound::UNSET,
            };
            return Some(Expression::new(ExprKind::Ident(hier), sp));
        }
        self.bump();
        None
    }

    /// §6.20.5: check complete lexical scopes, including forward references.
    /// A parser-global seen-name list leaks across modules and rejects legal
    /// declarations after an unrelated module's specparam of the same name.
    fn check_param_specparams(&mut self, params: &[ParameterDeclaration], items: &[ModuleItem]) {
        if !crate::strict_checks() {
            return;
        }
        fn walk(
            parser: &mut Parser,
            params: &[ParameterDeclaration],
            items: &[ModuleItem],
            inherited: &[String],
        ) {
            let decls: Vec<_> = params
                .iter()
                .chain(items.iter().filter_map(|item| match item {
                    ModuleItem::ParameterDeclaration(pd)
                    | ModuleItem::LocalparamDeclaration(pd) => Some(pd),
                    _ => None,
                }))
                .collect();
            let mut local_names = Vec::new();
            for pd in &decls {
                match &pd.kind {
                    ParameterKind::Data { assignments, .. } => {
                        local_names.extend(assignments.iter().map(|a| a.name.name.clone()))
                    }
                    ParameterKind::Type { assignments } => {
                        local_names.extend(assignments.iter().map(|a| a.name.name.clone()))
                    }
                }
            }
            for item in items {
                if let ModuleItem::DataDeclaration(dd) = item {
                    local_names.extend(dd.declarators.iter().map(|d| d.name.name.clone()));
                }
            }
            let mut visible: Vec<String> = inherited
                .iter()
                .filter(|n| !local_names.contains(n))
                .cloned()
                .collect();
            for pd in &decls {
                if pd.specparam
                    && let ParameterKind::Data { assignments, .. } = &pd.kind
                {
                    visible.extend(assignments.iter().map(|a| a.name.name.clone()));
                }
            }
            if visible.is_empty() {
                return;
            }
            for pd in decls {
                if pd.specparam {
                    continue;
                }
                let ParameterKind::Data { assignments, .. } = &pd.kind else {
                    continue;
                };
                for a in assignments {
                    let Some(init) = &a.init else { continue };
                    let mut ids = Vec::new();
                    Parser::expr_idents(init, &mut ids);
                    if let Some(sp) = ids.iter().find(|n| visible.contains(n)) {
                        parser.diagnostics.push(crate::diagnostics::Diagnostic::error(format!(
                            "parameter/localparam '{}' may not be initialized with the specify parameter '{}' (IEEE 1800-2017 §6.20.5)",
                            a.name.name, sp), init.span));
                    }
                }
            }
            for item in items {
                match item {
                    ModuleItem::GenerateRegion(g) => walk(parser, &[], &g.items, &visible),
                    ModuleItem::GenerateFor(g) => walk(parser, &[], &g.items, &visible),
                    ModuleItem::GenerateIf(g) => {
                        for (_, items) in &g.branches {
                            walk(parser, &[], items, &visible);
                        }
                    }
                    ModuleItem::GenerateCase(g) => {
                        for arm in &g.arms {
                            walk(parser, &[], &arm.items, &visible);
                        }
                    }
                    _ => {}
                }
            }
        }
        walk(self, params, items, &[]);
    }

    /// Does the statement read or write the bare name `name`?
    fn stmt_mentions(stmt: &crate::ast::stmt::Statement, name: &str) -> bool {
        use crate::ast::stmt::StatementKind as K;
        let e = |x: &Expression| {
            let mut v = Vec::new();
            Self::expr_idents(x, &mut v);
            v.iter().any(|n| n == name)
        };
        match &stmt.kind {
            K::Expr(x) => e(x),
            K::BlockingAssign { lvalue, rvalue } | K::NonblockingAssign { lvalue, rvalue, .. } => {
                e(lvalue) || e(rvalue)
            }
            K::If {
                condition,
                then_stmt,
                else_stmt,
                ..
            } => {
                e(condition)
                    || Self::stmt_mentions(then_stmt, name)
                    || else_stmt
                        .as_deref()
                        .is_some_and(|s| Self::stmt_mentions(s, name))
            }
            K::Case { expr, items, .. } => {
                e(expr)
                    || items
                        .iter()
                        .any(|i| i.patterns.iter().any(e) || Self::stmt_mentions(&i.stmt, name))
            }
            K::For {
                condition,
                step,
                body,
                ..
            } => {
                condition.as_ref().is_some_and(e)
                    || step.iter().any(e)
                    || Self::stmt_mentions(body, name)
            }
            K::While { condition, body } | K::DoWhile { body, condition } => {
                e(condition) || Self::stmt_mentions(body, name)
            }
            K::Repeat { count, body } => e(count) || Self::stmt_mentions(body, name),
            K::Foreach { array, body, .. } => e(array) || Self::stmt_mentions(body, name),
            K::Forever { body } => Self::stmt_mentions(body, name),
            K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => {
                stmts.iter().any(|s| Self::stmt_mentions(s, name))
            }
            K::Assertion(a) => {
                e(&a.expr)
                    || a.action
                        .as_deref()
                        .is_some_and(|s| Self::stmt_mentions(s, name))
                    || a.else_action
                        .as_deref()
                        .is_some_and(|s| Self::stmt_mentions(s, name))
            }
            _ => false,
        }
    }

    pub(super) fn parse_module_declaration(&mut self) -> ModuleDeclaration {
        let start = self.current_span().start;
        let outer_loops = std::mem::take(&mut self.plain_loop_vars);
        let kind = if self.eat(TokenKind::KwMacromodule).is_some() {
            ModuleKind::Macromodule
        } else {
            self.expect(TokenKind::KwModule);
            ModuleKind::Module
        };
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let header_imports = self.parse_module_header_imports();
        let params = self.parse_parameter_port_list();
        let ports = self.parse_port_list();
        let port_exprs = std::mem::take(&mut self.port_exprs);
        self.expect(TokenKind::Semicolon);

        // §11.13: a design element is a let scope.
        self.push_let_scope();
        let mut items = self.parse_module_items();
        self.pop_let_scope();
        if !header_imports.is_empty() {
            let mut prefixed = Vec::with_capacity(header_imports.len() + items.len());
            prefixed.extend(header_imports);
            prefixed.extend(items);
            items = prefixed;
        }
        self.lower_port_expressions(&ports, &mut items, port_exprs);
        default_subroutine_lifetime(&mut items, lifetime);

        self.expect(TokenKind::KwEndmodule);
        let endlabel = self.parse_end_label_checked(&name.name);
        let loops = std::mem::replace(&mut self.plain_loop_vars, outer_loops);
        self.check_generate_loop_vars(&loops, &items);
        self.check_param_specparams(&params, &items);

        ModuleDeclaration {
            lexical_parent: None,
            attrs: Vec::new(),
            kind,
            lifetime,
            name,
            params,
            ports,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    pub(super) fn parse_interface_declaration(&mut self) -> InterfaceDeclaration {
        let start = self.current_span().start;
        let outer_loops = std::mem::take(&mut self.plain_loop_vars);
        self.expect(TokenKind::KwInterface);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let header_imports = self.parse_module_header_imports();
        let params = self.parse_parameter_port_list();
        let ports = self.parse_port_list();
        let port_exprs = std::mem::take(&mut self.port_exprs);
        self.expect(TokenKind::Semicolon);

        // §11.13: a design element is a let scope.
        self.push_let_scope();
        let mut items = self.parse_module_items();
        self.pop_let_scope();
        if !header_imports.is_empty() {
            let mut prefixed = Vec::with_capacity(header_imports.len() + items.len());
            prefixed.extend(header_imports);
            prefixed.extend(items);
            items = prefixed;
        }
        self.lower_port_expressions(&ports, &mut items, port_exprs);
        default_subroutine_lifetime(&mut items, lifetime);

        self.expect(TokenKind::KwEndinterface);
        let endlabel = self.parse_end_label();
        let loops = std::mem::replace(&mut self.plain_loop_vars, outer_loops);
        self.check_generate_loop_vars(&loops, &items);

        InterfaceDeclaration {
            attrs: Vec::new(),
            lifetime,
            name,
            params,
            ports,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    pub(super) fn parse_program_declaration(&mut self) -> ProgramDeclaration {
        let start = self.current_span().start;
        let outer_loops = std::mem::take(&mut self.plain_loop_vars);
        self.expect(TokenKind::KwProgram);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let header_imports = self.parse_module_header_imports();
        let params = self.parse_parameter_port_list();
        let ports = self.parse_port_list();
        let port_exprs = std::mem::take(&mut self.port_exprs);
        self.expect(TokenKind::Semicolon);

        // §11.13: a design element is a let scope.
        self.push_let_scope();
        let mut items = self.parse_module_items();
        self.pop_let_scope();
        if !header_imports.is_empty() {
            let mut prefixed = Vec::with_capacity(header_imports.len() + items.len());
            prefixed.extend(header_imports);
            prefixed.extend(items);
            items = prefixed;
        }
        self.lower_port_expressions(&ports, &mut items, port_exprs);
        default_subroutine_lifetime(&mut items, lifetime);

        self.expect(TokenKind::KwEndprogram);
        let endlabel = self.parse_end_label();
        let loops = std::mem::replace(&mut self.plain_loop_vars, outer_loops);
        self.check_generate_loop_vars(&loops, &items);

        ProgramDeclaration {
            attrs: Vec::new(),
            lifetime,
            name,
            params,
            ports,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    fn parse_module_header_imports(&mut self) -> Vec<ModuleItem> {
        let mut imports = Vec::new();
        while self.at(TokenKind::KwImport) && self.peek_kind() != TokenKind::StringLiteral {
            imports.push(ModuleItem::ImportDeclaration(
                self.parse_import_declaration(),
            ));
        }
        imports
    }

    /// Whether the bracket groups starting `n` tokens ahead are followed by
    /// an identifier: `my_t [3:0] x` (a type, packed dimensions, a name), not
    /// `a [4]` (a name and its unpacked dimensions, §7.4.2, #657).
    pub(super) fn dims_then_identifier(&self, mut n: usize) -> bool {
        while self.peek_kind_n(n) == TokenKind::LBracket {
            let mut depth = 0usize;
            loop {
                match self.peek_kind_n(n) {
                    TokenKind::LBracket => depth += 1,
                    TokenKind::RBracket => {
                        depth -= 1;
                        if depth == 0 {
                            n += 1;
                            break;
                        }
                    }
                    TokenKind::Eof | TokenKind::Semicolon => return false,
                    _ => {}
                }
                n += 1;
            }
        }
        matches!(
            self.peek_kind_n(n),
            TokenKind::Identifier | TokenKind::EscapedIdentifier
        )
    }

    pub(super) fn parse_package_declaration(&mut self) -> PackageDeclaration {
        let start = self.current_span().start;
        self.expect(TokenKind::KwPackage);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        self.expect(TokenKind::Semicolon);

        let mut items = Vec::new();
        self.push_let_scope();
        while !self.at(TokenKind::KwEndpackage) && !self.at(TokenKind::Eof) {
            if self.at(TokenKind::KwConstraint) {
                self.parse_package_ooc_constraint(&mut items);
                self.release_consumed_tokens();
                continue;
            }
            if let Some(item) = self.parse_package_item() {
                items.push(item);
            } else {
                self.bump();
            }
            self.release_consumed_tokens();
        }
        self.pop_let_scope();
        if lifetime == Some(Lifetime::Automatic) {
            for it in &mut items {
                match it {
                    PackageItem::Function(fd) if fd.name.scopes.is_empty() => {
                        fd.lifetime.get_or_insert(Lifetime::Automatic);
                    }
                    PackageItem::Task(td) if td.name.scopes.is_empty() => {
                        td.lifetime.get_or_insert(Lifetime::Automatic);
                    }
                    _ => {}
                }
            }
        }

        self.expect(TokenKind::KwEndpackage);
        let endlabel = self.parse_end_label();

        PackageDeclaration {
            attrs: Vec::new(),
            lifetime,
            name,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    /// §27.4: the index of a generate loop is a genvar. One that names a
    /// variable of the enclosing design element (`integer i; ... for (i = 0;
    /// ...) begin : U`) and no genvar is an error.
    fn check_generate_loop_vars(&mut self, loops: &[Identifier], items: &[ModuleItem]) {
        if !crate::strict_checks() || loops.is_empty() {
            return;
        }
        fn walk<'a>(
            items: &'a [ModuleItem],
            top: bool,
            vars: &mut Vec<&'a str>,
            genvars: &mut Vec<&'a str>,
        ) {
            for it in items {
                match it {
                    ModuleItem::DataDeclaration(d) if top => {
                        vars.extend(d.declarators.iter().map(|v| v.name.name.as_str()))
                    }
                    ModuleItem::GenvarDeclaration(g) => {
                        genvars.extend(g.names.iter().map(|n| n.name.as_str()))
                    }
                    ModuleItem::GenerateRegion(gr) => walk(&gr.items, top, vars, genvars),
                    ModuleItem::GenerateFor(gf) => walk(&gf.items, false, vars, genvars),
                    ModuleItem::GenerateIf(gi) => {
                        for (_, b) in &gi.branches {
                            walk(b, false, vars, genvars);
                        }
                    }
                    ModuleItem::GenerateCase(gc) => {
                        for a in &gc.arms {
                            walk(&a.items, false, vars, genvars);
                        }
                    }
                    _ => {}
                }
            }
        }
        let (mut vars, mut genvars) = (Vec::new(), Vec::new());
        walk(items, true, &mut vars, &mut genvars);
        for v in loops {
            if vars.contains(&v.name.as_str()) && !genvars.contains(&v.name.as_str()) {
                self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                    format!(
                        "generate loop index '{}' is a variable, not a genvar (IEEE 1800-2017 §27.4)",
                        v.name
                    ),
                    v.span,
                ));
            }
        }
    }
}

impl<'a> Parser<'a> {
    /// A `wreal` net or port carries a real value and names no data type of
    /// its own -- `wreal n;` is a net type and nothing else. Substituting
    /// `real` here means every downstream question ("how wide is it", "is it
    /// real") reads the answer off the data type as usual, instead of each of
    /// those sites having to know about `NetType::Wreal`. An explicit data
    /// type is left alone.
    ///
    /// A PACKED RANGE is rejected. Verilog-AMS has no ranged `wreal`: the net
    /// carries one real value, not a vector of bits. Allowed to fall through,
    /// `wreal [3:0] w` stayed an `Implicit` type and became an ordinary 4-bit
    /// net -- `$bits` answered 4 and every value written to it was silently
    /// ROUNDED (2.5 read back 3.0), which is the exact corruption `wreal`
    /// exists to prevent, reported by nothing. Recovery substitutes `real` so
    /// the rest of the parse stays useful.
    fn wreal_data_type(
        &mut self,
        net_type: NetType,
        dt: DataType,
        span: crate::parse::Span,
    ) -> DataType {
        if !matches!(net_type, NetType::Wreal) {
            return dt;
        }
        match &dt {
            DataType::Implicit { dimensions, .. } => {
                if !dimensions.is_empty() {
                    self.error(
                        "a 'wreal' net cannot have a packed range: it carries a real value, \
                         not a vector of bits (Verilog-AMS 2.4 §3.8)",
                    );
                }
                DataType::Real {
                    kind: RealType::Real,
                    span,
                }
            }
            // The redundant explicit spelling (`wreal real x`) is harmless.
            DataType::Real {
                kind: RealType::Real,
                ..
            } => dt,
            // Issue #37: any OTHER explicit data type was silently accepted
            // AS that type — `wreal logic [3:0] p` elaborated as a 4-bit
            // vector, quietly reintroducing the integer-rounding corruption
            // the packed-range rejection above exists to prevent. Same
            // diagnostic, same recovery.
            _ => {
                self.error(
                    "a 'wreal' net carries a real value and cannot take a data type \
                     (Verilog-AMS 2.4 §3.8)",
                );
                DataType::Real {
                    kind: RealType::Real,
                    span,
                }
            }
        }
    }
}

/// IEEE 1800-2023 §6.21 / §13.3 / §13.4: a module, interface or program
/// declared `automatic` makes automatic the default lifetime of every task
/// and function declared in it (generate blocks included). A subroutine
/// with an explicit `static` keeps it; out-of-class method bodies
/// (`function C::m`) are class methods, automatic anyway (§8.6).
fn default_subroutine_lifetime(items: &mut [ModuleItem], lifetime: Option<Lifetime>) {
    if lifetime != Some(Lifetime::Automatic) {
        return;
    }
    for it in items {
        match it {
            ModuleItem::FunctionDeclaration(fd) if fd.name.scopes.is_empty() => {
                fd.lifetime.get_or_insert(Lifetime::Automatic);
            }
            ModuleItem::TaskDeclaration(td) if td.name.scopes.is_empty() => {
                td.lifetime.get_or_insert(Lifetime::Automatic);
            }
            ModuleItem::GenerateRegion(g) => default_subroutine_lifetime(&mut g.items, lifetime),
            ModuleItem::GenerateFor(g) => default_subroutine_lifetime(&mut g.items, lifetime),
            ModuleItem::GenerateIf(g) => {
                for (_, b) in &mut g.branches {
                    default_subroutine_lifetime(b, lifetime);
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &mut g.arms {
                    default_subroutine_lifetime(&mut arm.items, lifetime);
                }
            }
            _ => {}
        }
    }
}
