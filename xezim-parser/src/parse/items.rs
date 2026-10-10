//! Module-level item parsing (IEEE 1800-2017 §A.1)

use super::Parser;
use crate::ast::Identifier;
use crate::ast::decl::*;
use crate::ast::expr::*;
use crate::ast::module::*;
use crate::ast::types::*;
use crate::lexer::token::TokenKind;

impl Parser {
    /// IEEE 1800-2023 §14.4 clocking skew value after the `#`: `1step`, a
    /// number or time literal, a parameter name, or a parenthesized
    /// expression. `1step` lexes as the integer `1` followed by the
    /// identifier `step` with no space between; it used to be read as `#1`
    /// and the rest of the `default` item (`output #2`) was skipped.
    fn parse_clocking_skew_value(&mut self) -> Option<crate::ast::expr::Expression> {
        if self.at(TokenKind::IntegerLiteral)
            && self.current().text == "1"
            && self.peek_kind() == TokenKind::Identifier
        {
            let one = self.current().span;
            let step = self.tokens[self.pos + 1].span;
            if self.tokens[self.pos + 1].text == "step" && step.start == one.end {
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
                    cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
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
                cached_signal_id: std::cell::Cell::new(None),
                cached_resolved_name: std::cell::OnceCell::new(),
            };
            return Some(Expression::new(ExprKind::Ident(hier), sp));
        }
        self.bump();
        None
    }

    /// §16.10: the `assertion_variable_declaration`s at the head of a
    /// property or sequence body, each kept as
    /// `$sva_local(<type>, <name> [, <init>])` for the simulator, which gives
    /// every evaluation attempt its own copy.
    fn parse_sva_local_declarations(&mut self) -> Vec<Expression> {
        let mut decls = Vec::new();
        loop {
            if !self.is_type_start() && !self.at(TokenKind::KwVar) {
                return decls;
            }
            // Distinguish a declaration from a typedef cast or an ordinary
            // sequence expression without consuming either spelling.
            let saved_pos = self.pos;
            let saved_diagnostics = self.diagnostics.len();
            let explicit_var = self.eat(TokenKind::KwVar).is_some();
            // `var` also permits an implicit type, as in `var stamp;`.
            let implicit = explicit_var
                && matches!(
                    self.current_kind(),
                    TokenKind::Identifier | TokenKind::EscapedIdentifier
                )
                && matches!(
                    self.peek_kind(),
                    TokenKind::Semicolon | TokenKind::Assign | TokenKind::Comma
                );
            let tstart = self.current().span.start;
            let data_type = if implicit {
                DataType::Implicit {
                    signing: None,
                    dimensions: Vec::new(),
                    span: self.span_from(tstart),
                }
            } else {
                self.parse_data_type()
            };
            let declaration = explicit_var
                || (self.diagnostics.len() == saved_diagnostics
                    && matches!(
                        self.current_kind(),
                        TokenKind::Identifier | TokenKind::EscapedIdentifier
                    ));
            if !declaration {
                self.pos = saved_pos;
                self.diagnostics.truncate(saved_diagnostics);
                return decls;
            }
            loop {
                let name = self.parse_identifier();
                let span = name.span;
                let mut args = vec![
                    Expression::new(ExprKind::TypeLiteral(Box::new(data_type.clone())), span),
                    Self::sva_ident(name),
                ];
                if self.eat(TokenKind::Assign).is_some() {
                    args.push(self.parse_expression());
                }
                decls.push(Expression::new(
                    ExprKind::SystemCall {
                        name: "$sva_local".to_string(),
                        args,
                    },
                    span,
                ));
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::Semicolon);
        }
    }

    /// §16.8.2 local variable formal arguments (`local input int v`): the
    /// formal is a local variable of each attempt initialised from its
    /// actual. The body's references are renamed to a local `v$lf`, declared
    /// with the formal (substituted by the actual at instantiation) as its
    /// initialiser, so the attempt can assign it without touching the actual.
    fn sva_bind_local_formals(
        locals: &[(Identifier, DataType)],
        decls: &mut Vec<Expression>,
        body: &mut Expression,
    ) {
        for (formal, dt) in locals {
            let local = format!("{}$lf", formal.name);
            Self::sva_rename_ident(body, &formal.name, &local);
            for d in decls.iter_mut() {
                Self::sva_rename_ident(d, &formal.name, &local);
            }
            let span = formal.span;
            decls.insert(
                0,
                Expression::new(
                    ExprKind::SystemCall {
                        name: "$sva_local".to_string(),
                        args: vec![
                            Expression::new(ExprKind::TypeLiteral(Box::new(dt.clone())), span),
                            Self::sva_ident(Identifier { name: local, span }),
                            Self::sva_ident(formal.clone()),
                        ],
                    },
                    span,
                ),
            );
        }
    }

    /// §16.14.6: the clock a procedural concurrent assertion infers from
    /// its procedure, `always @(<edge> <expr> [iff <guard>] ...) <body>`, when
    /// the body has no other timing control: the event expression's only
    /// edge event, or, among several (`posedge clk or negedge rst_n`), the
    /// only one whose expression the body does not read.
    fn infer_procedural_assertion_clocks(stmt: &mut crate::ast::stmt::Statement) {
        use crate::ast::stmt::{EventControl, StatementKind, TimingControl};
        let StatementKind::TimingControl {
            control: TimingControl::Event(EventControl::EventExpr(events)),
            stmt: body,
        } = &mut stmt.kind
        else {
            return;
        };
        if events.is_empty() || events.iter().any(|e| e.edge.is_none()) {
            return;
        }
        if Self::stmt_has_timing(body) {
            return;
        }
        let clock = if events.len() == 1 {
            events[0].clone()
        } else {
            let free: Vec<_> = events
                .iter()
                .filter(|e| {
                    let mut names = Vec::new();
                    Self::expr_idents(&e.expr, &mut names);
                    !names.iter().any(|n| Self::stmt_mentions(body, n))
                })
                .collect();
            if free.len() != 1 {
                return;
            }
            free[0].clone()
        };
        Self::set_inferred_clock(body, &clock);
    }

    /// Does the statement hold a blocking timing control (`#`, `@`, `wait`)?
    fn stmt_has_timing(stmt: &crate::ast::stmt::Statement) -> bool {
        use crate::ast::stmt::StatementKind as K;
        match &stmt.kind {
            K::TimingControl { .. } | K::Wait { .. } | K::WaitFork | K::WaitOrder { .. } => true,
            K::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                Self::stmt_has_timing(then_stmt)
                    || else_stmt.as_deref().is_some_and(Self::stmt_has_timing)
            }
            K::Case { items, .. } => items.iter().any(|i| Self::stmt_has_timing(&i.stmt)),
            K::For { body, .. }
            | K::Foreach { body, .. }
            | K::While { body, .. }
            | K::DoWhile { body, .. }
            | K::Repeat { body, .. }
            | K::Forever { body } => Self::stmt_has_timing(body),
            K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => {
                stmts.iter().any(Self::stmt_has_timing)
            }
            _ => false,
        }
    }

    /// Give every procedural concurrent assertion in `stmt` the inferred
    /// clock `clock`.
    fn set_inferred_clock(
        stmt: &mut crate::ast::stmt::Statement,
        clock: &crate::ast::stmt::EventExpr,
    ) {
        use crate::ast::stmt::StatementKind as K;
        match &mut stmt.kind {
            K::Assertion(a) => {
                if a.is_property && a.procedural {
                    a.inferred_clock = Some(clock.clone());
                }
            }
            K::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                Self::set_inferred_clock(then_stmt, clock);
                if let Some(e) = else_stmt {
                    Self::set_inferred_clock(e, clock);
                }
            }
            K::Case { items, .. } => {
                for i in items {
                    Self::set_inferred_clock(&mut i.stmt, clock);
                }
            }
            K::For { body, .. }
            | K::Foreach { body, .. }
            | K::While { body, .. }
            | K::DoWhile { body, .. }
            | K::Repeat { body, .. }
            | K::Forever { body } => Self::set_inferred_clock(body, clock),
            K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => {
                for s in stmts {
                    Self::set_inferred_clock(s, clock);
                }
            }
            _ => {}
        }
    }

    /// The bare identifiers an expression reads.
    fn expr_idents(e: &Expression, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Ident(h) => {
                if let Some(seg) = h.path.first() {
                    out.push(seg.name.name.clone());
                }
                for seg in &h.path {
                    for sel in &seg.selects {
                        Self::expr_idents(sel, out);
                    }
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Paren(operand) => {
                Self::expr_idents(operand, out)
            }
            ExprKind::Binary { left, right, .. }
            | ExprKind::AssignExpr {
                lvalue: left,
                rvalue: right,
            }
            | ExprKind::Range(left, right) => {
                Self::expr_idents(left, out);
                Self::expr_idents(right, out);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                Self::expr_idents(condition, out);
                Self::expr_idents(then_expr, out);
                Self::expr_idents(else_expr, out);
            }
            ExprKind::Call { args, .. }
            | ExprKind::SystemCall { args, .. }
            | ExprKind::Concatenation(args) => {
                for a in args {
                    Self::expr_idents(a, out);
                }
            }
            ExprKind::Index { expr, index } => {
                Self::expr_idents(expr, out);
                Self::expr_idents(index, out);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                Self::expr_idents(expr, out);
                Self::expr_idents(left, out);
                Self::expr_idents(right, out);
            }
            ExprKind::MemberAccess { expr, .. } => Self::expr_idents(expr, out),
            ExprKind::SvaClocked { clock, body, .. } => {
                Self::expr_idents(clock, out);
                Self::expr_idents(body, out);
            }
            _ => {}
        }
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

    /// §16.10: only a local variable can be assigned in a match item list
    /// (`(seq, v = e)`); `locals` are the names the body may assign (its
    /// local variables and formals).
    pub(super) fn check_sva_match_assignments(&mut self, e: &Expression, locals: &[String]) {
        match &e.kind {
            ExprKind::SystemCall { name, args } if name == "$sva_match" => {
                for item in args.iter().skip(1) {
                    let target = match &item.kind {
                        ExprKind::AssignExpr { lvalue, .. }
                        | ExprKind::Binary {
                            op: BinaryOp::Assign,
                            left: lvalue,
                            ..
                        } => Some(&**lvalue),
                        ExprKind::Unary { op, operand }
                            if matches!(
                                op,
                                UnaryOp::PostIncr
                                    | UnaryOp::PreIncr
                                    | UnaryOp::PostDecr
                                    | UnaryOp::PreDecr
                            ) =>
                        {
                            Some(&**operand)
                        }
                        _ => None,
                    };
                    let Some(target) = target else {
                        continue;
                    };
                    let mut names = Vec::new();
                    Self::expr_idents(target, &mut names);
                    if let Some(n) = names.first().filter(|n| !locals.contains(n)) {
                        let msg = format!(
                            "illegal assignment to '{n}' in a match item list: only local \
                             variables can be assigned (IEEE 1800-2017 §16.10)"
                        );
                        self.diagnostics
                            .push(crate::diagnostics::Diagnostic::error(msg, item.span));
                    }
                }
                for a in args {
                    self.check_sva_match_assignments(a, locals);
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Paren(operand) => {
                self.check_sva_match_assignments(operand, locals)
            }
            ExprKind::Binary { left, right, .. } => {
                self.check_sva_match_assignments(left, locals);
                self.check_sva_match_assignments(right, locals);
            }
            ExprKind::SystemCall { args, .. } => {
                for a in args {
                    self.check_sva_match_assignments(a, locals);
                }
            }
            ExprKind::SvaClocked { body, .. } => self.check_sva_match_assignments(body, locals),
            _ => {}
        }
    }

    /// The names a property or sequence body may assign: its local
    /// variables (`$sva_local` declarations, renamed local formals) and its
    /// formals (a `local output` formal is one).
    fn sva_assignable_names(decls: &[Expression], ports: &[Identifier]) -> Vec<String> {
        let mut out: Vec<String> = ports.iter().map(|p| p.name.clone()).collect();
        for d in decls {
            if let ExprKind::SystemCall { args, .. } = &d.kind {
                if let Some(ExprKind::Ident(h)) = args.get(1).map(|a| &a.kind) {
                    if let Some(seg) = h.path.first() {
                        out.push(seg.name.name.clone());
                    }
                }
            }
        }
        out
    }

    /// A bare reference to `id`.
    fn sva_ident(id: Identifier) -> Expression {
        let span = id.span;
        Expression::new(
            ExprKind::Ident(HierarchicalIdentifier {
                root: None,
                path: vec![HierPathSegment {
                    name: id,
                    selects: Vec::new(),
                }],
                span,
                cached_signal_id: std::cell::Cell::new(None),
                cached_resolved_name: std::cell::OnceCell::new(),
            }),
            span,
        )
    }

    /// Rename every bare reference `from` in `e` to `to`.
    fn sva_rename_ident(e: &mut Expression, from: &str, to: &str) {
        match &mut e.kind {
            ExprKind::Ident(h) => {
                if h.root.is_none() && h.path.len() == 1 && h.path[0].name.name == from {
                    h.path[0].name.name = to.to_string();
                }
                for seg in &mut h.path {
                    for sel in &mut seg.selects {
                        Self::sva_rename_ident(sel, from, to);
                    }
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Paren(operand) => {
                Self::sva_rename_ident(operand, from, to)
            }
            ExprKind::Binary { left, right, .. }
            | ExprKind::AssignExpr {
                lvalue: left,
                rvalue: right,
            }
            | ExprKind::Range(left, right) => {
                Self::sva_rename_ident(left, from, to);
                Self::sva_rename_ident(right, from, to);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                Self::sva_rename_ident(condition, from, to);
                Self::sva_rename_ident(then_expr, from, to);
                Self::sva_rename_ident(else_expr, from, to);
            }
            ExprKind::Call { args, .. }
            | ExprKind::SystemCall { args, .. }
            | ExprKind::Concatenation(args) => {
                for a in args {
                    Self::sva_rename_ident(a, from, to);
                }
            }
            ExprKind::Replication { count, exprs } => {
                Self::sva_rename_ident(count, from, to);
                for a in exprs {
                    Self::sva_rename_ident(a, from, to);
                }
            }
            ExprKind::Index { expr, index } => {
                Self::sva_rename_ident(expr, from, to);
                Self::sva_rename_ident(index, from, to);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                Self::sva_rename_ident(expr, from, to);
                Self::sva_rename_ident(left, from, to);
                Self::sva_rename_ident(right, from, to);
            }
            ExprKind::MemberAccess { expr, .. } => Self::sva_rename_ident(expr, from, to),
            ExprKind::Inside { expr, ranges } => {
                Self::sva_rename_ident(expr, from, to);
                for r in ranges {
                    Self::sva_rename_ident(r, from, to);
                }
            }
            ExprKind::SvaClocked {
                clock, iff, body, ..
            } => {
                Self::sva_rename_ident(clock, from, to);
                if let Some(g) = iff {
                    Self::sva_rename_ident(g, from, to);
                }
                Self::sva_rename_ident(body, from, to);
            }
            _ => {}
        }
    }

    /// Wrap a property or sequence body in its local variable declarations
    /// (`$sva_locals(<decl>..., <body>)`), if it has any.
    fn sva_wrap_locals(decls: Vec<Expression>, body: Expression) -> Expression {
        if decls.is_empty() {
            return body;
        }
        let span = body.span;
        let mut args = decls;
        args.push(body);
        Expression::new(
            ExprKind::SystemCall {
                name: "$sva_locals".to_string(),
                args,
            },
            span,
        )
    }

    pub(super) fn parse_module_declaration(&mut self) -> ModuleDeclaration {
        let start = self.current().span.start;
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

        ModuleDeclaration {
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
        let start = self.current().span.start;
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
        let start = self.current().span.start;
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

    /// §16.5/§16.6: consume an SVA property/sequence port list and return
    /// the FORMAL NAMES in declaration order. Each top-level comma-separated
    /// segment may carry `local`/direction keywords, a type, and a default
    /// (`= expr`); the port name is the last identifier before the default
    /// (or before the segment end). Called with the cursor ON the `(`.
    /// The formal port names of a property or sequence declaration, and its
    /// §16.8.2 `local [input]` formals with their types.
    fn parse_sva_port_names(&mut self) -> (Vec<Identifier>, Vec<(Identifier, DataType)>) {
        let mut ports: Vec<Identifier> = Vec::new();
        let mut local_ports: Vec<(Identifier, DataType)> = Vec::new();
        self.bump(); // (
        let mut depth: i32 = 1;
        let mut last_ident: Option<Identifier> = None;
        let mut in_default = false;
        let mut port_start = true;
        // The type of the current formal when it is a `local [input]` one.
        let mut local_type: Option<DataType> = None;
        let finish = |last: &mut Option<Identifier>,
                      local: &mut Option<DataType>,
                      ports: &mut Vec<Identifier>,
                      local_ports: &mut Vec<(Identifier, DataType)>| {
            if let Some(id) = last.take() {
                if let Some(dt) = local.take() {
                    local_ports.push((id.clone(), dt));
                }
                ports.push(id);
            }
            *local = None;
        };
        while depth > 0 && !self.at(TokenKind::Eof) {
            if port_start && depth == 1 && self.at(TokenKind::KwLocal) {
                self.bump();
                let input = match self.current_kind() {
                    TokenKind::KwInput => {
                        self.bump();
                        true
                    }
                    TokenKind::KwOutput | TokenKind::KwInout => {
                        self.bump();
                        false
                    }
                    _ => true,
                };
                let tstart = self.current().span.start;
                let named_now = matches!(
                    self.current_kind(),
                    TokenKind::Identifier | TokenKind::EscapedIdentifier
                ) && matches!(
                    self.peek_kind(),
                    TokenKind::Comma | TokenKind::RParen | TokenKind::Assign
                );
                let dt = if named_now || !self.is_type_start() {
                    DataType::Implicit {
                        signing: None,
                        dimensions: Vec::new(),
                        span: self.span_from(tstart),
                    }
                } else {
                    self.parse_data_type()
                };
                // `local output` / `local inout` formals stay plain
                // substitutions (not modelled as locals).
                local_type = input.then_some(dt);
            }
            port_start = false;
            match self.current_kind() {
                TokenKind::LParen | TokenKind::LBracket => {
                    depth += 1;
                    self.bump();
                }
                TokenKind::RParen | TokenKind::RBracket => {
                    depth -= 1;
                    if depth == 0 {
                        finish(
                            &mut last_ident,
                            &mut local_type,
                            &mut ports,
                            &mut local_ports,
                        );
                    }
                    self.bump();
                }
                TokenKind::Comma if depth == 1 => {
                    finish(
                        &mut last_ident,
                        &mut local_type,
                        &mut ports,
                        &mut local_ports,
                    );
                    in_default = false;
                    port_start = true;
                    self.bump();
                }
                TokenKind::Assign if depth == 1 => {
                    // default value: the name is already in last_ident;
                    // idents inside the default must not overwrite it.
                    in_default = true;
                    self.bump();
                }
                TokenKind::Identifier | TokenKind::EscapedIdentifier => {
                    if !in_default {
                        last_ident = Some(self.parse_identifier());
                    } else {
                        self.bump();
                    }
                }
                _ => {
                    self.bump();
                }
            }
        }
        (ports, local_ports)
    }

    pub(super) fn parse_package_declaration(&mut self) -> PackageDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwPackage);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        self.expect(TokenKind::Semicolon);

        let mut items = Vec::new();
        self.push_let_scope();
        while !self.at(TokenKind::KwEndpackage) && !self.at(TokenKind::Eof) {
            if let Some(item) = self.parse_package_item() {
                items.push(item);
            } else {
                self.bump();
            }
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

    pub(super) fn parse_port_list(&mut self) -> PortList {
        self.port_exprs.clear();
        if self.eat(TokenKind::LParen).is_none() {
            return PortList::Empty;
        }
        if self.at(TokenKind::RParen) {
            self.bump();
            return PortList::Empty;
        }
        if self.is_port_direction() || self.is_data_type_keyword() || self.at(TokenKind::KwVar)
            // §6.6.8 — `interconnect p` opens an ANSI port list too.
            || self.at(TokenKind::KwInterconnect)
            || (self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Dot)
            || (self.at(TokenKind::Identifier) && matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash))
            // LRM §25.9 — `virtual <iface_t> <name>` port form.
            || (self.at(TokenKind::KwVirtual)
                && matches!(self.peek_kind(),
                    TokenKind::KwInterface | TokenKind::Identifier))
            // LRM §25.3.2 — generic interface port `interface [.mp] <name>`.
            || self.at(TokenKind::KwInterface)
        {
            let mut ports = Vec::new();
            let mut last_direction: Option<PortDirection> = None;
            let mut last_data_type: Option<DataType> = None;
            let mut last_net_type: Option<NetType> = None;
            let mut last_var_kw = false;
            loop {
                if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                    break;
                }
                let mut port = self.parse_ansi_port();
                let direction_was_explicit = port.direction.is_some();
                if port.direction.is_none() && last_direction.is_some() {
                    port.direction = last_direction;
                }
                if port.data_type.is_none() && last_data_type.is_some() && !direction_was_explicit {
                    port.data_type = last_data_type.clone();
                }
                if port.net_type.is_none() && last_net_type.is_some() && !direction_was_explicit {
                    port.net_type = last_net_type;
                }
                // §23.2.2.3: `output var a, b` — b continues the SAME port
                // declaration and is a variable too. `var` carried across the
                // comma like the data type; without this b registered as an
                // untyped default net.
                if !port.var_kw && last_var_kw && !direction_was_explicit {
                    port.var_kw = true;
                }
                if port.direction.is_some() {
                    last_direction = port.direction;
                }
                if port.data_type.is_some() {
                    last_data_type = port.data_type.clone();
                }
                if port.net_type.is_some() {
                    last_net_type = port.net_type;
                }
                last_var_kw = port.var_kw;
                // §23.2.2.4: only an input port takes a default value; an
                // inout is a net.
                if crate::strict_checks()
                    && port.direction == Some(PortDirection::Inout)
                    && let Some(d) = &port.default
                {
                    self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                        format!(
                            "inout port '{}' cannot have a default value (IEEE 1800-2017 §23.2.2.4)",
                            port.name.name
                        ),
                        d.span,
                    ));
                }
                ports.push(port);
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::RParen);
            PortList::Ansi(ports)
        } else {
            let mut names = Vec::new();
            let null_port = |names: &Vec<Identifier>, span| crate::ast::Identifier {
                name: format!("__xz_null_port_{}", names.len()),
                span,
            };
            loop {
                if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                    break;
                }
                // §23.2.2.1 null port — `(a, , b)` / `(a,, b)` is legal: the
                // position exists but is unnamed. Synthesize a placeholder
                // name so ordered instantiation keeps positional alignment;
                // nothing in the body can bind it, so a connection landing on
                // this slot is dropped, matching the LRM's "connection to a
                // null port is ignored".
                if self.at(TokenKind::Comma) {
                    let sp = self.current().span;
                    names.push(null_port(&names, sp));
                    self.bump(); // consume the comma standing in for the port
                    if self.at(TokenKind::RParen) {
                        names.push(null_port(&names, sp));
                    }
                    continue;
                }
                // §23.2.2.1 port expressions: `.name(expr)`, an unnamed
                // concatenation `{a, b}` or a select `a[7:0]`. Lowered by the
                // module declaration once the body declares the signals.
                if self.at(TokenKind::Dot) {
                    self.bump();
                    let name = self.parse_identifier();
                    self.expect(TokenKind::LParen);
                    if self.at(TokenKind::RParen) {
                        names.push(null_port(&names, name.span));
                    } else {
                        let e = self.parse_expression();
                        self.port_exprs.push((names.len(), e));
                        names.push(name);
                    }
                    self.expect(TokenKind::RParen);
                } else if self.at(TokenKind::LBrace)
                    || (self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket)
                {
                    let e = self.parse_expression();
                    let span = e.span;
                    self.port_exprs.push((names.len(), e));
                    names.push(crate::ast::Identifier {
                        name: format!("__xz_port_expr_{}", names.len()),
                        span,
                    });
                } else {
                    names.push(self.parse_identifier());
                }
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
                // A trailing `, )` leaves one more null port.
                if self.at(TokenKind::RParen) {
                    let sp = self.current().span;
                    names.push(null_port(&names, sp));
                }
            }
            self.expect(TokenKind::RParen);
            PortList::NonAnsi(names)
        }
    }

    /// §23.2.2.1: lower the port expressions of a non-ANSI header
    /// (`.b(a[2:1])`, `{a, b}`, `a[7:0]`) to plain ports. Each becomes a port
    /// as wide as its expression, joined to the signals it names by a
    /// continuous assignment (driving them for an input, reading them for an
    /// output). Those signals stop being ports and keep their declared type
    /// as nets or variables.
    fn lower_port_expressions(
        &mut self,
        ports: &PortList,
        items: &mut Vec<ModuleItem>,
        exprs: Vec<(usize, Expression)>,
    ) {
        if exprs.is_empty() {
            return;
        }
        let PortList::NonAnsi(names) = ports else {
            return;
        };
        let plain: Vec<String> = names
            .iter()
            .enumerate()
            .filter(|(i, _)| !exprs.iter().any(|(j, _)| j == i))
            .map(|(_, n)| n.name.clone())
            .collect();
        let mut demoted = Vec::new();
        for (idx, e) in exprs {
            let port = names[idx].clone();
            if let Err(msg) = Self::lower_port_expression(&port, &e, &plain, items, &mut demoted) {
                self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                    format!(
                        "unsupported port expression for port '{}': {msg} \
                         (IEEE 1800-2017 §23.2.2.1)",
                        port.name
                    ),
                    e.span,
                ));
            }
        }
        // Port declarations whose every name moved to a net or variable.
        items
            .retain(|it| !matches!(it, ModuleItem::PortDeclaration(d) if d.declarators.is_empty()));
    }

    fn lower_port_expression(
        port: &Identifier,
        e: &Expression,
        plain: &[String],
        items: &mut Vec<ModuleItem>,
        demoted: &mut Vec<(String, PortDirection, DataType)>,
    ) -> Result<(), String> {
        let span = e.span;
        let num = |v: i64| {
            Expression::new(
                ExprKind::Number(NumberLiteral::Integer {
                    size: None,
                    signed: true,
                    base: NumberBase::Decimal,
                    value: v.to_string(),
                    cached_val: std::cell::Cell::new(None),
                }),
                span,
            )
        };
        let bin = |op, l: Expression, r: Expression| {
            Expression::new(
                ExprKind::Binary {
                    op,
                    left: Box::new(l),
                    right: Box::new(r),
                },
                span,
            )
        };
        // |l - r| + 1
        let range_width = |l: &Expression, r: &Expression| {
            Expression::new(
                ExprKind::Conditional {
                    condition: Box::new(bin(BinaryOp::Geq, l.clone(), r.clone())),
                    then_expr: Box::new(bin(BinaryOp::Sub, l.clone(), r.clone())),
                    else_expr: Box::new(bin(BinaryOp::Sub, r.clone(), l.clone())),
                },
                span,
            )
        };
        // The signals named by the expression, each with the width of its
        // part when that is a select.
        fn leaves<'e>(
            e: &'e Expression,
            out: &mut Vec<(
                &'e Identifier,
                Option<(&'e Expression, &'e Expression, RangeKind)>,
                bool,
            )>,
        ) -> Result<(), String> {
            let base = |x: &'e Expression| -> Result<&'e Identifier, String> {
                match &x.kind {
                    ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                        Ok(&h.path[0].name)
                    }
                    _ => {
                        Err("only names, selects of names and concatenations are supported".into())
                    }
                }
            };
            match &e.kind {
                ExprKind::Concatenation(parts) => {
                    for p in parts {
                        leaves(p, out)?;
                    }
                }
                ExprKind::Index { expr, .. } => out.push((base(expr)?, None, true)),
                ExprKind::RangeSelect {
                    expr,
                    kind,
                    left,
                    right,
                } => out.push((base(expr)?, Some((left, right, *kind)), false)),
                _ => out.push((base(e)?, None, false)),
            }
            Ok(())
        }
        let mut parts = Vec::new();
        leaves(e, &mut parts)?;
        let decl_of = |items: &[ModuleItem], n: &str| {
            items.iter().find_map(|it| match it {
                ModuleItem::PortDeclaration(d)
                    if d.declarators.iter().any(|v| v.name.name == n) =>
                {
                    Some(d.clone())
                }
                _ => None,
            })
        };
        // A separate net or variable declaration completing the port.
        let completion = |items: &[ModuleItem], n: &str| {
            items.iter().find_map(|it| match it {
                ModuleItem::NetDeclaration(d) if d.declarators.iter().any(|v| v.name.name == n) => {
                    Some(d.data_type.clone())
                }
                ModuleItem::DataDeclaration(d)
                    if d.declarators.iter().any(|v| v.name.name == n) =>
                {
                    Some(d.data_type.clone())
                }
                _ => None,
            })
        };
        let packed = |dt: &DataType| match dt {
            DataType::Implicit { dimensions, .. } | DataType::IntegerVector { dimensions, .. } => {
                Some(dimensions.clone())
            }
            _ => None,
        };
        let mut direction = None;
        let mut width: Option<Expression> = None;
        for (id, sel, bit) in &parts {
            if plain.contains(&id.name) || id.name == port.name {
                return Err(format!("'{}' is also a port of its own", id.name));
            }
            // A signal already demoted by an earlier port expression keeps
            // the direction and type it was declared with.
            let (dir, dt) = match demoted.iter().find(|(n, ..)| *n == id.name) {
                Some((_, dir, dt)) => (*dir, dt.clone()),
                None => {
                    let d = decl_of(items, &id.name).ok_or_else(|| {
                        format!("'{}' has no input or output declaration", id.name)
                    })?;
                    (d.direction, d.data_type)
                }
            };
            if dir == PortDirection::Inout || direction.is_some_and(|d| d != dir) {
                return Err("an inout or mixed-direction port expression".into());
            }
            direction = Some(dir);
            let w = if *bit {
                num(1)
            } else if let Some((l, r, kind)) = sel {
                match kind {
                    RangeKind::Constant => bin(BinaryOp::Add, range_width(l, r), num(1)),
                    _ => (*r).clone(),
                }
            } else {
                // The range may sit on the completing declaration instead.
                let own = packed(&dt);
                let dims = match own {
                    Some(d) if !d.is_empty() => d,
                    _ => completion(items, &id.name)
                        .as_ref()
                        .and_then(packed)
                        .or(own)
                        .ok_or_else(|| format!("'{}' has no vector type", id.name))?,
                };
                match dims.as_slice() {
                    [] => num(1),
                    [PackedDimension::Range { left, right, .. }] => {
                        bin(BinaryOp::Add, range_width(left, right), num(1))
                    }
                    _ => return Err(format!("'{}' has more than one packed dimension", id.name)),
                }
            };
            width = Some(match width {
                None => w,
                Some(acc) => bin(BinaryOp::Add, acc, w),
            });
        }
        let (Some(direction), Some(width)) = (direction, width) else {
            return Err("an empty port expression".into());
        };
        // The named signals leave the port list: each keeps its declared type
        // as a net or variable unless another declaration already completes it.
        for (id, _, _) in &parts {
            if demoted.iter().any(|(n, ..)| *n == id.name) {
                continue;
            }
            let completed = completion(items, &id.name).is_some();
            let Some(at) = items.iter().position(|it| {
                matches!(it, ModuleItem::PortDeclaration(d)
                    if d.declarators.iter().any(|v| v.name.name == id.name))
            }) else {
                continue;
            };
            let ModuleItem::PortDeclaration(d) = &mut items[at] else {
                continue;
            };
            let pos = d.declarators.iter().position(|v| v.name.name == id.name);
            let v = d.declarators.remove(pos.unwrap_or_default());
            let (net_type, data_type, dspan) = (d.net_type, d.data_type.clone(), d.span);
            demoted.push((id.name.clone(), direction, data_type.clone()));
            if completed {
                continue;
            }
            let is_var = net_type.is_none() && !matches!(data_type, DataType::Implicit { .. });
            // In the port declaration's place, so later items see it.
            items.insert(
                at + 1,
                if is_var {
                    ModuleItem::DataDeclaration(DataDeclaration {
                        const_kw: false,
                        var_kw: false,
                        lifetime: None,
                        data_type,
                        declarators: vec![v],
                        span: dspan,
                    })
                } else {
                    ModuleItem::NetDeclaration(NetDeclaration {
                        net_type: net_type.unwrap_or(NetType::Wire),
                        strength: None,
                        data_type,
                        delay: None,
                        delay_fall: None,
                        delay_off: None,
                        declarators: vec![NetDeclarator {
                            name: v.name,
                            dimensions: v.dimensions,
                            init: None,
                            span: v.span,
                        }],
                        span: dspan,
                    })
                },
            );
        }
        // The new port follows the declarations of the signals it joins
        // (their ranges may use parameters declared before them).
        let joined = |it: &ModuleItem| {
            let named = |n: &str| parts.iter().any(|(id, ..)| id.name == n);
            match it {
                ModuleItem::PortDeclaration(d) => d.declarators.iter().any(|v| named(&v.name.name)),
                ModuleItem::NetDeclaration(d) => d.declarators.iter().any(|v| named(&v.name.name)),
                ModuleItem::DataDeclaration(d) => d.declarators.iter().any(|v| named(&v.name.name)),
                _ => false,
            }
        };
        let at = items.iter().rposition(joined).map_or(0, |i| i + 1);
        let port_ref = Expression::new(
            ExprKind::Ident(HierarchicalIdentifier {
                root: None,
                path: vec![HierPathSegment {
                    name: port.clone(),
                    selects: Vec::new(),
                }],
                span,
                cached_signal_id: std::cell::Cell::new(None),
                cached_resolved_name: std::cell::OnceCell::new(),
            }),
            span,
        );
        items.insert(
            at,
            ModuleItem::PortDeclaration(PortDeclaration {
                direction,
                net_type: None,
                data_type: DataType::Implicit {
                    signing: None,
                    dimensions: vec![PackedDimension::Range {
                        left: Box::new(bin(BinaryOp::Sub, width, num(1))),
                        right: Box::new(num(0)),
                        span,
                    }],
                    span,
                },
                declarators: vec![crate::ast::stmt::VarDeclarator {
                    name: port.clone(),
                    dimensions: Vec::new(),
                    init: None,
                    span,
                }],
                span,
            }),
        );
        let (lhs, rhs) = match direction {
            PortDirection::Input => (e.clone(), port_ref),
            _ => (port_ref, e.clone()),
        };
        items.push(ModuleItem::ContinuousAssign(ContinuousAssign {
            strength: None,
            delay: None,
            delay_fall: None,
            delay_off: None,
            assignments: vec![(lhs, rhs)],
            span,
        }));
        Ok(())
    }

    fn parse_ansi_port(&mut self) -> AnsiPort {
        let start = self.current().span.start;
        let direction = self.parse_optional_direction();
        let net_type = self.parse_optional_net_type();
        let var_kw = self.eat(TokenKind::KwVar).is_some();
        // LRM §25.9: `virtual <iface_t> [.<modport>] <name>` — module
        // port form. Mirror `parse_function_ports` so a child module
        // can take a virtual interface as a port for vif pass-through.
        let data_type = if self.at(TokenKind::KwVirtual)
            && (self.peek_kind() == TokenKind::KwInterface
                || self.peek_kind() == TokenKind::Identifier)
        {
            self.bump(); // virtual
            if self.at(TokenKind::KwInterface) {
                self.bump();
            }
            let if_name = self.parse_identifier();
            let modport = if self.at(TokenKind::Dot) {
                self.bump();
                Some(self.parse_identifier())
            } else {
                None
            };
            Some(DataType::Interface {
                name: if_name,
                modport,
                type_args: Vec::new(),
                span: self.span_from(start),
            })
        } else if self.at(TokenKind::KwInterface) {
            // §25.3.2 generic interface port: `interface [.<modport>] <name>`.
            self.bump(); // interface
            let modport = if self.at(TokenKind::Dot) {
                self.bump();
                Some(self.parse_identifier())
            } else {
                None
            };
            Some(DataType::Interface {
                name: crate::ast::Identifier {
                    name: "interface".to_string(),
                    span: self.span_from(start),
                },
                modport,
                type_args: Vec::new(),
                span: self.span_from(start),
            })
        } else if self.is_data_type_keyword() {
            Some(self.parse_data_type())
        } else if self.at(TokenKind::LBracket) {
            let dimensions = self.parse_packed_dimensions();
            Some(DataType::Implicit {
                signing: None,
                dimensions,
                span: self.span_from(start),
            })
        } else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Dot {
            let if_name = self.parse_identifier();
            self.expect(TokenKind::Dot);
            let mp_name = self.parse_identifier();
            Some(DataType::Interface {
                name: if_name,
                modport: Some(mp_name),
                type_args: Vec::new(),
                span: self.span_from(start),
            })
        } else if self.at(TokenKind::Identifier)
            && matches!(
                self.peek_kind(),
                TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash
            )
        {
            Some(self.parse_data_type())
        } else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket {
            // AMBIGUOUS: `typedef_t [7:0] name` (a type with packed dims)
            // vs `name[t-1:0]` (an implicit-typed port whose NAME carries an
            // unpacked dimension — `output v0vJ[t-1:0],`). Look past the
            // balanced bracket groups: an IDENTIFIER there means the first
            // token was a type; a comma/`)`/`=` means it was the port name.
            let mut p = self.pos + 1;
            while self
                .tokens
                .get(p)
                .is_some_and(|t| t.kind == TokenKind::LBracket)
            {
                let mut depth = 1;
                p += 1;
                while depth > 0 {
                    match self.tokens.get(p).map(|t| t.kind) {
                        Some(TokenKind::LBracket) => depth += 1,
                        Some(TokenKind::RBracket) => depth -= 1,
                        Some(_) => {}
                        None => break,
                    }
                    p += 1;
                }
            }
            if self.tokens.get(p).is_some_and(|t| {
                matches!(t.kind, TokenKind::Identifier | TokenKind::EscapedIdentifier)
            }) {
                Some(self.parse_data_type())
            } else {
                None
            }
        } else {
            None
        };
        // An ANSI `wreal` port carries a real and declares no data type of
        // its own. Same reason as the net path: fill one in so the width
        // and real-ness queries downstream have something to read. A ranged
        // one (`input wreal [3:0] p`) reaches here as an `Implicit` with
        // packed dimensions and is rejected by the shared helper.
        let wreal_span = self.span_from(start);
        let data_type = match (net_type, data_type) {
            (Some(NetType::Wreal), None) => Some(DataType::Real {
                kind: RealType::Real,
                span: wreal_span,
            }),
            (Some(nt), Some(dt)) => Some(self.wreal_data_type(nt, dt, wreal_span)),
            (_, dt) => dt,
        };
        let mut dimensions = if data_type.is_some() {
            self.parse_unpacked_dimensions()
        } else {
            Vec::new()
        };
        let name = self.parse_identifier();
        dimensions.extend(self.parse_unpacked_dimensions());
        let default = if self.eat(TokenKind::Assign).is_some() {
            Some(self.parse_expression())
        } else {
            None
        };
        AnsiPort {
            attrs: Vec::new(),
            direction,
            net_type,
            var_kw,
            data_type,
            name,
            dimensions,
            default,
            span: self.span_from(start),
        }
    }

    pub(super) fn parse_module_items(&mut self) -> Vec<ModuleItem> {
        let end_tokens = [
            TokenKind::KwEndmodule,
            TokenKind::KwEndinterface,
            TokenKind::KwEndprogram,
            TokenKind::Eof,
        ];
        let mut items = Vec::new();
        while !self.at_any(&end_tokens) {
            let before = self.pos;
            if let Some(item) = self.parse_module_item() {
                self.hide_let_names_of_item(&item);
                items.push(item);
                items.append(&mut self.pending_module_items);
            } else if self.pos == before {
                // parse_module_item returned None WITHOUT consuming anything —
                // genuinely stuck; report and force progress. A None that DID
                // advance is a deliberate parse-accept/skip (specparam,
                // interconnect, …) and must not be flagged as an error.
                self.error(format!("unexpected: {:?}", self.current().text));
                self.bump();
            }
        }
        items
    }

    pub(super) fn parse_module_item(&mut self) -> Option<ModuleItem> {
        let start = self.current().span.start;
        let mut is_extern = false;
        let mut is_virtual = false;
        let mut _is_static = false;
        loop {
            match self.current_kind() {
                TokenKind::KwExtern => {
                    self.bump();
                    is_extern = true;
                }
                TokenKind::KwVirtual
                    if self.peek_kind() == TokenKind::KwFunction
                        || self.peek_kind() == TokenKind::KwTask
                        || self.peek_kind() == TokenKind::KwClass =>
                {
                    self.bump();
                    is_virtual = true;
                }
                TokenKind::KwStatic
                    if self.peek_kind() == TokenKind::KwFunction
                        || self.peek_kind() == TokenKind::KwTask =>
                {
                    self.bump();
                    _is_static = true;
                }
                _ => break,
            }
        }

        match self.current_kind() {
            // §23.4 nested module declaration — parsed whole and hoisted to
            // the definitions map by the top-level pipeline.
            TokenKind::KwModule | TokenKind::KwMacromodule => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a module declaration is not allowed inside a generate block \
                         (IEEE 1800-2017 §23.4, §27)",
                    );
                }
                return Some(ModuleItem::NestedModule(Box::new(
                    self.parse_module_declaration(),
                )));
            }
            // `timeunit 1ns / 10ps;` / `timeprecision …;` inside a module —
            // already parsed at top-level via Description::TimeunitsDecl;
            // accept and discard inside modules too (LRM allows both).
            TokenKind::KwTimeunit | TokenKind::KwTimeprecision => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a timeunit or timeprecision declaration is not allowed inside a \
                         generate block (IEEE 1800-2017 §3.14.2.2, §27)",
                    );
                }
                Some(ModuleItem::TimeunitsDecl(
                    self.parse_timeunits_declaration(),
                ))
            }
            // A `program … endprogram` block nested inside a module (LRM §24.3).
            // A program shares the enclosing scope for cross-references (its
            // `initial`/`final` blocks drive the module's nets), so inline its
            // items as an (unnamed) generate region — they elaborate directly in
            // the module scope, which is exactly the sharing the LRM prescribes
            // for the common testbench-in-module form.
            TokenKind::KwProgram => {
                let prog = self.parse_program_declaration();
                Some(ModuleItem::GenerateRegion(GenerateRegion {
                    items: prog.items,
                    span: prog.span,
                }))
            }
            // Deprecated hierarchical parameter override `defparam path.p = e, …;`
            // (LRM §23.10.1). Parse each `<hier_path> = <expr>` pair so
            // elaboration can apply the override; on any malformed pair, fall
            // back to consuming to the semicolon so the item stream survives.
            TokenKind::KwDefparam => {
                self.bump();
                let mut assigns: Vec<(Expression, Expression)> = Vec::new();
                loop {
                    let lhs = self.parse_expression();
                    if self.eat(TokenKind::Assign).is_none() {
                        break;
                    }
                    let rhs = self.parse_expression();
                    assigns.push((lhs, rhs));
                    if self.eat(TokenKind::Comma).is_some() {
                        continue;
                    }
                    break;
                }
                // Recover to the terminating semicolon regardless.
                while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                let _ = self.eat(TokenKind::Semicolon);
                if assigns.is_empty() {
                    None
                } else {
                    Some(ModuleItem::Defparam(assigns))
                }
            }
            // Elaboration-time system tasks at module-item level: $error, $warning,
            // $info, $fatal — typically inside a `STATIC_ASSERT` macro expansion
            // (`generate if (!(cond)) $error msg; endgenerate`). Parse and discard.
            TokenKind::SystemIdentifier => {
                self.bump();
                if self.at(TokenKind::LParen) {
                    let _ = self.parse_call_args();
                } else {
                    // No-paren form: $error msg;  where msg is an expression.
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::Null)
            }
            TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef => {
                let dir = self
                    .parse_optional_direction()
                    .unwrap_or(PortDirection::Input);
                let nt = self.parse_optional_net_type();
                // §23.2.2.1: `input var x;` — optional `var` keyword.
                let has_var = self.eat(TokenKind::KwVar).is_some();
                // §23.2.2.3: an `inout` port shall be of a net type — `inout var`
                // is illegal (a variable cannot have multiple drivers / be
                // bidirectionally connected).
                if has_var && dir == PortDirection::Inout {
                    self.error("an 'inout' port cannot be declared 'var' (must be a net type)");
                }
                let dt = if self.is_data_type_keyword()
                    || self.at(TokenKind::KwSigned)
                    || self.at(TokenKind::KwUnsigned)
                {
                    self.parse_data_type()
                } else if self.at(TokenKind::Identifier)
                    && matches!(
                        self.peek_kind(),
                        TokenKind::Identifier
                            | TokenKind::DoubleColon
                            | TokenKind::Hash
                            | TokenKind::LBracket
                    )
                {
                    self.parse_data_type()
                } else if self.at(TokenKind::LBracket) {
                    let dimensions = self.parse_packed_dimensions();
                    DataType::Implicit {
                        signing: None,
                        dimensions,
                        span: self.span_from(start),
                    }
                } else {
                    DataType::Implicit {
                        signing: None,
                        dimensions: Vec::new(),
                        span: self.span_from(start),
                    }
                };
                let wreal_span = self.span_from(start);
                let dt = match nt {
                    Some(n) => self.wreal_data_type(n, dt, wreal_span),
                    None => dt,
                };
                let decls = self.parse_var_declarator_list();
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::PortDeclaration(PortDeclaration {
                    direction: dir,
                    net_type: nt,
                    data_type: dt,
                    declarators: decls,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwWire
            | TokenKind::KwTri
            | TokenKind::KwWand
            | TokenKind::KwWor
            | TokenKind::KwSupply0
            | TokenKind::KwSupply1
            | TokenKind::KwTriand
            | TokenKind::KwTrior
            | TokenKind::KwTri0
            | TokenKind::KwTri1
            | TokenKind::KwTrireg
            | TokenKind::KwUwire
            | TokenKind::KwWreal => Some(ModuleItem::NetDeclaration(self.parse_net_declaration())),
            // §14.3: `global clocking …` — consume the `global` qualifier and
            // reuse the clocking-block parse via the KwClocking arm below.
            TokenKind::KwGlobal if self.peek_kind() == TokenKind::KwClocking => {
                self.bump();
                self.parse_module_item()
            }
            // §6.20.5 specparam — parse-accept (xezim doesn't model specify
            // timing); consume through the terminating ';'.
            TokenKind::KwSpecparam => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a specparam declaration is not allowed inside a generate block \
                         (IEEE 1800-2017 §6.20.5, §27)",
                    );
                }
                // §6.20.5: a specparam is a module-scoped elaboration-time
                // constant, and §23.3.3 makes it reachable by hierarchical
                // name. The whole declaration used to be skipped to the `;`
                // and DROPPED, so `u_child.SPEC_DELAY` resolved to nothing and
                // read x while the sibling localparam read fine. Parse it as a
                // localparam instead: it then lands in the same constant table
                // that hierarchical resolution already searches.
                //
                // Backtracks to the old whole-declaration skip for any shape
                // this parser does not model — notably `specparam PATHPULSE$ =
                // ...`, whose name is not a plain identifier — so an exotic
                // form is still tolerated rather than becoming a hard error.
                let start_pos = self.pos;
                let diag_len = self.diagnostics.len();
                self.bump(); // specparam
                let mut decl = self.parse_parameter_declaration();
                if self.at(TokenKind::Semicolon) && self.diagnostics.len() == diag_len {
                    self.bump(); // ;
                    decl.local = true;
                    Some(ModuleItem::LocalparamDeclaration(decl))
                } else {
                    self.diagnostics.truncate(diag_len);
                    self.pos = start_pos;
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
                    self.expect(TokenKind::Semicolon);
                    None
                }
            }
            // §6.6.8 interconnect net — a REAL declaration (it used to be
            // consumed to ';' and dropped, so the name looked undeclared,
            // §6.10 gave it a 1-bit implicit wire, and a nettype port
            // truncated onto it while the diagnostic blamed a missing
            // declaration). Parsed like any net; the elaborator registers it
            // and adopts the connected formal's type.
            TokenKind::KwInterconnect => {
                Some(ModuleItem::NetDeclaration(self.parse_net_declaration()))
            }
            TokenKind::KwInterface if self.peek_kind() == TokenKind::KwClass => {
                // `interface class Name; ... endclass` — treat as a class decl.
                self.bump();
                let mut class = self.parse_class_declaration();
                class.virtual_kw = is_virtual;
                class.is_interface = true;
                Some(ModuleItem::ClassDeclaration(class))
            }
            _ if self.is_data_type_keyword() => {
                Some(ModuleItem::DataDeclaration(self.parse_data_declaration()))
            }
            TokenKind::KwVar
            | TokenKind::KwConst
            | TokenKind::KwStatic
            | TokenKind::KwAutomatic => {
                Some(ModuleItem::DataDeclaration(self.parse_data_declaration()))
            }
            TokenKind::KwParameter => Some(ModuleItem::ParameterDeclaration(
                self.parse_parameter_decl_stmt(),
            )),
            TokenKind::KwLocalparam => Some(ModuleItem::LocalparamDeclaration(
                self.parse_parameter_decl_stmt(),
            )),
            TokenKind::KwTypedef => Some(ModuleItem::TypedefDeclaration(
                self.parse_typedef_declaration(),
            )),
            TokenKind::KwAlways
            | TokenKind::KwAlways_comb
            | TokenKind::KwAlways_ff
            | TokenKind::KwAlways_latch => {
                let kind = match self.bump().kind {
                    TokenKind::KwAlways_comb => AlwaysKind::AlwaysComb,
                    TokenKind::KwAlways_ff => AlwaysKind::AlwaysFf,
                    TokenKind::KwAlways_latch => AlwaysKind::AlwaysLatch,
                    _ => AlwaysKind::Always,
                };
                // Skip optional inline attribute spec `(* ... *)` between
                // `always_*` and the body. The preprocessor only strips
                // standalone-line attributes; inline ones reach the parser.
                self.skip_optional_attribute();
                let mut stmt = self.parse_statement();
                if matches!(kind, AlwaysKind::Always | AlwaysKind::AlwaysFf) {
                    Self::infer_procedural_assertion_clocks(&mut stmt);
                }
                Some(ModuleItem::AlwaysConstruct(AlwaysConstruct {
                    kind,
                    stmt,
                    span: self.span_from(start),
                    gen_scope: String::new(),
                }))
            }
            TokenKind::KwInitial => {
                self.bump();
                let st = self.parse_statement();
                Some(ModuleItem::InitialConstruct(InitialConstruct {
                    stmt: st,
                    span: self.span_from(start),
                    gen_scope: String::new(),
                }))
            }
            TokenKind::KwFinal => {
                self.bump();
                let st = self.parse_statement();
                Some(ModuleItem::FinalConstruct(FinalConstruct {
                    stmt: st,
                    span: self.span_from(start),
                }))
            }
            // §10.11 `alias a = b [= c ...];` — carried whole; elaboration
            // unifies the named nets onto one signal.
            TokenKind::KwAlias => {
                self.bump();
                let mut terms: Vec<Expression> = vec![self.parse_expression()];
                while self.at(TokenKind::Assign) {
                    self.bump();
                    terms.push(self.parse_expression());
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::AliasDecl(terms))
            }
            TokenKind::KwAssign => {
                self.bump();
                // Optional drive_strength `(strong1, weak0)` (§10.3.1).
                // Retained as a comma-joined keyword list so `%v` (§21.2.1.5)
                // can report the driven strength; otherwise unmodelled.
                let mut strength: Option<String> = None;
                if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
                    self.bump();
                    let mut parts: Vec<String> = Vec::new();
                    while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                        let t = self.bump();
                        if t.kind != TokenKind::Comma {
                            parts.push(t.text.clone());
                        }
                    }
                    self.expect(TokenKind::RParen);
                    strength = Some(parts.join(","));
                }
                let mut delay_fall = None;
                let mut delay_off = None;
                let delay = if self.eat(TokenKind::Hash).is_some() {
                    if self.eat(TokenKind::LParen).is_some() {
                        // §10.3.3 `#(rise, fall[, turnoff])`: up to three
                        // comma-separated delays.
                        let expr = self.parse_expression();
                        if self.eat(TokenKind::Comma).is_some() {
                            delay_fall = Some(self.parse_expression());
                            if self.eat(TokenKind::Comma).is_some() {
                                delay_off = Some(self.parse_expression());
                            }
                        }
                        self.expect(TokenKind::RParen);
                        Some(expr)
                    } else {
                        Some(self.parse_expression())
                    }
                } else {
                    None
                };
                let mut asgns = Vec::new();
                loop {
                    let l = self.parse_expression();
                    self.expect(TokenKind::Assign);
                    let r = self.parse_expression();
                    asgns.push((l, r));
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ContinuousAssign(ContinuousAssign {
                    strength,
                    delay,
                    delay_fall,
                    delay_off,
                    assignments: asgns,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwGenerate => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "generate regions do not nest: `generate` is not allowed inside a \
                         generate region or block (IEEE 1800-2017 §27.3)",
                    );
                }
                self.bump();
                self.generate_depth += 1;
                let items = self.parse_module_items_until(TokenKind::KwEndgenerate);
                self.generate_depth -= 1;
                self.expect(TokenKind::KwEndgenerate);
                Some(ModuleItem::GenerateRegion(GenerateRegion {
                    items,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwGenvar => {
                self.bump();
                let mut names = Vec::new();
                loop {
                    names.push(self.parse_identifier());
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::GenvarDeclaration(GenvarDeclaration {
                    names,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwFunction => {
                if is_extern {
                    Some(ModuleItem::FunctionDeclaration(
                        self.parse_function_prototype(),
                    ))
                } else {
                    Some(ModuleItem::FunctionDeclaration(
                        self.parse_function_declaration(),
                    ))
                }
            }
            TokenKind::KwTask => {
                if is_extern {
                    Some(ModuleItem::TaskDeclaration(self.parse_task_prototype()))
                } else {
                    Some(ModuleItem::TaskDeclaration(self.parse_task_declaration()))
                }
            }
            TokenKind::KwImport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(ModuleItem::DPIImport(self.parse_dpi_import()))
                } else {
                    Some(ModuleItem::ImportDeclaration(
                        self.parse_import_declaration(),
                    ))
                }
            }
            TokenKind::KwExport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(ModuleItem::DPIExport(self.parse_dpi_export()))
                } else {
                    self.bump();
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
                    self.expect(TokenKind::Semicolon);
                    Some(ModuleItem::Null)
                }
            }
            TokenKind::KwClass => {
                let mut class = self.parse_class_declaration();
                class.virtual_kw = is_virtual;
                Some(ModuleItem::ClassDeclaration(class))
            }
            TokenKind::KwConstraint => {
                // Out-of-class constraint definition: `constraint ClassName::name { ... }`.
                // Record the qualified name; discard the body.
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
                        items.push(self.parse_constraint_item());
                    }
                    self.expect(TokenKind::RBrace);
                } else if self.at(TokenKind::Semicolon) {
                    self.bump();
                }
                Some(ModuleItem::OutOfClassConstraint {
                    class_name,
                    constraint_name,
                    items,
                })
            }
            TokenKind::KwVirtual => {
                if self.peek_kind() == TokenKind::KwInterface {
                    Some(self.parse_identifier_starting_item())
                } else if self.peek_kind() == TokenKind::Identifier {
                    // §25.9: a MODULE-scope virtual-interface variable —
                    // `virtual req_if #(4).driver rd;`. Bumping past `virtual`
                    // and re-parsing (the old behavior) made `req_if #(4)`
                    // look like a parameterized INSTANTIATION, which then
                    // choked on `.driver`. parse_data_declaration starts at
                    // the `virtual` keyword and handles `#(...)` and
                    // `.modport` through parse_data_type.
                    Some(ModuleItem::DataDeclaration(self.parse_data_declaration()))
                } else {
                    self.bump();
                    self.parse_module_item()
                }
            }
            // IEEE 1800-2023 §23.11: `bind` inside a module body. Parsed into a
            // `ModuleItem::Bind`, which elaboration applies the same way as a
            // compilation-unit bind (appending the bound instantiation to every
            // instance of <target>). Unhandled selectors skip-parse to `Null`.
            TokenKind::KwBind => {
                self.bump(); // bind
                match self.try_bind_directive() {
                    Some(b) => Some(ModuleItem::Bind(b)),
                    None => Some(ModuleItem::Null),
                }
            }
            TokenKind::KwModport => {
                let start = self.current().span.start;
                self.bump();
                let mut items = Vec::new();
                loop {
                    let istart = self.current().span.start;
                    let name = self.parse_identifier();
                    self.expect(TokenKind::LParen);
                    let mut ports = Vec::new();
                    // LRM §25.5: a direction keyword applies to ALL following
                    // comma-separated members until the next direction keyword
                    // (`output a, b, c, input d` → a/b/c output, d input). Carry
                    // the last-seen direction; a bare member inherits it instead
                    // of defaulting to input (which mis-marked outputs as inputs,
                    // wrongly rejecting writes — veer-el2 / rsd).
                    let mut last_dir = PortDirection::Input;
                    loop {
                        if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                            break;
                        }
                        let pstart = self.current().span.start;
                        // IEEE 1800-2023 §25.5: `modport <name> ( clocking <cb> )`
                        // — a modport_clocking_declaration. We record it as a
                        // synthetic Input port whose name is the clocking
                        // block; downstream consumers that don't understand
                        // clocking still see *something* there.
                        if self.eat(TokenKind::KwClocking).is_some() {
                            let cb_name = self.parse_identifier();
                            ports.push(ModportPort {
                                direction: PortDirection::Input,
                                name: cb_name,
                                span: self.span_from(pstart),
                                expr: None,
                            });
                        } else if self.at(TokenKind::KwImport) || self.at(TokenKind::KwExport) {
                            // §25.5 modport import/export of a task/function.
                            // Record the imported NAME as a synthetic Input port
                            // (so it parses and stays reachable via the interface),
                            // then skip any method prototype up to the separator.
                            self.bump(); // import / export
                            if self.at(TokenKind::Identifier) {
                                let name = self.parse_identifier();
                                ports.push(ModportPort {
                                    direction: PortDirection::Input,
                                    name,
                                    span: self.span_from(pstart),
                                    expr: None,
                                });
                            }
                            while !self.at(TokenKind::Comma)
                                && !self.at(TokenKind::RParen)
                                && !self.at(TokenKind::Eof)
                            {
                                self.bump();
                            }
                        } else {
                            if let Some(d) = self.parse_optional_direction() {
                                last_dir = d;
                            }
                            // §25.5.4 modport expression: `.b(word[7:0])` —
                            // the member `b` stands for an expression over
                            // the interface's signals.
                            if self.eat(TokenKind::Dot).is_some() {
                                let port_name = self.parse_identifier();
                                self.expect(TokenKind::LParen);
                                let e = self.parse_expression();
                                self.expect(TokenKind::RParen);
                                ports.push(ModportPort {
                                    direction: last_dir,
                                    name: port_name,
                                    span: self.span_from(pstart),
                                    expr: Some(e),
                                });
                            } else {
                                let port_name = self.parse_identifier();
                                ports.push(ModportPort {
                                    direction: last_dir,
                                    name: port_name,
                                    span: self.span_from(pstart),
                                    expr: None,
                                });
                            }
                        }
                        if self.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen);
                    items.push(ModportItem {
                        name,
                        ports,
                        span: self.span_from(istart),
                    });
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ModportDeclaration(ModportDeclaration {
                    items,
                    span: self.span_from(start),
                }))
            }
            // IEEE 1800-2023 §14.3 — clocking block. We now capture the
            // direction-tagged signals into a real ClockingDeclaration so
            // the elaborator can register `clocking_blocks[<name>]` and the
            // identifier validator accepts `<cb>.<sig>` references. Body
            // statements beyond `<dir> [type] <name> (, <name>)*` are
            // skipped (default skew, etc. — rich grammar not modelled).
            TokenKind::KwClocking => {
                let start = self.current().span.start;
                self.bump();
                let cb_name =
                    if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
                        Some(self.parse_identifier())
                    } else {
                        None
                    };
                // LRM §14.3 clock event: `@(posedge <sig>)` — capture
                // the signal identifier so the simulator can snapshot
                // its inputs before each clock edge. Falls back to the
                // legacy skip path for forms we don't recognise.
                let mut clock_signal_id: Option<crate::ast::Identifier> = None;
                let mut clock_edge: Option<crate::ast::stmt::Edge> = None;
                if self.at(TokenKind::At) {
                    self.bump();
                    if self.at(TokenKind::LParen) {
                        self.bump();
                        if self.eat(TokenKind::KwPosedge).is_some() {
                            clock_edge = Some(crate::ast::stmt::Edge::Posedge);
                        } else if self.eat(TokenKind::KwNegedge).is_some() {
                            clock_edge = Some(crate::ast::stmt::Edge::Negedge);
                        } else if self.eat(TokenKind::KwEdge).is_some() {
                            clock_edge = Some(crate::ast::stmt::Edge::Edge);
                        }
                        if self.at(TokenKind::Identifier) {
                            clock_signal_id = Some(self.parse_identifier());
                        }
                        // Skip to matching close-paren (handles
                        // `(posedge clk iff cond)` etc.).
                        let mut d = 1i32;
                        while !self.at(TokenKind::Eof) && d > 0 {
                            match self.current_kind() {
                                TokenKind::LParen => d += 1,
                                TokenKind::RParen => {
                                    d -= 1;
                                    if d == 0 {
                                        self.bump();
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            self.bump();
                        }
                    }
                }
                self.expect(TokenKind::Semicolon);
                let items: Vec<crate::ast::stmt::Statement> = Vec::new();
                let mut signals: Vec<ClockingSignal> = Vec::new();
                let mut default_input_skew: Option<crate::ast::expr::Expression> = None;
                let mut default_output_skew: Option<crate::ast::expr::Expression> = None;
                while !self.at(TokenKind::KwEndclocking) && !self.at(TokenKind::Eof) {
                    // `default input #d output #d;` (§14.4) — capture the skew
                    // expressions; anything unrecognized is skipped to the `;`
                    // so the signal-list pass below stays in sync.
                    if self.at(TokenKind::KwDefault) {
                        self.bump();
                        loop {
                            let dir_in = self.at(TokenKind::KwInput);
                            let dir_out = self.at(TokenKind::KwOutput);
                            if !dir_in && !dir_out {
                                break;
                            }
                            self.bump();
                            // `clocking_skew ::= edge_identifier [delay_control]`
                            if matches!(
                                self.current_kind(),
                                TokenKind::KwNegedge | TokenKind::KwPosedge | TokenKind::KwEdge
                            ) {
                                self.bump();
                            }
                            if self.at(TokenKind::Hash) {
                                self.bump();
                                let skew = self.parse_clocking_skew_value();
                                if dir_in {
                                    default_input_skew = skew;
                                } else {
                                    default_output_skew = skew;
                                }
                            }
                        }
                        while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                            self.bump();
                        }
                        if self.at(TokenKind::Semicolon) {
                            self.bump();
                        }
                        continue;
                    }
                    match self.current_kind() {
                        TokenKind::KwInput
                        | TokenKind::KwOutput
                        | TokenKind::KwInout
                        | TokenKind::KwRef => {
                            let sstart = self.current().span.start;
                            let direction = self
                                .parse_optional_direction()
                                .unwrap_or(PortDirection::Input);
                            // Optional `#delay` skew specifier (§14.4) —
                            // captured per-signal; `#1step`/opaque forms → None.
                            let mut sig_skew: Option<crate::ast::expr::Expression> = None;
                            // `clocking_skew ::= edge_identifier [delay_control]`
                            if matches!(
                                self.current_kind(),
                                TokenKind::KwNegedge | TokenKind::KwPosedge | TokenKind::KwEdge
                            ) {
                                self.bump();
                            }
                            if self.at(TokenKind::Hash) {
                                self.bump();
                                sig_skew = self.parse_clocking_skew_value();
                            }
                            if self.is_data_type_keyword()
                                || (self.at(TokenKind::Identifier)
                                    && self.peek_kind() == TokenKind::Identifier)
                            {
                                let _ = self.parse_data_type();
                            }
                            loop {
                                if self.at(TokenKind::Identifier) {
                                    let id = self.parse_identifier();
                                    // §14.3 signal renaming: `input alias = expr;`
                                    let bound_to = if self.eat(TokenKind::Assign).is_some() {
                                        Some(self.parse_expression())
                                    } else {
                                        None
                                    };
                                    signals.push(ClockingSignal {
                                        direction,
                                        name: id,
                                        skew: sig_skew.clone(),
                                        bound_to,
                                        span: self.span_from(sstart),
                                    });
                                }
                                if self.eat(TokenKind::Comma).is_none() {
                                    break;
                                }
                            }
                            // Skip anything we don't understand up to `;`.
                            while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                                self.bump();
                            }
                            if self.at(TokenKind::Semicolon) {
                                self.bump();
                            }
                        }
                        _ => {
                            self.bump();
                        }
                    }
                }
                self.expect(TokenKind::KwEndclocking);
                let endlabel = if self.eat(TokenKind::Colon).is_some() {
                    Some(self.parse_identifier())
                } else {
                    None
                };
                let id = cb_name.unwrap_or_else(|| Identifier {
                    name: "default".to_string(),
                    span: self.span_from(start),
                });
                Some(ModuleItem::ClockingDeclaration(ClockingDeclaration {
                    name: id,
                    clock_signal: clock_signal_id,
                    clock_edge,
                    default_input_skew,
                    default_output_skew,
                    is_default: false,
                    signals,
                    items,
                    endlabel,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwAssert | TokenKind::KwAssume | TokenKind::KwCover => {
                Some(ModuleItem::AssertionItem(self.parse_assertion_statement()))
            }
            TokenKind::KwProperty => {
                let start = self.current().span.start;
                self.bump();
                let name = self.parse_identifier();
                let (ports, local_ports) = if self.at(TokenKind::LParen) {
                    self.parse_sva_port_names()
                } else {
                    (Vec::new(), Vec::new())
                };
                self.expect(TokenKind::Semicolon);
                // §16.10: assertion-local variable declarations.
                let mut decls = self.parse_sva_local_declarations();
                // LRM §16.6 — capture the property body when it matches
                // the common `[@(<event>)] [disable iff (<expr>)] <expr>;`
                // shape. Re-uses the assertion parser's clock-event capture
                // (an `SvaClocked { clock, body }` wrapper). Properties not
                // matching this shape fall back to the legacy token-skip
                // path so the parser stays resilient.
                let bstart = self.current().span.start;
                let save_pos = self.pos;
                let save_diag = self.diagnostics.len();
                let clocked = self.at(TokenKind::At);
                let clock = if clocked {
                    self.bump(); // @
                    Some(self.parse_sva_clock_event())
                } else {
                    None
                };
                // §16.12: optional `disable iff (<expr>)` after the clocking
                // event, before the property expression; kept as
                // `Binary{SvaDisableIff, guard, body}`.
                let disable_guard =
                    if self.at(TokenKind::KwDisable) && self.peek_kind() == TokenKind::KwIff {
                        self.bump(); // disable
                        self.bump(); // iff
                        let _ = self.eat(TokenKind::LParen);
                        let g = self.parse_expression();
                        let _ = self.eat(TokenKind::RParen);
                        Some(g)
                    } else {
                        None
                    };
                let body_expr = if clocked || !self.at(TokenKind::KwEndproperty) {
                    self.in_sva_seq = true;
                    let mut body = self.parse_expression();
                    self.in_sva_seq = false;
                    // An unclocked body is taken only when it parses cleanly
                    // (a default clocking or an inferred clock supplies the
                    // clock); otherwise the token-skip path below runs.
                    if !clocked
                        && !(self.diagnostics.len() == save_diag && self.at(TokenKind::Semicolon))
                    {
                        self.diagnostics.truncate(save_diag);
                        self.pos = save_pos;
                        None
                    } else {
                        let _ = self.eat(TokenKind::Semicolon);
                        Self::sva_bind_local_formals(&local_ports, &mut decls, &mut body);
                        let assignable = Self::sva_assignable_names(&decls, &ports);
                        self.check_sva_match_assignments(&body, &assignable);
                        let body = Self::sva_wrap_locals(std::mem::take(&mut decls), body);
                        let body = if let Some(g) = disable_guard {
                            let span = body.span;
                            Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::SvaDisableIff,
                                    left: Box::new(g),
                                    right: Box::new(body),
                                },
                                span,
                            )
                        } else {
                            body
                        };
                        Some(match clock {
                            Some((clk, clk_edge, clk_iff)) => Expression::new(
                                ExprKind::SvaClocked {
                                    clock: Box::new(clk),
                                    edge: clk_edge,
                                    iff: clk_iff.map(Box::new),
                                    body: Box::new(body),
                                },
                                self.span_from(bstart),
                            ),
                            None => body,
                        })
                    }
                } else {
                    None
                };
                while !self.at(TokenKind::KwEndproperty) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                self.expect(TokenKind::KwEndproperty);
                let endlabel = self.parse_end_label();
                let items = Vec::new();
                Some(ModuleItem::PropertyDeclaration(PropertyDeclaration {
                    name,
                    ports,
                    items,
                    body: body_expr,
                    endlabel,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwSequence => {
                let start = self.current().span.start;
                self.bump();
                let name = self.parse_identifier();
                let (ports, local_ports) = if self.at(TokenKind::LParen) {
                    self.parse_sva_port_names()
                } else {
                    (Vec::new(), Vec::new())
                };
                self.expect(TokenKind::Semicolon);
                // §16.10: assertion-local variable declarations.
                let mut decls = self.parse_sva_local_declarations();
                // LRM §16.5 — capture the sequence body when it matches
                // the common `@(<event>) <expr>;` shape, mirroring the
                // property-decl path. Other shapes (raw `##N` chains)
                // fall back to the token-skip path.
                let body_expr = if self.at(TokenKind::At) {
                    let bstart = self.current().span.start;
                    self.bump();
                    let (clk, clk_edge, clk_iff) = self.parse_sva_clock_event();
                    self.in_sva_seq = true;
                    let mut body = self.parse_expression();
                    self.in_sva_seq = false;
                    let _ = self.eat(TokenKind::Semicolon);
                    Self::sva_bind_local_formals(&local_ports, &mut decls, &mut body);
                    let assignable = Self::sva_assignable_names(&decls, &ports);
                    self.check_sva_match_assignments(&body, &assignable);
                    let body = Self::sva_wrap_locals(std::mem::take(&mut decls), body);
                    Some(Expression::new(
                        ExprKind::SvaClocked {
                            clock: Box::new(clk),
                            edge: clk_edge,
                            iff: clk_iff.map(Box::new),
                            body: Box::new(body),
                        },
                        self.span_from(bstart),
                    ))
                } else if !self.at(TokenKind::KwEndsequence) {
                    // Unclocked body (`sequence s; a ##1 b; endsequence`):
                    // parse it speculatively so a named sequence used INSIDE
                    // a property (`a |=> s`) has a body to expand. Any shape
                    // the expression parser does not cover backtracks to the
                    // token-skip path below, exactly as before.
                    let save_pos = self.pos;
                    let save_diag = self.diagnostics.len();
                    self.in_sva_seq = true;
                    let mut body = self.parse_expression();
                    self.in_sva_seq = false;
                    if self.diagnostics.len() == save_diag && self.at(TokenKind::Semicolon) {
                        self.bump();
                        Self::sva_bind_local_formals(&local_ports, &mut decls, &mut body);
                        let assignable = Self::sva_assignable_names(&decls, &ports);
                        self.check_sva_match_assignments(&body, &assignable);
                        Some(Self::sva_wrap_locals(std::mem::take(&mut decls), body))
                    } else {
                        self.diagnostics.truncate(save_diag);
                        self.pos = save_pos;
                        None
                    }
                } else {
                    None
                };
                while !self.at(TokenKind::KwEndsequence) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                self.expect(TokenKind::KwEndsequence);
                let endlabel = self.parse_end_label();
                let items = Vec::new();
                Some(ModuleItem::SequenceDeclaration(SequenceDeclaration {
                    name,
                    ports,
                    items,
                    body: body_expr,
                    endlabel,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwCovergroup => Some(ModuleItem::CovergroupDeclaration(
                self.parse_covergroup_declaration(),
            )),
            TokenKind::KwClocking => {
                let start = self.current().span.start;
                self.bump();
                let name = if self.at(TokenKind::Identifier) {
                    Some(self.parse_identifier())
                } else {
                    None
                };
                if self.at(TokenKind::At) {
                    let _ = self.parse_event_control();
                }
                self.expect(TokenKind::Semicolon);
                let mut items = Vec::new();
                let mut signals = Vec::new();
                while !self.at(TokenKind::KwEndclocking) && !self.at(TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::KwInput
                        | TokenKind::KwOutput
                        | TokenKind::KwInout
                        | TokenKind::KwRef => {
                            let sstart = self.current().span.start;
                            let direction = self
                                .parse_optional_direction()
                                .unwrap_or(PortDirection::Input);
                            // Optional data type inside clocking declaration.
                            if self.is_data_type_keyword()
                                || (self.at(TokenKind::Identifier)
                                    && self.peek_kind() == TokenKind::Identifier)
                            {
                                let _ = self.parse_data_type();
                            }
                            loop {
                                if self.at(TokenKind::Identifier) {
                                    let id = self.parse_identifier();
                                    signals.push(ClockingSignal {
                                        direction,
                                        name: id,
                                        skew: None,
                                        bound_to: None,
                                        span: self.span_from(sstart),
                                    });
                                }
                                if self.eat(TokenKind::Comma).is_none() {
                                    break;
                                }
                            }
                            self.expect(TokenKind::Semicolon);
                        }
                        _ => items.push(self.parse_statement()),
                    }
                }
                self.expect(TokenKind::KwEndclocking);
                let endlabel = self.parse_end_label();
                // ClockingDeclaration struct needs an Option<Identifier> for name if we want to store it accurately,
                // but for now let's just use a dummy identifier if it's missing.
                let id = name.unwrap_or_else(|| Identifier {
                    name: "default".to_string(),
                    span: self.span_from(start),
                });
                Some(ModuleItem::ClockingDeclaration(ClockingDeclaration {
                    name: id,
                    clock_signal: None,
                    clock_edge: None,
                    default_input_skew: None,
                    default_output_skew: None,
                    is_default: false,
                    signals,
                    items,
                    endlabel,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwDefault => {
                self.bump();
                if self.at(TokenKind::KwClocking) {
                    // §14.12 STANDALONE designation `default clocking <name>;`
                    // — names an ALREADY-declared block rather than declaring
                    // one. Detect by the `;` right after the identifier (a
                    // declaration always has `@(...)` or at least a body) and
                    // emit a marker: an empty, clock-less ClockingDeclaration
                    // with is_default set, which the elaborator folds into the
                    // existing same-named block. Without this the parser
                    // recursed into the block form and ran to EOF looking for
                    // `endclocking`.
                    if matches!(self.peek_kind(), TokenKind::Identifier)
                        && self.peek_kind_n(2) == TokenKind::Semicolon
                    {
                        self.bump(); // clocking
                        let name = self.parse_identifier();
                        self.expect(TokenKind::Semicolon);
                        return Some(ModuleItem::ClockingDeclaration(ClockingDeclaration {
                            name,
                            clock_signal: None,
                            clock_edge: None,
                            default_input_skew: None,
                            default_output_skew: None,
                            is_default: true,
                            signals: Vec::new(),
                            items: Vec::new(),
                            endlabel: None,
                            span: self.span_from(start),
                        }));
                    }
                    // §14.11: mark the block so procedural `##N` knows which
                    // clocking block to synchronize to.
                    let mut item = self.parse_module_item(); // recurse to handle clocking
                    if let Some(ModuleItem::ClockingDeclaration(cd)) = item.as_mut() {
                        cd.is_default = true;
                    }
                    item
                } else if self.at(TokenKind::KwDisable) {
                    // §16.15 `default disable iff <expr>;`: the default
                    // disable condition of every concurrent assertion in this
                    // module, interface or generate scope that has no
                    // `disable iff` of its own. Kept as a marker assertion
                    // item, `$sva_default_disable(<expr>)`, which reaches the
                    // simulator in the same scope as the scope's assertions.
                    self.bump(); // disable
                    let _ = self.eat(TokenKind::KwIff);
                    let guard = self.parse_expression();
                    self.expect(TokenKind::Semicolon);
                    let span = self.span_from(start);
                    Some(ModuleItem::AssertionItem(
                        crate::ast::stmt::AssertionStatement {
                            kind: crate::ast::stmt::AssertionKind::Assert,
                            expr: Expression::new(
                                ExprKind::SystemCall {
                                    name: "$sva_default_disable".to_string(),
                                    args: vec![guard],
                                },
                                span,
                            ),
                            action: None,
                            else_action: None,
                            is_property: true,
                            is_sequence: false,
                            deferred: None,
                            label: None,
                            procedural: false,
                            inferred_clock: None,
                            span,
                        },
                    ))
                } else {
                    None
                }
            }
            TokenKind::KwIf => {
                let s = self.current().span.start;
                Some(self.parse_generate_if(s))
            }
            TokenKind::KwCase => {
                let s = self.current().span.start;
                Some(self.parse_generate_case(s))
            }
            TokenKind::KwChecker => {
                let start = self.current().span.start;
                self.bump();
                let name = self.parse_identifier();
                let ports = self.parse_port_list();
                self.expect(TokenKind::Semicolon);
                self.push_let_scope();
                let items = self.parse_module_items_until(TokenKind::KwEndchecker);
                self.pop_let_scope();
                self.expect(TokenKind::KwEndchecker);
                let endlabel = self.parse_end_label();
                Some(ModuleItem::CheckerDeclaration(CheckerDeclaration {
                    name,
                    ports,
                    items,
                    endlabel,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwLet => Some(ModuleItem::LetDeclaration(self.parse_let_declaration())),
            TokenKind::KwNettype => {
                let start = self.current().span.start;
                self.bump();
                let data_type = self.parse_data_type();
                let name = self.parse_identifier();
                let resolver = if self.eat(TokenKind::KwWith).is_some() {
                    Some(self.parse_identifier())
                } else {
                    None
                };
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::NettypeDeclaration(NettypeDeclaration {
                    data_type,
                    name,
                    resolver,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwFor => {
                let s = self.current().span.start;
                self.bump();
                self.expect(TokenKind::LParen);
                // Parse init: genvar i = 0 or i = 0
                let has_genvar = self.eat(TokenKind::KwGenvar).is_some();
                let var_name = if self.at(TokenKind::Identifier) {
                    let n = self.current().text.clone();
                    if !has_genvar {
                        let span = self.current().span;
                        self.plain_loop_vars.push(Identifier {
                            name: n.clone(),
                            span,
                        });
                    }
                    self.bump();
                    n
                } else {
                    String::new()
                };
                self.expect(TokenKind::Assign);
                let init_expr = self.parse_expression();
                let init_val = match &init_expr.kind {
                    ExprKind::Number(NumberLiteral::Integer { value, base, .. }) => {
                        let r = match base {
                            NumberBase::Binary => 2,
                            NumberBase::Octal => 8,
                            NumberBase::Hex => 16,
                            NumberBase::Decimal => 10,
                        };
                        i64::from_str_radix(&value.replace('_', ""), r).unwrap_or(0)
                    }
                    _ => 0,
                };
                self.expect(TokenKind::Semicolon);
                // Parse condition
                let cond = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                // Parse increment: allow both expression steps (`i++`) and
                // assignment-style steps (`i = i + 1`), which are common in
                // generate-for loops in real RTL.
                let incr = {
                    let expr = self.parse_lvalue_or_expr();
                    if self.at(TokenKind::Assign)
                        || self.at_any(&[
                            TokenKind::PlusAssign,
                            TokenKind::MinusAssign,
                            TokenKind::StarAssign,
                            TokenKind::SlashAssign,
                            TokenKind::PercentAssign,
                            TokenKind::AndAssign,
                            TokenKind::OrAssign,
                            TokenKind::XorAssign,
                            TokenKind::ShiftLeftAssign,
                            TokenKind::ShiftRightAssign,
                            TokenKind::ArithShiftLeftAssign,
                            TokenKind::ArithShiftRightAssign,
                        ])
                    {
                        let op_kind = self.current().kind.clone();
                        self.bump();
                        let rhs = self.parse_expression();
                        let span = self.span_from(s);
                        let rvalue = match op_kind {
                            TokenKind::PlusAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Add,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::MinusAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Sub,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::StarAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Mul,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::SlashAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Div,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::PercentAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Mod,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::AndAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::BitAnd,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::OrAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::BitOr,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::XorAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::BitXor,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ShiftLeftAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ShiftLeft,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ShiftRightAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ShiftRight,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ArithShiftLeftAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ArithShiftLeft,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ArithShiftRightAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ArithShiftRight,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            _ => Expression::new(
                                ExprKind::AssignExpr {
                                    lvalue: Box::new(expr.clone()),
                                    rvalue: Box::new(rhs),
                                },
                                span,
                            ),
                        };
                        match op_kind {
                            TokenKind::Assign => rvalue,
                            _ => Expression::new(
                                ExprKind::AssignExpr {
                                    lvalue: Box::new(expr),
                                    rvalue: Box::new(rvalue),
                                },
                                span,
                            ),
                        }
                    } else {
                        expr
                    }
                };
                self.expect(TokenKind::RParen);
                let (items, name) = self.parse_generate_branch_items_named();
                Some(ModuleItem::GenerateFor(GenerateFor {
                    var: var_name,
                    init_val,
                    init: Some(init_expr),
                    cond,
                    incr,
                    items,
                    name,
                    span: self.span_from(s),
                }))
            }
            TokenKind::KwAnd
            | TokenKind::KwNand
            | TokenKind::KwOr
            | TokenKind::KwNor
            | TokenKind::KwXor
            | TokenKind::KwXnor
            | TokenKind::KwBuf
            | TokenKind::KwNot
            | TokenKind::KwBufif0
            | TokenKind::KwBufif1
            | TokenKind::KwNotif0
            | TokenKind::KwNotif1
            | TokenKind::KwNmos
            | TokenKind::KwPmos
            | TokenKind::KwCmos
            | TokenKind::KwRnmos
            | TokenKind::KwRpmos
            | TokenKind::KwRcmos
            | TokenKind::KwTran
            | TokenKind::KwRtran
            | TokenKind::KwTranif0
            | TokenKind::KwTranif1
            | TokenKind::KwRtranif0
            | TokenKind::KwRtranif1
            | TokenKind::KwPullup
            | TokenKind::KwPulldown => Some(ModuleItem::GateInstantiation(
                self.parse_gate_instantiation(),
            )),
            TokenKind::KwSpecify => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a specify block is not allowed inside a generate block \
                         (IEEE 1800-2017 §30, §27)",
                    );
                }
                // §30 specify block: module paths (every §30.4 form) into
                // SpecifyPaths so the elaborator can model their delays, plus
                // the §31 timing checks and `specparam`s. Anything else
                // (`pulsestyle_*`, `showcancelled`, ...) is skipped to the
                // next `;`.
                self.bump();
                let mut paths = Vec::new();
                let mut delayed_nets: Vec<(String, String)> = Vec::new();
                let mut timing_checks = Vec::new();
                while !self.at(TokenKind::KwEndspecify) && !self.at(TokenKind::Eof) {
                    if matches!(
                        self.current_kind(),
                        TokenKind::LParen | TokenKind::KwIf | TokenKind::KwIfnone
                    ) {
                        if let Some(p) = self.try_parse_specify_path() {
                            paths.push(p);
                            continue;
                        }
                    }
                    if self.at(TokenKind::SystemIdentifier)
                        && Self::is_timing_check_task(self.current().text.as_str())
                    {
                        let check_pos = self.pos;
                        let check = self.parse_timing_check();
                        // §15.6 negative-timing-check tasks carry `delayed_reference`
                        // / `delayed_data` OUTPUT nets that the cell's functional
                        // path uses — extract those so the elaborator can drive them.
                        if Self::is_timing_check_name(self.tokens[check_pos].text.as_str()) {
                            let end_pos = self.pos;
                            self.pos = check_pos;
                            self.parse_timing_check_delayed_nets(&mut delayed_nets);
                            self.pos = end_pos;
                        }
                        timing_checks.extend(check);
                        continue;
                    }
                    // §31.2 a specparam declared in the specify block is a
                    // module-scoped constant, like one at module level: emit
                    // it through the module-level specparam handling.
                    if self.at(TokenKind::KwSpecparam) {
                        let item = self.parse_module_item();
                        self.pending_module_items.extend(item);
                        continue;
                    }
                    // Unrecognized specify item: skip to (and past) the next ';'.
                    self.skip_to_semi();
                }
                self.expect(TokenKind::KwEndspecify);
                // A delayed net is typically named as the delayed_data/ref of
                // MANY checks on the same source — dedup so it gets exactly one
                // zero-delay driver (redundant identical drivers churn settle).
                delayed_nets.sort();
                delayed_nets.dedup();
                Some(ModuleItem::SpecifyBlock(SpecifyBlock {
                    paths,
                    delayed_nets,
                    timing_checks,
                    span: self.span_from(start),
                }))
            }
            TokenKind::Identifier | TokenKind::EscapedIdentifier => {
                Some(self.parse_identifier_starting_item())
            }
            TokenKind::Semicolon => {
                self.bump();
                Some(ModuleItem::Null)
            }
            TokenKind::Directive => {
                self.bump();
                self.parse_module_item()
            }
            TokenKind::KwBegin => {
                let s = self.current().span.start;
                let items = self.parse_generate_branch_items();
                Some(ModuleItem::GenerateRegion(GenerateRegion {
                    items,
                    span: self.span_from(s),
                }))
            }
            _ => None,
        }
    }

    fn parse_net_declaration(&mut self) -> NetDeclaration {
        let start = self.current().span.start;
        let net_type = self.parse_optional_net_type().unwrap_or(NetType::Wire);
        // §10.3.1: optional drive_strength `(strong1, weak0)` on a net
        // declaration with a continuous assignment, e.g.
        // `wire (strong1, weak0) w = a & b;`. xezim doesn't model strengths;
        // consume the group when it opens with a strength keyword.
        if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
            self.bump();
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                self.bump();
            }
            self.expect(TokenKind::RParen);
        }
        // §6.9.2: optional `vectored` / `scalared` charge/drive qualifier
        // between the net type and the (optional) range — `tri1 vectored [15:0] a;`.
        if self.at(TokenKind::KwVectored) || self.at(TokenKind::KwScalared) {
            self.bump();
        }
        // §10.3.3: optional net delay `wire #10 w;` / `wire #(d1,d2) w;`.
        // The LRM places it after the data type (below); this position is
        // accepted too.
        let mut delay = self.parse_net_delay();
        let data_type = if self.is_data_type_keyword() {
            self.parse_data_type()
        }
        // User-defined typedef net type — `wire dword foo;`,
        // `wire word_t a, b;`, `wire pkg::t x;`, `wire t#(8) x;`. A bare
        // identifier followed by another identifier / `::` / `#` is a type
        // name, not the net name (mirrors the port path). `[` is excluded
        // to preserve `wire foo [3:0];` (unpacked net array named foo).
        else if self.at(TokenKind::Identifier)
            && matches!(
                self.peek_kind(),
                TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash
            )
        {
            self.parse_data_type()
        }
        // `wire word_t [1:0][7:0] x;` — identifier followed by packed dims
        // and THEN another identifier is a typedef'd net with packed
        // dimensions (§6.7.1). Distinguish from `wire foo [3:0];` (a net
        // NAMED foo with an unpacked dim) by looking past the balanced
        // bracket groups: an identifier there means the first token was a
        // type. This form used to be a hard parse error ("expected
        // Semicolon"), because the type name was taken as the declarator.
        else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket && {
            let mut p = self.pos + 1;
            while p < self.tokens.len() && self.tokens[p].kind == TokenKind::LBracket {
                let mut depth = 0usize;
                while p < self.tokens.len() {
                    match self.tokens[p].kind {
                        TokenKind::LBracket => depth += 1,
                        TokenKind::RBracket => {
                            depth -= 1;
                            if depth == 0 {
                                p += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    p += 1;
                }
            }
            p < self.tokens.len() && self.tokens[p].kind == TokenKind::Identifier
        } {
            self.parse_data_type()
        } else if self.at(TokenKind::LBracket) {
            let dimensions = self.parse_packed_dimensions();
            DataType::Implicit {
                signing: None,
                dimensions,
                span: self.span_from(start),
            }
        } else {
            DataType::Implicit {
                signing: None,
                dimensions: Vec::new(),
                span: self.span_from(start),
            }
        };
        let wreal_span = self.span_from(start);
        let data_type = self.wreal_data_type(net_type, data_type, wreal_span);
        // §6.7: `net_type data_type_or_implicit [delay3] list_of_net_decl_assignments`
        // — `wire [5:0] #1 w = a + b;`.
        if delay.0.is_none() {
            delay = self.parse_net_delay();
        }
        let declarators = self.parse_net_declarator_list();
        self.expect(TokenKind::Semicolon);
        let (delay, delay_fall, delay_off) = delay;
        NetDeclaration {
            net_type,
            strength: None,
            data_type,
            delay,
            delay_fall,
            delay_off,
            declarators,
            span: self.span_from(start),
        }
    }

    /// Optional `#d` / `#(rise[, fall[, turn-off]])` net delay (§6.7.1,
    /// §28.16), as (rise, fall, turn-off). A min:typ:max value keeps typ.
    fn parse_net_delay(&mut self) -> (Option<Expression>, Option<Expression>, Option<Expression>) {
        if self.eat(TokenKind::Hash).is_none() {
            return (None, None, None);
        }
        if self.eat(TokenKind::LParen).is_none() {
            return (Some(self.parse_delay_value()), None, None);
        }
        let mut vals: Vec<Expression> = Vec::new();
        loop {
            let first = self.parse_expression();
            vals.push(self.parse_mintypmax_rest(first));
            if vals.len() == 3 || self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        let mut depth = 1i32;
        while depth > 0 && !self.at(TokenKind::Eof) {
            match self.current_kind() {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => depth -= 1,
                _ => {}
            }
            self.bump();
        }
        let mut it = vals.into_iter();
        (it.next(), it.next(), it.next())
    }

    fn parse_net_declarator_list(&mut self) -> Vec<NetDeclarator> {
        let mut decls = Vec::new();
        loop {
            let start = self.current().span.start;
            let name = self.parse_identifier();
            let dimensions = self.parse_unpacked_dimensions();
            let init = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else {
                None
            };
            decls.push(NetDeclarator {
                name,
                dimensions,
                init,
                span: self.span_from(start),
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        decls
    }

    fn parse_gate_instantiation(&mut self) -> GateInstantiation {
        let start = self.current().span.start;
        let gate_type = match self.current_kind() {
            TokenKind::KwAnd => GateType::And,
            TokenKind::KwNand => GateType::Nand,
            TokenKind::KwOr => GateType::Or,
            TokenKind::KwNor => GateType::Nor,
            TokenKind::KwXor => GateType::Xor,
            TokenKind::KwXnor => GateType::Xnor,
            TokenKind::KwBuf => GateType::Buf,
            TokenKind::KwNot => GateType::Not,
            TokenKind::KwBufif0 => GateType::Bufif0,
            TokenKind::KwBufif1 => GateType::Bufif1,
            TokenKind::KwNotif0 => GateType::Notif0,
            TokenKind::KwNotif1 => GateType::Notif1,
            TokenKind::KwNmos => GateType::Nmos,
            TokenKind::KwPmos => GateType::Pmos,
            TokenKind::KwCmos => GateType::Cmos,
            TokenKind::KwRnmos => GateType::Rnmos,
            TokenKind::KwRpmos => GateType::Rpmos,
            TokenKind::KwRcmos => GateType::Rcmos,
            TokenKind::KwTran => GateType::Tran,
            TokenKind::KwRtran => GateType::Rtran,
            TokenKind::KwTranif0 => GateType::Tranif0,
            TokenKind::KwTranif1 => GateType::Tranif1,
            TokenKind::KwRtranif0 => GateType::Rtranif0,
            TokenKind::KwRtranif1 => GateType::Rtranif1,
            TokenKind::KwPullup => GateType::Pullup,
            TokenKind::KwPulldown => GateType::Pulldown,
            _ => GateType::And,
        };
        self.bump();
        // Optional drive_strength `(strong0, strong1)` / charge_strength
        // `(small)` / pull strength `(pull1)` (§28.4). xezim doesn't model
        // strengths; consume the group when it opens with a strength keyword.
        if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
            self.bump(); // (
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                self.bump();
            }
            self.expect(TokenKind::RParen);
        }
        // Optional `#(delay)` or `#delay` spec between the gate keyword and
        // the first instance: `buf #(D) name (...)`. §28.11: the list is
        // `(rise, fall, turn-off)` — capture rise AND fall (the turn-off value
        // is still skipped). Collapsing fall onto rise made every 1->0 edge
        // use the rise delay.
        let mut delay: Option<Expression> = None;
        let mut delay_fall: Option<Expression> = None;
        if self.eat(TokenKind::Hash).is_some() {
            if self.eat(TokenKind::LParen).is_some() {
                let rise = self.parse_expression();
                delay = Some(self.parse_mintypmax_rest(rise));
                if self.eat(TokenKind::Comma).is_some() {
                    let fall = self.parse_expression();
                    delay_fall = Some(self.parse_mintypmax_rest(fall));
                }
                let mut depth = 1;
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
                        _ => {
                            self.bump();
                        }
                    }
                }
            } else {
                delay = Some(self.parse_delay_value());
            }
        }
        let mut instances = Vec::new();
        loop {
            let istart = self.current().span.start;
            let name = if self.at(TokenKind::Identifier) {
                Some(self.parse_identifier())
            } else {
                None
            };
            let _dims = self.parse_unpacked_dimensions(); // Gates can have arrays too
            let mut terminals = Vec::new();
            self.expect(TokenKind::LParen);
            loop {
                terminals.push(self.parse_expression());
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::RParen);
            instances.push(GateInstance {
                name,
                terminals,
                span: self.span_from(istart),
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(TokenKind::Semicolon);
        GateInstantiation {
            gate_type,
            delay,
            delay_fall,
            instances,
            span: self.span_from(start),
        }
    }

    fn parse_generate_if(&mut self, start: usize) -> ModuleItem {
        let mut branches = Vec::new();
        let mut branch_labels = Vec::new();
        self.bump();
        self.expect(TokenKind::LParen);
        let cond = self.parse_expression();
        self.expect(TokenKind::RParen);
        let (items, label) = self.parse_generate_branch_items_named();
        branches.push((Some(cond), items));
        branch_labels.push(label);
        while self.eat(TokenKind::KwElse).is_some() {
            if self.at(TokenKind::KwIf) {
                self.bump();
                self.expect(TokenKind::LParen);
                let c = self.parse_expression();
                self.expect(TokenKind::RParen);
                let (items, label) = self.parse_generate_branch_items_named();
                branches.push((Some(c), items));
                branch_labels.push(label);
            } else {
                let (items, label) = self.parse_generate_branch_items_named();
                branches.push((None, items));
                branch_labels.push(label);
                break;
            }
        }
        ModuleItem::GenerateIf(GenerateIf {
            branches,
            branch_labels,
            span: self.span_from(start),
        })
    }

    fn parse_generate_case(&mut self, start: usize) -> ModuleItem {
        // case (selector)
        self.bump(); // consume `case`
        self.expect(TokenKind::LParen);
        let selector = self.parse_expression();
        self.expect(TokenKind::RParen);
        let mut arms: Vec<GenerateCaseArm> = Vec::new();
        while !self.at(TokenKind::KwEndcase) && !self.at(TokenKind::Eof) {
            // Either `default[:] generate-block` or `expr {, expr}: generate-block`.
            let mut values: Vec<crate::ast::expr::Expression> = Vec::new();
            if self.eat(TokenKind::KwDefault).is_some() {
                let _ = self.eat(TokenKind::Colon);
            } else {
                loop {
                    values.push(self.parse_expression());
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Colon);
            }
            let (items, label) = self.parse_generate_branch_items_named();
            arms.push(GenerateCaseArm {
                values,
                items,
                label,
            });
        }
        self.expect(TokenKind::KwEndcase);
        ModuleItem::GenerateCase(GenerateCase {
            selector,
            arms,
            span: self.span_from(start),
        })
    }

    fn parse_generate_branch_items(&mut self) -> Vec<ModuleItem> {
        self.parse_generate_branch_items_named().0
    }

    /// Parse the simple specify module path `( src => dst ) = ( d {, d} ) ;`
    /// (or `... = d ;`) with plain-identifier endpoints. Returns the path's
    /// first delay as its `delay`. Returns None and rewinds for any other
    /// form (edge-sensitive `( posedge a => ...)`, `*>`, conditional, bit-
    /// selected endpoints, timing checks) so the caller skips it.
    /// System-task names whose argument list carries `delayed_reference` /
    /// `delayed_data` output nets (IEEE 1364 §15.6).
    fn is_timing_check_name(name: &str) -> bool {
        matches!(
            name,
            "$setuphold" | "$recrem" | "$setup" | "$hold" | "$recovery" | "$removal"
        )
    }

    /// IEEE 1800-2017 §31 timing check system tasks.
    fn is_timing_check_task(name: &str) -> bool {
        matches!(
            name,
            "$setup"
                | "$hold"
                | "$setuphold"
                | "$recovery"
                | "$removal"
                | "$recrem"
                | "$skew"
                | "$timeskew"
                | "$fullskew"
                | "$period"
                | "$width"
                | "$nochange"
        )
    }

    /// Parse a §31 timing check `$name ( arg {, arg} ) ;` into its argument
    /// list, consuming through the `;`. Each argument is split out at the
    /// top-level commas and parsed on its own (see `parse_timing_check_arg`);
    /// an argument that does not parse becomes `None`, like an omitted one.
    /// Returns None (after skipping the item) when the list is malformed.
    fn parse_timing_check(&mut self) -> Option<TimingCheck> {
        let start = self.current().span.start;
        let name = self.bump().text;
        if !self.at(TokenKind::LParen) {
            self.skip_to_semi();
            return None;
        }
        self.bump();
        let mut ranges: Vec<(usize, usize)> = Vec::new();
        let mut arg_start = self.pos;
        let mut depth = 0i32;
        loop {
            match self.current_kind() {
                TokenKind::Eof | TokenKind::KwEndspecify => return None,
                TokenKind::Semicolon if depth == 0 => {
                    self.bump();
                    return None;
                }
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen if depth == 0 => {
                    ranges.push((arg_start, self.pos));
                    self.bump();
                    break;
                }
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::Comma if depth == 0 => {
                    ranges.push((arg_start, self.pos));
                    self.bump();
                    arg_start = self.pos;
                    continue;
                }
                _ => {}
            }
            self.bump();
        }
        self.eat(TokenKind::Semicolon);
        let span = self.span_from(start);
        let args = ranges
            .into_iter()
            .map(|(a, b)| Self::parse_timing_check_arg(&self.tokens[a..b]))
            .collect();
        Some(TimingCheck { name, args, span })
    }

    /// One timing check argument (§31.2 `timing_check_event` or a plain
    /// expression): `[posedge | negedge | edge [descriptors]] terminal
    /// [&&& condition]`. `&&&` lexes as `&&` followed by `&`. A limit may be a
    /// `min:typ:max` triplet, resolved by `+mindelays/+typdelays/+maxdelays`.
    fn parse_timing_check_arg(toks: &[crate::lexer::token::Token]) -> Option<TimingCheckArg> {
        if toks.is_empty() {
            return None;
        }
        let text = Self::tokens_source_text(toks);
        let mut i = 0usize;
        let mut edges = None;
        match toks[0].kind {
            TokenKind::KwPosedge => {
                edges = Some(TIMING_POSEDGE);
                i = 1;
            }
            TokenKind::KwNegedge => {
                edges = Some(TIMING_NEGEDGE);
                i = 1;
            }
            TokenKind::KwEdge => {
                i = 1;
                if toks.get(1).map(|t| t.kind) == Some(TokenKind::LBracket) {
                    let close = toks.iter().position(|t| t.kind == TokenKind::RBracket)?;
                    let mut mask = 0u16;
                    for desc in toks[2..close].split(|t| t.kind == TokenKind::Comma) {
                        let d: String = desc.iter().map(|t| t.text.to_ascii_lowercase()).collect();
                        let level = |c: char| match c {
                            '0' => Some(0u8),
                            '1' => Some(1u8),
                            'x' | 'z' => Some(2u8),
                            _ => None,
                        };
                        let mut cs = d.chars();
                        let (Some(from), Some(to), None) = (
                            cs.next().and_then(level),
                            cs.next().and_then(level),
                            cs.next(),
                        ) else {
                            return None;
                        };
                        if from == to {
                            return None;
                        }
                        mask |= timing_edge_bit(from, to);
                    }
                    edges = Some(mask);
                    i = close + 1;
                } else {
                    edges = Some(TIMING_POSEDGE | TIMING_NEGEDGE);
                }
            }
            _ => {}
        }
        let mut depth = 0i32;
        let mut split = None;
        for k in i..toks.len() {
            match toks[k].kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::LogAnd
                    if depth == 0 && toks.get(k + 1).map(|t| t.kind) == Some(TokenKind::BitAnd) =>
                {
                    split = Some(k);
                    break;
                }
                _ => {}
            }
        }
        let (expr_toks, cond) = match split {
            Some(k) => (&toks[i..k], Some(Self::parse_token_expr(&toks[k + 2..])?)),
            None => (&toks[i..], None),
        };
        let expr = Self::parse_token_expr(Self::select_mintypmax(expr_toks))?;
        Some(TimingCheckArg {
            edges,
            expr,
            cond,
            text,
        })
    }

    /// Pick the `+mindelays/+typdelays/+maxdelays` element of a `min:typ:max`
    /// token run (optionally parenthesized); any other run is returned whole.
    fn select_mintypmax(toks: &[crate::lexer::token::Token]) -> &[crate::lexer::token::Token] {
        let inner = if toks.len() >= 2
            && toks[0].kind == TokenKind::LParen
            && toks[toks.len() - 1].kind == TokenKind::RParen
        {
            &toks[1..toks.len() - 1]
        } else {
            toks
        };
        let mut depth = 0i32;
        let mut colons = Vec::new();
        for (k, t) in inner.iter().enumerate() {
            match t.kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::Question if depth == 0 => return toks,
                TokenKind::Colon if depth == 0 => colons.push(k),
                _ => {}
            }
        }
        if colons.len() != 2 {
            return toks;
        }
        match crate::delay_select() {
            0 => &inner[..colons[0]],
            2 => &inner[colons[1] + 1..],
            _ => &inner[colons[0] + 1..colons[1]],
        }
    }

    /// Parse a complete expression from a token run with a private parser, so
    /// a run that is not one expression is rejected without diagnostics.
    fn parse_token_expr(toks: &[crate::lexer::token::Token]) -> Option<Expression> {
        if toks.is_empty() {
            return None;
        }
        let end = toks[toks.len() - 1].span.end;
        let mut run = toks.to_vec();
        run.push(crate::lexer::token::Token::new(
            TokenKind::Eof,
            String::new(),
            crate::ast::Span::new(end, end),
        ));
        let mut p = super::Parser::new(run);
        let e = p.parse_expression();
        (p.at(TokenKind::Eof) && !p.has_errors()).then_some(e)
    }

    /// Token texts joined with a single space wherever the source had one.
    fn tokens_source_text(toks: &[crate::lexer::token::Token]) -> String {
        let mut s = String::new();
        for (k, t) in toks.iter().enumerate() {
            if k > 0 && toks[k - 1].span.end < t.span.start {
                s.push(' ');
            }
            s.push_str(&t.text);
        }
        s
    }

    /// Parse a `$setuphold(...)` / `$recrem(...)` timing check ONLY to recover
    /// its delayed nets. The full arg list is `(ref_event, data_event, limit1,
    /// limit2, [notifier], [tstamp], [tcheck], [delayed_ref], [delayed_data])`;
    /// only `$setuphold`/`$recrem` carry the two delayed-net outputs (args 8,9).
    /// We split on top-level commas, take the reference/data SIGNAL from the
    /// first two edge-event args, and pair each present delayed net with its
    /// source signal → `(delayed_ref, ref_sig)`, `(delayed_data, data_sig)`.
    /// Everything is then consumed to the terminating `;`.
    fn parse_timing_check_delayed_nets(&mut self, out: &mut Vec<(String, String)>) {
        let is_recrem_or_setuphold =
            matches!(self.current().text.as_str(), "$setuphold" | "$recrem");
        self.bump(); // the $name
        if !self.at(TokenKind::LParen) {
            self.skip_to_semi();
            return;
        }
        self.bump(); // '('
        // Collect each top-level (paren-depth-0) comma-separated arg as the
        // list of its tokens' texts, plus whether it began with posedge/negedge.
        let mut args: Vec<Vec<String>> = Vec::new();
        let mut cur: Vec<String> = Vec::new();
        let mut depth = 0i32;
        while !self.at(TokenKind::Eof) {
            match self.current().kind {
                TokenKind::LParen => {
                    depth += 1;
                    cur.push(self.bump().text.clone());
                }
                TokenKind::RParen => {
                    if depth == 0 {
                        self.bump(); // closing ')'
                        break;
                    }
                    depth -= 1;
                    cur.push(self.bump().text.clone());
                }
                TokenKind::Comma if depth == 0 => {
                    self.bump();
                    args.push(std::mem::take(&mut cur));
                }
                _ => cur.push(self.bump().text.clone()),
            }
        }
        args.push(cur);
        self.eat(TokenKind::Semicolon);

        // The SIGNAL of an edge-event arg is the first identifier after a
        // posedge/negedge (or the first identifier); a `&&& cond` tail is
        // ignored. A plain delayed-net arg is a single identifier.
        fn signal_of(arg: &[String]) -> Option<String> {
            let mut it = arg.iter();
            while let Some(t) = it.next() {
                if t == "posedge" || t == "negedge" || t == "edge" {
                    if let Some(n) = it.next() {
                        return Some(n.clone());
                    }
                }
            }
            // no edge keyword: first identifier-looking token
            arg.iter()
                .find(|t| {
                    t.chars()
                        .next()
                        .map(|c| c.is_alphabetic() || c == '_')
                        .unwrap_or(false)
                })
                .cloned()
        }
        fn plain_net(arg: &[String]) -> Option<String> {
            let toks: Vec<&String> = arg.iter().filter(|t| !t.trim().is_empty()).collect();
            if toks.len() == 1
                && toks[0]
                    .chars()
                    .next()
                    .map(|c| c.is_alphabetic() || c == '_')
                    .unwrap_or(false)
            {
                Some(toks[0].clone())
            } else {
                None
            }
        }

        // Two-limit checks ($setuphold/$recrem) carry delayed_ref/delayed_data
        // at args[7]/[8] (§15.6 13-arg form); single-limit checks ($setup/
        // $hold/$recovery/$removal) at args[6]/[7] in the vendor-extension
        // 8-arg form `(ref, data, limit, notifier, tstamp_cond, tcheck_cond,
        // delayed_ref, delayed_data)` that gate libraries wire UDP terminals
        // from. Short (LRM-minimal) forms have no delayed nets.
        let (dref_idx, ddata_idx) = if is_recrem_or_setuphold {
            (7, 8)
        } else {
            (6, 7)
        };
        if args.len() <= dref_idx {
            return;
        }
        let ref_sig = signal_of(&args[0]);
        let data_sig = signal_of(&args[1]);
        if let (Some(dref), Some(src)) = (plain_net(&args[dref_idx]), ref_sig) {
            out.push((dref, src));
        }
        if let Some(a) = args.get(ddata_idx) {
            if let (Some(ddata), Some(src)) = (plain_net(a), data_sig) {
                out.push((ddata, src));
            }
        }
    }

    /// §30.4 module path declaration: parallel `=>` or full `*>`, with an
    /// optional polarity, edge identifier and data source (§30.4.3), under an
    /// optional `if (cond)` / `ifnone` (§30.4.4), and a delay list of 1, 2,
    /// 3, 6 or 12 values (§30.5.1) with or without parentheses. Each value
    /// may be a min:typ:max triplet — the element chosen by
    /// `+mindelays`/`+typdelays`/`+maxdelays` (default typ) is kept. Returns
    /// `None` (position restored) for anything else, which the caller skips.
    fn try_parse_specify_path(&mut self) -> Option<SpecifyPath> {
        let start_pos = self.pos;
        let diag_len = self.diagnostics.len();
        let sp_start = self.current().span.start;
        let p = self.parse_specify_path_inner(sp_start);
        if p.is_none() || self.diagnostics.len() != diag_len {
            self.diagnostics.truncate(diag_len);
            self.pos = start_pos;
            return None;
        }
        p
    }

    fn parse_specify_path_inner(&mut self, sp_start: usize) -> Option<SpecifyPath> {
        let mut cond = None;
        let mut ifnone = false;
        if self.eat(TokenKind::KwIf).is_some() {
            self.eat(TokenKind::LParen)?;
            cond = Some(self.parse_expression());
            self.eat(TokenKind::RParen)?;
        } else if self.eat(TokenKind::KwIfnone).is_some() {
            ifnone = true;
        }
        self.eat(TokenKind::LParen)?;
        let edge = matches!(
            self.current_kind(),
            TokenKind::KwPosedge | TokenKind::KwNegedge | TokenKind::KwEdge
        );
        if edge {
            self.bump();
        }
        let srcs = self.parse_specify_terminals()?;
        // Parallel `=>` or full `*>` connection with optional polarity (a
        // per-net delay model needs neither). The lexer splits `+=>` into
        // `+=` `>` and `*>` into `*` `>`.
        if matches!(
            self.current_kind(),
            TokenKind::PlusAssign | TokenKind::MinusAssign
        ) {
            self.bump();
            self.eat(TokenKind::Gt)?;
        } else {
            if matches!(self.current_kind(), TokenKind::Plus | TokenKind::Minus) {
                self.bump();
            }
            if self.at(TokenKind::FatArrow) && self.current().text == "=>" {
                self.bump();
            } else if self.at(TokenKind::Star) && self.peek_kind() == TokenKind::Gt {
                self.bump();
                self.bump();
            } else {
                return None;
            }
        }
        let dsts = if self.eat(TokenKind::LParen).is_some() {
            // Edge-sensitive `( dst [+|-] : data_source )`.
            let dsts = self.parse_specify_terminals()?;
            match self.current_kind() {
                TokenKind::PlusColon | TokenKind::MinusColon | TokenKind::Colon => {
                    self.bump();
                }
                TokenKind::Plus | TokenKind::Minus if self.peek_kind() == TokenKind::Colon => {
                    self.bump();
                    self.bump();
                }
                _ => return None,
            }
            let _ = self.parse_expression();
            self.eat(TokenKind::RParen)?;
            dsts
        } else {
            self.parse_specify_terminals()?
        };
        self.eat(TokenKind::RParen)?;
        self.eat(TokenKind::Assign)?;
        let delays = self.parse_path_delay_value()?;
        self.eat(TokenKind::Semicolon)?;
        Some(SpecifyPath {
            srcs,
            dsts,
            cond,
            ifnone,
            delays,
            span: self.span_from(sp_start),
        })
    }

    /// `name [ [range] ] {, name [ [range] ]}` — the base names; a bit or
    /// part select only narrows the path to part of the net.
    fn parse_specify_terminals(&mut self) -> Option<Vec<Identifier>> {
        let mut out = Vec::new();
        loop {
            if !matches!(
                self.current_kind(),
                TokenKind::Identifier | TokenKind::EscapedIdentifier
            ) {
                return None;
            }
            out.push(self.parse_identifier());
            if self.eat(TokenKind::LBracket).is_some() {
                let _ = self.parse_expression();
                if matches!(
                    self.current_kind(),
                    TokenKind::Colon | TokenKind::PlusColon | TokenKind::MinusColon
                ) {
                    self.bump();
                    let _ = self.parse_expression();
                }
                self.eat(TokenKind::RBracket)?;
            }
            if self.eat(TokenKind::Comma).is_none() {
                return Some(out);
            }
        }
    }

    /// §30.5.1 `path_delay_value`: a list of delay values, parenthesized or
    /// not. A parenthesized form followed by anything but `;` was a bare
    /// expression that merely starts with `(`.
    fn parse_path_delay_value(&mut self) -> Option<Vec<Expression>> {
        let entry = |p: &mut Self| -> Expression {
            let first = p.parse_expression();
            if !p.at(TokenKind::Colon) {
                return first;
            }
            p.bump();
            let typ = p.parse_expression();
            let max = if p.at(TokenKind::Colon) {
                p.bump();
                Some(p.parse_expression())
            } else {
                None
            };
            match crate::delay_select() {
                0 => first,
                2 => max.unwrap_or(typ),
                _ => typ,
            }
        };
        let list = |p: &mut Self| -> Vec<Expression> {
            let mut v = vec![entry(p)];
            while p.eat(TokenKind::Comma).is_some() {
                v.push(entry(p));
            }
            v
        };
        let start = self.pos;
        if self.eat(TokenKind::LParen).is_some() {
            let v = list(self);
            if self.eat(TokenKind::RParen).is_some() && self.at(TokenKind::Semicolon) {
                return Some(v);
            }
            self.pos = start;
        }
        Some(list(self))
    }

    /// Like `parse_generate_branch_items` but also returns the optional
    /// `begin : <label>` block name (needed to namespace generate-for renames).
    fn parse_generate_branch_items_named(&mut self) -> (Vec<ModuleItem>, Option<String>) {
        self.generate_depth += 1;
        // §27.5: a generate block is a scope, for lets too (§11.13).
        self.push_let_scope();
        let prefixed = self.after_block_label();
        let r = if self.eat(TokenKind::KwBegin).is_some() {
            let label = self.parse_end_label().map(|id| id.name);
            let items = self.parse_module_items_until(TokenKind::KwEnd);
            self.expect(TokenKind::KwEnd);
            if let Some(l) = self.parse_end_label()
                && label.is_none()
                && !prefixed
            {
                self.unnamed_block_end_label(&l);
            }
            (items, label)
        } else {
            (self.parse_module_item().into_iter().collect(), None)
        };
        self.pop_let_scope();
        self.generate_depth -= 1;
        r
    }

    /// Convert a `#(...)` parameter VALUE into a TYPE-ARG expression when it
    /// is used as the specialization of a parameterized CLASS in a data-
    /// declaration type (`param_obj #(int) x;`). `parse_param_value` returns
    /// `ParamValue::Type(dt)` for a type keyword (`int`, `bit`) or a
    /// typedef/class name; data declarations need those as identifier
    /// expressions so the specialize's `type_args` list is non-empty and
    /// downstream per-spec binding (type_bindings / current_spec / the
    /// class registry's `type_name`) can reconstruct `param_obj#(int)`. A
    /// position that drops them leaves the type_args empty and the variable
    /// default-specializes (`param_obj#(bit)`), which is what broke UVM's
    /// `type_id::type_name()` for parameterized-class fields/collections.
    /// One `#(...)` connection of a class-typed data declaration as a type
    /// arg. A named connection (`#(.W(5))`, §8.25) keeps its name as a
    /// `NamedArg`: dropping it bound the value to the class's FIRST
    /// parameter, whatever the name said.
    fn param_connection_to_type_arg(
        &self,
        pc: &ParamConnection,
    ) -> Option<crate::ast::expr::Expression> {
        match pc {
            ParamConnection::Ordered(Some(pv)) => self.param_value_to_type_arg(pv),
            ParamConnection::Named {
                name,
                value: Some(pv),
            } => {
                let v = self.param_value_to_type_arg(pv)?;
                let span = v.span;
                Some(crate::ast::expr::Expression::new(
                    crate::ast::expr::ExprKind::NamedArg {
                        name: name.clone(),
                        expr: Some(Box::new(v)),
                    },
                    span,
                ))
            }
            _ => None,
        }
    }

    fn param_value_to_type_arg(&self, pv: &ParamValue) -> Option<crate::ast::expr::Expression> {
        use crate::ast::Identifier as PIdent;
        use crate::ast::expr::{ExprKind, Expression, HierPathSegment, HierarchicalIdentifier};
        use crate::ast::types::DataType;
        let (leaf, span) = match pv {
            ParamValue::Expr(e) => return Some(e.clone()),
            ParamValue::Type(dt) => match dt {
                // A DIMENSIONED vector (`bit [7:0]`) or a signed atom is not a
                // bare name: rendering just the keyword would alias
                // `P#(bit[7:0])` with `P#(bit)`. Carry the whole type instead;
                // the spec-fragment renderer knows how to print a
                // `TypeLiteral`.
                DataType::IntegerVector {
                    dimensions, span, ..
                } if !dimensions.is_empty() => {
                    return Some(Expression::new(
                        ExprKind::TypeLiteral(Box::new(dt.clone())),
                        *span,
                    ));
                }
                DataType::TypeReference { name, .. } => (name.name.name.clone(), name.name.span),
                DataType::IntegerAtom { kind, span, .. } => (
                    match kind {
                        crate::ast::types::IntegerAtomType::Byte => "byte",
                        crate::ast::types::IntegerAtomType::ShortInt => "shortint",
                        crate::ast::types::IntegerAtomType::Int => "int",
                        crate::ast::types::IntegerAtomType::LongInt => "longint",
                        crate::ast::types::IntegerAtomType::Integer => "integer",
                        crate::ast::types::IntegerAtomType::Time => "time",
                    }
                    .to_string(),
                    *span,
                ),
                DataType::IntegerVector { kind, span, .. } => (
                    match kind {
                        crate::ast::types::IntegerVectorType::Bit => "bit",
                        crate::ast::types::IntegerVectorType::Logic => "logic",
                        crate::ast::types::IntegerVectorType::Reg => "reg",
                    }
                    .to_string(),
                    *span,
                ),
                DataType::Simple {
                    kind: crate::ast::types::SimpleType::String,
                    span,
                } => ("string".to_string(), *span),
                _ => return None,
            },
        };
        let hier = HierarchicalIdentifier {
            root: None,
            path: vec![HierPathSegment {
                name: PIdent { name: leaf, span },
                selects: Vec::new(),
            }],
            span,
            cached_signal_id: std::cell::Cell::new(None),
            cached_resolved_name: std::cell::OnceCell::new(),
        };
        Some(Expression::new(ExprKind::Ident(hier), span))
    }

    /// The optional `#(...)` parameter value assignment of an instantiation
    /// (`mod #(.P(v), 3) u (...)`), shared by module items and `bind`
    /// directives. `None` when no `#` follows.
    pub(super) fn parse_instantiation_params(&mut self) -> Option<Vec<ParamConnection>> {
        if !self.at(TokenKind::Hash) {
            return None;
        }
        self.bump();
        if self.eat(TokenKind::LParen).is_some() {
            let mut p = Vec::new();
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                if self.at(TokenKind::Dot) {
                    self.bump();
                    let pn = self.parse_identifier();
                    self.expect(TokenKind::LParen);
                    let pv = if !self.at(TokenKind::RParen) {
                        Some(self.parse_param_value())
                    } else {
                        None
                    };
                    self.expect(TokenKind::RParen);
                    p.push(ParamConnection::Named {
                        name: pn,
                        value: pv,
                    });
                } else {
                    p.push(ParamConnection::Ordered(Some(self.parse_param_value())));
                }

                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::RParen);
            Some(p)
        } else if matches!(
            self.current_kind(),
            TokenKind::IntegerLiteral | TokenKind::RealLiteral | TokenKind::TimeLiteral
        ) {
            // §28.3 primitive delay without parens — `ubuf #2 u (o, i)`.
            // Eating the `#` and returning None left the literal in the
            // stream to trip the instance-name parse. A single NUMERIC
            // literal becomes the one positional value, converging with
            // `#(2)` downstream (the UDP elaborator reads a scalar delay
            // out of `params`). Literals only: an identifier here would
            // be ambiguous against too many neighbors.
            Some(vec![ParamConnection::Ordered(Some(
                self.parse_param_value(),
            ))])
        } else {
            None
        }
    }

    fn parse_identifier_starting_item(&mut self) -> ModuleItem {
        let start = self.current().span.start;
        let first_name = self.parse_identifier();
        if self.at(TokenKind::DoubleColon) {
            // `::`-chained scoped type: `pkg::T`, `pkg::cls::T`,
            // `pkg::cls::sub::T` (IEEE 1800-2017 §8.23) and `pkg::cls#(N)::T`
            // (§8.25.1). Walk the WHOLE chain — the old two-name form
            // collapsed `pkg::cls::T` to scope `pkg` + name `cls` and then
            // died on the trailing `::T` when the declarator list parsed.
            let mut scopes: Vec<crate::ast::types::TypeScope> = Vec::new();
            let mut tn_name = first_name;
            while self.at(TokenKind::DoubleColon) {
                self.bump(); // ::
                scopes.push(crate::ast::types::TypeScope {
                    name: tn_name,
                    type_args: Vec::new(),
                });
                tn_name = self.parse_identifier();
                // `cls#(N)::t` — a per-link specialization, consumed only
                // when a `::` follows (the leaf's own `#(...)` is parsed
                // below, as before).
                if self.at(TokenKind::Hash)
                    && self.peek_kind() == TokenKind::LParen
                    && self.peek_hash_paren_is_scope_link()
                {
                    let link_args = self.parse_type_args_hash(start);
                    self.expect(TokenKind::DoubleColon);
                    scopes.push(crate::ast::types::TypeScope {
                        name: tn_name,
                        type_args: link_args,
                    });
                    tn_name = self.parse_identifier();
                }
            }
            let second_name = tn_name;
            // `pkg::cls #(.P(v)) var = new;` — scoped PARAMETERIZED class
            // as the declaration type (§8.25). The specialization was never
            // consumed here, so the declarator parser saw `#`.
            let type_args = self.parse_type_args_hash(start);
            let dimensions = self.parse_packed_dimensions();
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes,
                    name: second_name,
                    span: self.span_from(start),
                },
                dimensions,
                type_args,
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }
        if self.eat(TokenKind::Colon).is_some() {
            let mut item = self.parse_module_item().unwrap_or(ModuleItem::Null);
            if let ModuleItem::AssertionItem(a) = &mut item {
                a.label = Some(first_name);
            }
            return item;
        }
        // §25.5: non-ANSI body port declaration with a MODPORT-qualified
        // interface type — `counter_if.counter_mp c_data;`. The lookahead is
        // `. ident ident` with a `;`/`,` after: nothing else at item level
        // has that shape (an instantiation would be `type name (…)`). ANSI
        // headers already route through parse_data_type's Interface arm;
        // this body form died on the dot ("expected identifier, found Dot").
        if self.at(TokenKind::Dot)
            && self.peek_kind() == TokenKind::Identifier
            && self.peek_kind_n(2) == TokenKind::Identifier
            && matches!(self.peek_kind_n(3), TokenKind::Semicolon | TokenKind::Comma)
        {
            self.bump(); // .
            let modport = self.parse_identifier();
            let dt = DataType::Interface {
                name: first_name.clone(),
                modport: Some(modport),
                type_args: Vec::new(),
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }
        let params = self.parse_instantiation_params();

        // §8.25.1: `Cls#(args)::td var;` — a parameterized class used as a
        // scope prefix, spelled WITHOUT a package qualifier. The `#(...)`
        // was just consumed as instantiation params; a following `::`
        // means it was the class's SPECIALIZATION, so convert the
        // connections to type args and walk the rest of the scope chain
        // (further `::` links and per-link `#(...)::` specializations,
        // §8.23).
        if self.at(TokenKind::DoubleColon) {
            let type_args: Vec<crate::ast::expr::Expression> = match &params {
                Some(ps) => ps
                    .iter()
                    .filter_map(|pc| self.param_connection_to_type_arg(pc))
                    .collect(),
                None => Vec::new(),
            };
            let mut scopes: Vec<crate::ast::types::TypeScope> =
                vec![crate::ast::types::TypeScope {
                    name: first_name,
                    type_args,
                }];
            self.bump(); // ::
            let mut tn_name = self.parse_identifier();
            while self.at(TokenKind::DoubleColon) {
                self.bump(); // ::
                scopes.push(crate::ast::types::TypeScope {
                    name: tn_name,
                    type_args: Vec::new(),
                });
                tn_name = self.parse_identifier();
                if self.at(TokenKind::Hash)
                    && self.peek_kind() == TokenKind::LParen
                    && self.peek_hash_paren_is_scope_link()
                {
                    let link_args = self.parse_type_args_hash(start);
                    self.expect(TokenKind::DoubleColon);
                    scopes.push(crate::ast::types::TypeScope {
                        name: tn_name,
                        type_args: link_args,
                    });
                    tn_name = self.parse_identifier();
                }
            }
            let dimensions = self.parse_packed_dimensions();
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes,
                    name: tn_name,
                    span: self.span_from(start),
                },
                dimensions,
                type_args: Vec::new(),
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }

        // Packed dimensions on a user-typedef base: `MyType [hi:lo] var_name;`
        // After the optional #(params), if we see `[`, treat the construct as a
        // data declaration of `MyType` with packed dimensions, not a module
        // instantiation.
        if self.at(TokenKind::LBracket) {
            let dimensions = self.parse_packed_dimensions();
            let type_args: Vec<crate::ast::expr::Expression> = match &params {
                Some(ps) => ps
                    .iter()
                    .filter_map(|pc| self.param_connection_to_type_arg(pc))
                    .collect(),
                None => Vec::new(),
            };
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes: Vec::new(),
                    name: first_name,
                    span: self.span_from(start),
                },
                dimensions,
                type_args,
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }
        // §29.3 `udp_instance ::= [name_of_instance] ( terminals )`: a UDP
        // instance may omit its name (`p (q, d);`). It is kept with an empty
        // name; the elaborator rejects a nameless module instance (§23.3.2).
        if self.at(TokenKind::LParen) {
            let mut instances = Vec::new();
            loop {
                let inst_start = self.current().span.start;
                let name = if self.at(TokenKind::Identifier) {
                    self.parse_identifier()
                } else {
                    Identifier {
                        name: String::new(),
                        span: self.span_from(inst_start),
                    }
                };
                let dims = self.parse_unpacked_dimensions();
                let conns = self.parse_port_connections();
                instances.push(HierarchicalInstance {
                    name,
                    dimensions: dims,
                    connections: conns,
                    span: self.span_from(inst_start),
                });
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::Semicolon);
            return ModuleItem::ModuleInstantiation(ModuleInstantiation {
                module_name: first_name,
                params,
                instances,
                span: self.span_from(start),
            });
        }
        if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
            let initial_pos = self.pos;
            let mut is_data_decl = false;
            let mut instances = Vec::new();
            loop {
                let inst_save_pos = self.pos;
                let inst_start = self.current().span.start;
                let _iname = self.parse_identifier();
                let _dims = self.parse_unpacked_dimensions();
                if self.at(TokenKind::Assign)
                    || self.at(TokenKind::Semicolon)
                    || self.at(TokenKind::Comma)
                {
                    is_data_decl = true;
                    break;
                }
                self.pos = inst_save_pos; // rewind just this instance
                let iname = self.parse_identifier();
                let dims = self.parse_unpacked_dimensions();
                let conns = self.parse_port_connections();
                instances.push(HierarchicalInstance {
                    name: iname,
                    dimensions: dims,
                    connections: conns,
                    span: self.span_from(inst_start),
                });
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            if is_data_decl {
                self.pos = initial_pos;
                let type_args: Vec<crate::ast::expr::Expression> = match &params {
                    Some(ps) => ps
                        .iter()
                        .filter_map(|pc| self.param_connection_to_type_arg(pc))
                        .collect(),
                    None => Vec::new(),
                };
                let dt = DataType::TypeReference {
                    name: TypeName {
                        scopes: Vec::new(),
                        name: first_name,
                        span: self.span_from(start),
                    },
                    dimensions: Vec::new(),
                    type_args,
                    span: self.span_from(start),
                };
                let decls = self.parse_var_declarator_list();
                self.expect(TokenKind::Semicolon);
                ModuleItem::DataDeclaration(DataDeclaration {
                    const_kw: false,
                    var_kw: false,
                    lifetime: None,
                    data_type: dt,
                    declarators: decls,
                    span: self.span_from(start),
                })
            } else {
                self.expect(TokenKind::Semicolon);
                ModuleItem::ModuleInstantiation(ModuleInstantiation {
                    module_name: first_name,
                    params,
                    instances,
                    span: self.span_from(start),
                })
            }
        } else {
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes: Vec::new(),
                    name: first_name,
                    span: self.span_from(start),
                },
                dimensions: Vec::new(),
                type_args: Vec::new(),
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            ModuleItem::DataDeclaration(DataDeclaration {
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            })
        }
    }

    /// One actual of an instance connection. §17.2: a checker's event
    /// formal takes an event expression (`chk u(v, posedge clk)`), which
    /// is not an ordinary expression; it is carried as the internal
    /// `$__posedge(e)` / `$__negedge(e)` / `$__edge(e)` call and folded
    /// into the clocking event when the checker body is instantiated.
    fn parse_port_actual(&mut self) -> Expression {
        let name = match self.current().kind {
            TokenKind::KwPosedge => "$__posedge",
            TokenKind::KwNegedge => "$__negedge",
            TokenKind::KwEdge => "$__edge",
            _ => return self.parse_expression(),
        };
        let start = self.current().span.start;
        self.bump();
        let e = self.parse_expression();
        Expression::new(
            ExprKind::SystemCall {
                name: name.to_string(),
                args: vec![e],
            },
            self.span_from(start),
        )
    }

    pub(super) fn parse_port_connections(&mut self) -> Vec<PortConnection> {
        let mut conns = Vec::new();
        if self.eat(TokenKind::LParen).is_none() {
            return conns;
        }
        if self.at(TokenKind::RParen) {
            self.bump();
            return conns;
        }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                break;
            }
            if self.at(TokenKind::Comma) {
                // Empty positional connection: `dut(, result)`. An omitted
                // ordered port takes its declared default (§23.2.2.4) or is
                // left unconnected.
                conns.push(PortConnection::Ordered(None));
            } else if self.at(TokenKind::Dot) {
                self.bump();
                if self.at(TokenKind::Star) {
                    self.bump();
                    conns.push(PortConnection::Wildcard);
                } else {
                    let nm = self.parse_identifier();
                    let (ex, had_parens) = if self.eat(TokenKind::LParen).is_some() {
                        let e = if !self.at(TokenKind::RParen) {
                            Some(self.parse_port_actual())
                        } else {
                            None
                        };
                        self.expect(TokenKind::RParen);
                        (e, true)
                    } else {
                        (None, false)
                    };
                    conns.push(PortConnection::Named {
                        name: nm,
                        expr: ex,
                        implicit: !had_parens,
                    });
                }
            } else {
                conns.push(PortConnection::Ordered(Some(self.parse_port_actual())));
            }
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            // Trailing empty positional connection: `dut(result, )`.
            if self.at(TokenKind::RParen) {
                conns.push(PortConnection::Ordered(None));
                break;
            }
        }
        // §23.3.2: connections are all by position or all by name.
        if crate::strict_checks()
            && conns
                .iter()
                .any(|c| matches!(c, PortConnection::Ordered(Some(_))))
            && conns
                .iter()
                .any(|c| !matches!(c, PortConnection::Ordered(_)))
        {
            self.error(
                "port connections by position and by name cannot be mixed in one \
                 instance (IEEE 1800-2017 §23.3.2)",
            );
        }
        self.expect(TokenKind::RParen);
        conns
    }

    pub(super) fn parse_module_items_until(&mut self, end: TokenKind) -> Vec<ModuleItem> {
        let mut items = Vec::new();
        while !self.at(end) && !self.at(TokenKind::Eof) {
            if let Some(item) = self.parse_module_item() {
                self.hide_let_names_of_item(&item);
                items.push(item);
                items.append(&mut self.pending_module_items);
            } else {
                self.error(format!("unexpected: {:?}", self.current().text));
                self.bump();
            }
        }
        items
    }

    /// The tokens of a parameter value list parsed from `start` on, as text,
    /// to tell specializations apart (empty without a list).
    fn param_args_text(&self, start: usize) -> String {
        let toks = &self.tokens[start..self.pos];
        let inner = match toks {
            [h, l, rest @ .., _] if h.kind == TokenKind::Hash && l.kind == TokenKind::LParen => {
                rest
            }
            [l, rest @ .., _] if l.kind == TokenKind::LParen => rest,
            _ => toks,
        };
        inner
            .iter()
            .map(|t| t.text.as_str())
            .collect::<Vec<_>>()
            .join(" ")
    }

    pub(super) fn parse_class_declaration(&mut self) -> ClassDeclaration {
        let start = self.current().span.start;
        // A module item arrives here with `virtual` / `interface` already
        // consumed; the caller sets the flags, but the class checks below
        // need them too.
        let after = |p: &Self, k: TokenKind| {
            p.at(TokenKind::KwClass) && p.pos > 0 && p.tokens[p.pos - 1].kind == k
        };
        let virt = self.eat(TokenKind::KwVirtual).is_some() || after(self, TokenKind::KwVirtual);
        // IEEE 1800-2017 §8.26: `interface class <name>; … endclass`. The
        // leading `interface` keyword (mutually exclusive with `virtual`)
        // marks an interface class; the rest parses like a normal class.
        let is_iface =
            self.eat(TokenKind::KwInterface).is_some() || after(self, TokenKind::KwInterface);
        self.expect(TokenKind::KwClass);
        // IEEE 1800-2023 §8.20.5: `class :final <name>` — only `:final` is
        // legal on a class declaration. Gated on --sv2023.
        let is_final = if crate::is_sv2023()
            && self.at(TokenKind::Colon)
            && self.peek_kind() == TokenKind::KwFinal
        {
            self.bump(); // ':'
            self.bump(); // 'final'
            true
        } else {
            false
        };
        let _lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let params = self.parse_parameter_port_list();
        let mut bases = Vec::new();
        let mut unscoped_bases: Vec<Identifier> = Vec::new();
        let extends = if self.eat(TokenKind::KwExtends).is_some() {
            let ext_start = self.current().span.start;
            // §8.13: the base class may be package/class-scoped —
            // `extends pkg::Base` or `extends A::B::C`. Keep the final
            // segment as the base-class name; the scope prefix is consumed.
            let mut base_name = self.parse_identifier();
            let mut scoped = false;
            while self.at(TokenKind::DoubleColon) {
                self.bump();
                scoped = true;
                base_name = self.parse_identifier();
            }
            if !scoped {
                unscoped_bases.push(base_name.clone());
            }
            let args_at = self.pos;
            let args = if self.at(TokenKind::Hash) {
                self.parse_param_args()
            } else if self.at(TokenKind::LParen) {
                self.parse_param_args()
            }
            // Support extends C(args) or C#(args)
            else {
                Vec::new()
            };
            bases.push((base_name.name.clone(), self.param_args_text(args_at)));
            // §8.26: an interface class may extend MULTIPLE interface classes
            // (`extends ic1#(T), ic2#(T)`). Keep the first in the AST and
            // parse-accept the rest (consume `, base[::seg]…[#(args)]`).
            while self.at(TokenKind::Comma) {
                self.bump();
                let mut other = self.parse_identifier();
                let mut scoped = false;
                while self.at(TokenKind::DoubleColon) {
                    self.bump();
                    scoped = true;
                    other = self.parse_identifier();
                }
                if !scoped {
                    unscoped_bases.push(other.clone());
                }
                let at = self.pos;
                if self.at(TokenKind::Hash) || self.at(TokenKind::LParen) {
                    let _ = self.parse_param_args();
                }
                bases.push((other.name, self.param_args_text(at)));
            }
            Some(ClassExtends {
                name: base_name,
                args,
                span: self.span_from(ext_start),
            })
        } else {
            None
        };
        // IEEE 1800-2017 §8.26.4: an interface class shall not extend a type
        // parameter, even one whose type is an interface class. Every base is
        // checked, not only the first one the AST keeps.
        if is_iface {
            for b in &unscoped_bases {
                let is_type_param = params.iter().any(|p| match &p.kind {
                    ParameterKind::Type { assignments } => {
                        assignments.iter().any(|a| a.name.name == b.name)
                    }
                    _ => false,
                });
                if is_type_param {
                    self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                        format!(
                            "interface class '{}' extends type parameter '{}'; an interface \
                             class shall not extend a type parameter (IEEE 1800-2017 §8.26.4)",
                            name.name, b.name
                        ),
                        b.span,
                    ));
                }
            }
        }
        let mut implements = Vec::new();
        if self.eat(TokenKind::KwImplements).is_some() {
            loop {
                let mut iface = self.parse_identifier();
                // §8.26: scoped interface-class name `implements pkg::Iface`.
                while self.at(TokenKind::DoubleColon) {
                    self.bump();
                    iface = self.parse_identifier();
                }
                implements.push(iface);
                // §8.26.1: `implements Iface#(params)` — consume and discard
                // the parameterization (only the base name is recorded).
                if self.at(TokenKind::Hash) {
                    let _ = self.parse_param_args();
                }
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        self.expect(TokenKind::Semicolon);
        // Push the class name onto the parser's class-context stack so
        // `type(this)` references resolve to this class (§6.20.2.1).
        crate::push_class_context(name.name.clone());
        let mut items = Vec::new();
        let outer_pure = std::mem::take(&mut self.pure_constraints);
        // A class is a scope: its members hide outer lets of the same name.
        self.push_let_scope();
        while !self.at(TokenKind::KwEndclass) && !self.at(TokenKind::Eof) {
            let it = self.parse_class_item();
            self.hide_let_names_of_class_item(&it);
            items.push(it);
        }
        self.pop_let_scope();
        let pure_constraints = std::mem::replace(&mut self.pure_constraints, outer_pure);
        crate::pop_class_context();
        {
            let mut type_names = Vec::new();
            let mut add_params = |pd: &ParameterDeclaration, out: &mut Vec<String>| match &pd.kind {
                ParameterKind::Data { assignments, .. } => {
                    out.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
                ParameterKind::Type { assignments } => {
                    out.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
            };
            for pd in &params {
                add_params(pd, &mut type_names);
            }
            let mut constraints = Vec::new();
            for it in &items {
                match it {
                    ClassItem::Parameter(pd) => add_params(pd, &mut type_names),
                    ClassItem::Typedef(t) => type_names.push(t.name.name.clone()),
                    ClassItem::Constraint(c) if !pure_constraints.contains(&c.name.name) => {
                        constraints.push(c.name.name.clone())
                    }
                    _ => {}
                }
            }
            self.class_infos.push(super::ClassInfo {
                name: name.clone(),
                is_virtual: virt,
                is_interface: is_iface,
                bases,
                type_names,
                pure_constraints,
                constraints,
            });
        }
        self.expect(TokenKind::KwEndclass);
        let endlabel = self.parse_end_label();
        if crate::strict_checks() {
            self.check_interface_class_names();
        }
        ClassDeclaration {
            virtual_kw: virt,
            is_interface: is_iface,
            is_final,
            name,
            params,
            extends,
            implements,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    /// §8.26.6.2 / §8.26.6.3: an interface class that inherits one parameter
    /// or type name from two different base classes, or from two
    /// specializations of one, declares that name itself. Checked for the
    /// class just parsed, against the classes before it in this file; a chain
    /// through any other class is not followed.
    fn check_interface_class_names(&mut self) {
        let find = |n: &str| self.class_infos.iter().find(|c| c.name.name == n);
        let mut errs = Vec::new();
        for c in self
            .class_infos
            .last()
            .filter(|c| c.is_interface && c.bases.len() > 1)
        {
            // (name, the specialized class it is inherited from)
            let mut origin: Vec<(String, String)> = Vec::new();
            let mut stack: Vec<(String, String, u32)> = c
                .bases
                .iter()
                .map(|(b, a)| (b.clone(), a.clone(), 0))
                .collect();
            let mut complete = true;
            while let Some((b, args, depth)) = stack.pop() {
                let Some(bi) = find(&b) else {
                    complete = false;
                    break;
                };
                let from = format!("{b}#({args})");
                for n in &bi.type_names {
                    origin.push((n.clone(), from.clone()));
                }
                if depth < 32 {
                    stack.extend(
                        bi.bases
                            .iter()
                            .map(|(b, a)| (b.clone(), a.clone(), depth + 1)),
                    );
                }
            }
            if !complete {
                continue;
            }
            origin.sort();
            origin.dedup();
            let mut names: Vec<&str> = origin.iter().map(|(n, _)| n.as_str()).collect();
            names.dedup();
            for n in names {
                let from: Vec<&str> = origin
                    .iter()
                    .filter(|(o, _)| o == n)
                    .map(|(_, f)| f.as_str())
                    .collect();
                if from.len() > 1 && !c.type_names.iter().any(|t| t == n) {
                    errs.push(crate::diagnostics::Diagnostic::error(
                        format!(
                            "interface class '{}' inherits '{n}' from {} and must declare it \
                             itself (IEEE 1800-2017 §8.26.6.2)",
                            c.name.name,
                            from.join(" and ")
                        ),
                        c.name.span,
                    ));
                }
            }
        }
        self.diagnostics.extend(errs);
    }

    fn parse_class_item(&mut self) -> ClassItem {
        let start = self.current().span.start;
        if self.eat(TokenKind::Semicolon).is_some() {
            return ClassItem::Empty;
        }
        let mut qualifiers = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::KwStatic => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Static);
                }
                TokenKind::KwProtected => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Protected);
                }
                TokenKind::KwLocal => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Local);
                }
                TokenKind::KwRand => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Rand);
                }
                TokenKind::KwRandc => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Randc);
                }
                TokenKind::KwConst => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Const);
                }
                TokenKind::KwPure => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Pure);
                    if self.at(TokenKind::KwVirtual) {
                        self.bump();
                        qualifiers.push(ClassQualifier::Virtual);
                    }
                }
                TokenKind::KwVirtual => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Virtual);
                    if self.at(TokenKind::KwPure) {
                        self.bump();
                        qualifiers.push(ClassQualifier::Pure);
                    }
                }
                TokenKind::KwExtern => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Extern);
                }
                _ => break,
            }
        }

        match self.current_kind() {
            TokenKind::Directive => {
                self.bump();
                self.parse_class_item()
            }
            TokenKind::KwFunction => {
                let is_pure = qualifiers.contains(&ClassQualifier::Pure);
                let is_extern = qualifiers.contains(&ClassQualifier::Extern);
                if is_pure || is_extern {
                    let func = self.parse_function_prototype();
                    if is_pure {
                        ClassItem::Method(ClassMethod {
                            qualifiers,
                            kind: ClassMethodKind::PureVirtual(func),
                            span: self.span_from(start),
                        })
                    } else {
                        ClassItem::Method(ClassMethod {
                            qualifiers,
                            kind: ClassMethodKind::Extern(func),
                            span: self.span_from(start),
                        })
                    }
                } else {
                    let func = self.parse_function_declaration();
                    ClassItem::Method(ClassMethod {
                        qualifiers,
                        kind: ClassMethodKind::Function(func),
                        span: self.span_from(start),
                    })
                }
            }
            TokenKind::KwTask => {
                let is_pure = qualifiers.contains(&ClassQualifier::Pure);
                let is_extern = qualifiers.contains(&ClassQualifier::Extern);
                if is_pure || is_extern {
                    let task = self.parse_task_prototype();
                    ClassItem::Method(ClassMethod {
                        qualifiers,
                        kind: ClassMethodKind::Task(task),
                        span: self.span_from(start),
                    })
                } else {
                    let task = self.parse_task_declaration();
                    ClassItem::Method(ClassMethod {
                        qualifiers,
                        kind: ClassMethodKind::Task(task),
                        span: self.span_from(start),
                    })
                }
            }
            TokenKind::KwConstraint => {
                self.bump();
                let cname = self.parse_identifier();
                if qualifiers.contains(&ClassQualifier::Pure) {
                    self.pure_constraints.push(cname.name.clone());
                }
                let (items, has_body) = if self.at(TokenKind::LBrace) {
                    self.bump();
                    let mut items = Vec::new();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        items.push(self.parse_constraint_item());
                    }
                    self.expect(TokenKind::RBrace);
                    (items, true)
                } else {
                    self.expect(TokenKind::Semicolon);
                    (Vec::new(), false)
                };
                ClassItem::Constraint(ClassConstraint {
                    is_static: qualifiers.contains(&ClassQualifier::Static),
                    is_extern: qualifiers.contains(&ClassQualifier::Extern),
                    has_body,
                    name: cname,
                    items,
                    span: self.span_from(start),
                })
            }
            TokenKind::KwTypedef => ClassItem::Typedef(self.parse_typedef_declaration()),
            TokenKind::KwParameter | TokenKind::KwLocalparam => {
                let pd = self.parse_parameter_declaration();
                self.expect(TokenKind::Semicolon);
                ClassItem::Parameter(pd)
            }
            TokenKind::KwClass => ClassItem::Class(self.parse_class_declaration()),
            TokenKind::KwCovergroup => ClassItem::Covergroup(self.parse_covergroup_declaration()),
            TokenKind::KwImport => ClassItem::Import(self.parse_import_declaration()),
            _ if self.is_data_type_keyword()
                || self.at(TokenKind::Identifier)
                || self.at(TokenKind::KwVar)
                || (crate::is_sv2023()
                    && self.at(TokenKind::KwType)
                    && self.peek_kind() == TokenKind::LParen) =>
            {
                let dt = if self.at(TokenKind::KwVar) {
                    self.bump();
                    if self.is_data_type_keyword() || self.at(TokenKind::Identifier) {
                        self.parse_data_type()
                    } else {
                        DataType::Implicit {
                            signing: None,
                            dimensions: Vec::new(),
                            span: self.span_from(start),
                        }
                    }
                } else {
                    self.parse_data_type()
                };
                let decls = self.parse_var_declarator_list();
                self.expect(TokenKind::Semicolon);
                ClassItem::Property(ClassProperty {
                    qualifiers,
                    data_type: dt,
                    declarators: decls,
                    span: self.span_from(start),
                })
            }
            _ => {
                self.error(format!(
                    "unexpected token in class: {:?}",
                    self.current().text
                ));
                self.bump();
                ClassItem::Empty
            }
        }
    }

    /// Consume a balanced `( ... )` group, including nested parens. Assumes the
    /// current token is `(`. Used to skip clauses whose contents we don't model
    /// (covergroup formals, `with function sample` port lists, `iff` guards).
    fn skip_balanced_parens(&mut self) {
        if !self.at(TokenKind::LParen) {
            return;
        }
        self.bump();
        let mut depth = 1;
        while depth > 0 && !self.at(TokenKind::Eof) {
            if self.at(TokenKind::LParen) {
                depth += 1;
            } else if self.at(TokenKind::RParen) {
                depth -= 1;
            }
            self.bump();
        }
    }

    /// Skip an unmodeled coverpoint bin body up to (but not consuming) the
    /// terminating `;` at nesting depth 0, or a `}` / `)` / `]` that CLOSES
    /// the enclosing scope. Depth-aware so bodies like
    /// `cp with (item inside {list})` don't desync the coverpoint's brace
    /// matching on the inner `}`.
    fn skip_bin_body_to_semicolon(&mut self) {
        let mut depth = 0usize;
        loop {
            match self.current_kind() {
                TokenKind::Eof => break,
                TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => depth += 1,
                TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                TokenKind::Semicolon if depth == 0 => break,
                _ => {}
            }
            self.bump();
        }
    }

    /// §19.5.2 trans_set: `trans_range_list { => trans_range_list }`.
    fn parse_trans_set(&mut self) -> Vec<crate::ast::decl::TransStep> {
        use crate::ast::decl::{TransRepeat, TransRepeatKind, TransStep};
        let mut steps = Vec::new();
        loop {
            let mut values = vec![self.parse_constraint_range()];
            while self.eat(TokenKind::Comma).is_some() {
                values.push(self.parse_constraint_range());
            }
            let mut repeat = None;
            // The expression parser folds a trailing `v [-> n]` into its SVA
            // repetition marker; unwrap it into the step's repetition.
            if let Some(crate::ast::decl::ConstraintRange::Value(e)) = values.last_mut() {
                if let crate::ast::expr::ExprKind::SystemCall { name, args } = &mut e.kind {
                    let kind = match name.as_str() {
                        "$sva_rep_consec" => Some(TransRepeatKind::Consecutive),
                        "$sva_rep_goto" => Some(TransRepeatKind::Goto),
                        "$sva_rep_noncon" => Some(TransRepeatKind::NonConsecutive),
                        _ => None,
                    };
                    if let (Some(kind), 3) = (kind, args.len()) {
                        let hi = args.pop();
                        let lo = args.pop().unwrap();
                        let operand = args.pop().unwrap();
                        *e = operand;
                        repeat = Some(TransRepeat { kind, lo, hi });
                    }
                }
            }
            if repeat.is_none() && self.at(TokenKind::LBracket) {
                self.bump();
                let kind = match self.current_kind() {
                    TokenKind::Star => Some(TransRepeatKind::Consecutive),
                    TokenKind::Arrow => Some(TransRepeatKind::Goto),
                    TokenKind::Assign => Some(TransRepeatKind::NonConsecutive),
                    _ => None,
                };
                match kind {
                    Some(kind) => {
                        self.bump();
                        let lo = self.parse_expression();
                        let hi = if self.eat(TokenKind::Colon).is_some() {
                            Some(self.parse_expression())
                        } else {
                            None
                        };
                        repeat = Some(TransRepeat { kind, lo, hi });
                    }
                    None => self.error("expected [*, [-> or [= in a transition"),
                }
                self.expect(TokenKind::RBracket);
            }
            steps.push(TransStep { values, repeat });
            if self.eat(TokenKind::FatArrow).is_none() {
                break;
            }
        }
        steps
    }

    /// §19.6.1 select_expression, `||` level.
    fn parse_cross_select_or(&mut self) -> crate::ast::decl::CrossSelect {
        let mut l = self.parse_cross_select_and();
        while self.eat(TokenKind::LogOr).is_some() {
            let r = self.parse_cross_select_and();
            l = crate::ast::decl::CrossSelect::Or(Box::new(l), Box::new(r));
        }
        l
    }

    fn parse_cross_select_and(&mut self) -> crate::ast::decl::CrossSelect {
        let mut l = self.parse_cross_select_with();
        while self.eat(TokenKind::LogAnd).is_some() {
            let r = self.parse_cross_select_with();
            l = crate::ast::decl::CrossSelect::And(Box::new(l), Box::new(r));
        }
        l
    }

    fn parse_cross_select_with(&mut self) -> crate::ast::decl::CrossSelect {
        let mut s = self.parse_cross_select_primary();
        while self.eat(TokenKind::KwWith).is_some() {
            self.expect(TokenKind::LParen);
            let e = self.parse_expression();
            self.expect(TokenKind::RParen);
            if self.eat(TokenKind::KwMatches).is_some() {
                let _ = self.parse_expression();
            }
            s = crate::ast::decl::CrossSelect::With(Box::new(s), e);
        }
        s
    }

    fn parse_cross_select_primary(&mut self) -> crate::ast::decl::CrossSelect {
        use crate::ast::decl::CrossSelect;
        if self.eat(TokenKind::LogNot).is_some() {
            return CrossSelect::Not(Box::new(self.parse_cross_select_primary()));
        }
        if self.eat(TokenKind::LParen).is_some() {
            let s = self.parse_cross_select_or();
            self.expect(TokenKind::RParen);
            return s;
        }
        if self.eat(TokenKind::KwBinsof).is_some() {
            self.expect(TokenKind::LParen);
            let cp = self.parse_identifier();
            let bin = if self.eat(TokenKind::Dot).is_some() {
                Some(self.parse_identifier())
            } else {
                None
            };
            self.expect(TokenKind::RParen);
            let intersect = if self.eat(TokenKind::KwIntersect).is_some() {
                self.expect(TokenKind::LBrace);
                let mut ranges = Vec::new();
                while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                    ranges.push(self.parse_constraint_range());
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::RBrace);
                Some(ranges)
            } else {
                None
            };
            return CrossSelect::Binsof { cp, bin, intersect };
        }
        if self.at(TokenKind::Identifier) {
            self.bump();
            return CrossSelect::All;
        }
        self.error(format!(
            "expected a cross bin select expression, found '{}'",
            self.current().text
        ));
        CrossSelect::All
    }

    pub(super) fn parse_covergroup_declaration(&mut self) -> CovergroupDeclaration {
        let start = self.current().span.start;
        self.bump();
        let name = self.parse_identifier();
        // §19.3 constructor formal list (`covergroup cg (int lo, int hi)`),
        // parsed like function ports and bound at `new(...)`.
        let ports = if self.at(TokenKind::LParen) {
            self.parse_function_ports()
        } else {
            Vec::new()
        };
        // Optional coverage event: either `@(event)` / `@@(block_event)` or a
        // `with function sample(tf_port_list)` clause (SV 19.4). The sample
        // function turns the covergroup into one sampled explicitly by call.
        let event = if self.at(TokenKind::At) {
            Some(self.parse_event_control())
        } else {
            None
        };
        let mut sample_ports: Vec<FunctionPort> = Vec::new();
        if self.at(TokenKind::KwWith) {
            self.bump();
            self.expect(TokenKind::KwFunction);
            let _ = self.parse_identifier(); // `sample`
            if self.at(TokenKind::LParen) {
                sample_ports = self.parse_function_ports();
            }
        }
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndgroup) && !self.at(TokenKind::Eof) {
            items.push(self.parse_covergroup_item());
        }
        self.expect(TokenKind::KwEndgroup);
        let endlabel = self.parse_end_label();
        // §19.5: an unlabeled coverpoint on a variable is named after the
        // variable; one on any other expression gets a generated name
        // (`coverpoint#<n>`, n counting coverpoints from 1).
        let mut n_cp = 0usize;
        for it in &mut items {
            if let CovergroupItem::Coverpoint(cp) = it {
                n_cp += 1;
                if cp.name.is_none() {
                    let var = match &cp.expr.kind {
                        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => Some(
                            h.path
                                .iter()
                                .map(|s| s.name.name.as_str())
                                .collect::<Vec<_>>()
                                .join("."),
                        ),
                        _ => None,
                    };
                    cp.name = Some(crate::ast::Identifier {
                        name: var.unwrap_or_else(|| format!("coverpoint#{}", n_cp)),
                        span: cp.expr.span,
                    });
                }
            }
        }
        CovergroupDeclaration {
            name,
            ports,
            sample_ports,
            event,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    fn parse_covergroup_item(&mut self) -> CovergroupItem {
        let start = self.current().span.start;
        let mut name = None;
        if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Colon {
            name = Some(self.parse_identifier());
            self.expect(TokenKind::Colon);
        }

        match self.current_kind() {
            TokenKind::KwCoverpoint => {
                self.bump();
                // §19.5 (SV-2023) `coverpoint real <expr>`. Gated on --sv2023
                // so that under SV-2017 `real` stays whatever it was before
                // (an ordinary expression token) rather than being silently
                // swallowed as a modifier.
                let is_real = crate::is_sv2023() && self.eat(TokenKind::KwReal).is_some();
                // `parse_expression` includes `iff` as a low-precedence
                // binary op (`BinaryOp::Iff`), so `v iff (guard)` parses
                // as `Binary(Iff, v, guard)` — split that back into
                // `expr = v, iff_guard = guard` here. Standalone `iff` in
                // its own token still works as a fallback.
                let mut iff_guard: Option<crate::ast::expr::Expression> = None;
                let parsed_expr = self.parse_expression();
                let expr = match parsed_expr.kind {
                    crate::ast::expr::ExprKind::Binary {
                        op: crate::ast::expr::BinaryOp::Iff,
                        left,
                        right,
                    } => {
                        iff_guard = Some(*right);
                        *left
                    }
                    _ => parsed_expr,
                };
                if self.at(TokenKind::KwIff) {
                    self.bump();
                    if self.eat(TokenKind::LParen).is_some() {
                        iff_guard = Some(self.parse_expression());
                        let _ = self.eat(TokenKind::RParen);
                    }
                }
                let mut bins: Vec<crate::ast::decl::CoverBin> = Vec::new();
                let mut cp_options: Vec<(String, crate::ast::expr::Expression)> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    // Parse a sequence of bin declarations until matching `}`.
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        let bin_start = self.current().span.start;
                        // Optional `wildcard` modifier (LRM §19.5) — applies
                        // to the next `bins`/`ignore_bins`/`illegal_bins`.
                        let is_wildcard = self.eat(TokenKind::KwWildcard).is_some();
                        let kind_tok = self.current_kind();
                        let kind = match kind_tok {
                            TokenKind::KwBins => Some(crate::ast::decl::CoverBinKind::Bins),
                            TokenKind::KwIgnore_bins => {
                                Some(crate::ast::decl::CoverBinKind::Ignore)
                            }
                            TokenKind::KwIllegal_bins => {
                                Some(crate::ast::decl::CoverBinKind::Illegal)
                            }
                            // Identifier text fallback for tokenizer variants.
                            TokenKind::Identifier => match self.current().text.as_str() {
                                "bins" => Some(crate::ast::decl::CoverBinKind::Bins),
                                "ignore_bins" => Some(crate::ast::decl::CoverBinKind::Ignore),
                                "illegal_bins" => Some(crate::ast::decl::CoverBinKind::Illegal),
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some(k) = kind {
                            self.bump(); // bins / ignore_bins / illegal_bins / KwBins
                            let bin_name = if self.at(TokenKind::Identifier) {
                                self.parse_identifier()
                            } else {
                                // §19.5: a bin is named by an identifier; a
                                // reserved word (`small`, `large`) is not one.
                                self.error(format!(
                                    "expected a bin name, found '{}'",
                                    self.current().text
                                ));
                                self.skip_bin_body_to_semicolon();
                                if self.at(TokenKind::Semicolon) {
                                    self.bump();
                                }
                                continue;
                            };
                            // §19.5.1 `[]` or `[N]` array form.
                            let mut is_array = false;
                            let mut array_size = None;
                            if self.at(TokenKind::LBracket) {
                                is_array = true;
                                self.bump();
                                if !self.at(TokenKind::RBracket) {
                                    array_size = Some(self.parse_expression());
                                }
                                self.expect(TokenKind::RBracket);
                            }
                            // `=` then bin body.
                            if self.eat(TokenKind::Assign).is_some() {
                                let mut values: Vec<crate::ast::decl::ConstraintRange> = Vec::new();
                                let mut transitions: Vec<Vec<crate::ast::decl::TransStep>> =
                                    Vec::new();
                                let mut bin_kind = k;
                                if self.at(TokenKind::LBrace) {
                                    self.bump();
                                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                                        values.push(self.parse_constraint_range());
                                        if self.at(TokenKind::Comma) {
                                            self.bump();
                                        }
                                    }
                                    if self.at(TokenKind::RBrace) {
                                        self.bump();
                                    }
                                } else if self.at(TokenKind::KwDefault) {
                                    // `bins other = default;` — LRM §19.5
                                    // catches every value not matched by any
                                    // explicit bin in the same coverpoint.
                                    self.bump();
                                    bin_kind = crate::ast::decl::CoverBinKind::Default;
                                } else if self.at(TokenKind::LParen) {
                                    // §19.5.2 trans_list: `(set), (set), ...`.
                                    loop {
                                        self.expect(TokenKind::LParen);
                                        transitions.push(self.parse_trans_set());
                                        self.expect(TokenKind::RParen);
                                        if !(self.at(TokenKind::Comma)
                                            && self.peek_kind() == TokenKind::LParen)
                                        {
                                            break;
                                        }
                                        self.bump();
                                    }
                                } else {
                                    // Forms we don't handle yet — gobble to
                                    // the terminating `;` (depth-aware).
                                    self.skip_bin_body_to_semicolon();
                                }
                                bins.push(crate::ast::decl::CoverBin {
                                    name: bin_name,
                                    kind: bin_kind,
                                    values,
                                    array_form: is_array,
                                    array_size,
                                    is_wildcard,
                                    transitions,
                                    span: self.span_from(bin_start),
                                });
                            } else {
                                self.skip_bin_body_to_semicolon();
                            }
                            if self.at(TokenKind::Semicolon) {
                                self.bump();
                            }
                        } else if self.at(TokenKind::Identifier)
                            && (self.current().text == "option"
                                || self.current().text == "type_option")
                        {
                            // §19.7 coverpoint-level `option.NAME = expr;`.
                            self.bump(); // option / type_option
                            if self.eat(TokenKind::Dot).is_some() {
                                let opt_name = self.parse_identifier().name;
                                if self.eat(TokenKind::Assign).is_some() {
                                    let val = self.parse_expression();
                                    cp_options.push((opt_name, val));
                                }
                            }
                            if self.at(TokenKind::Semicolon) {
                                self.bump();
                            }
                        } else {
                            // Not a bin keyword — skip token to make progress.
                            self.bump();
                        }
                    }
                    if self.at(TokenKind::RBrace) {
                        self.bump();
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Coverpoint(Coverpoint {
                    name,
                    expr,
                    is_real,
                    iff_guard,
                    bins,
                    options: cp_options,
                    span: self.span_from(start),
                })
            }
            TokenKind::KwCross => {
                self.bump();
                let mut ids = Vec::new();
                loop {
                    ids.push(self.parse_identifier());
                    if !self.at(TokenKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                // LRM §19.6 `iff (guard)` — sample is skipped when guard
                // is false. (Note: unlike for coverpoint, `parse_expression`
                // doesn't slurp `iff` here because we already consumed
                // identifiers.)
                let mut iff_guard: Option<crate::ast::expr::Expression> = None;
                if self.at(TokenKind::KwIff) {
                    self.bump();
                    if self.eat(TokenKind::LParen).is_some() {
                        iff_guard = Some(self.parse_expression());
                        let _ = self.eat(TokenKind::RParen);
                    }
                }
                let mut bins: Vec<crate::ast::decl::CrossBin> = Vec::new();
                let mut options: Vec<(String, crate::ast::expr::Expression)> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    // §19.6.1 cross body: bins selections and options. Other
                    // items are skipped depth-tracked.
                    loop {
                        if self.at(TokenKind::Eof) {
                            break;
                        }
                        if self.at(TokenKind::RBrace) {
                            self.bump();
                            break;
                        }
                        let kind = match self.current_kind() {
                            TokenKind::KwBins => Some(crate::ast::decl::CoverBinKind::Bins),
                            TokenKind::KwIgnore_bins => {
                                Some(crate::ast::decl::CoverBinKind::Ignore)
                            }
                            TokenKind::KwIllegal_bins => {
                                Some(crate::ast::decl::CoverBinKind::Illegal)
                            }
                            _ => None,
                        };
                        if let Some(kind) = kind {
                            self.bump();
                            if !self.at(TokenKind::Identifier) {
                                self.error(format!(
                                    "expected a bin name, found '{}'",
                                    self.current().text
                                ));
                                self.skip_bin_body_to_semicolon();
                                let _ = self.eat(TokenKind::Semicolon);
                                continue;
                            }
                            let bin_name = self.parse_identifier();
                            self.expect(TokenKind::Assign);
                            let select = self.parse_cross_select_or();
                            let mut iff_guard = None;
                            if self.eat(TokenKind::KwIff).is_some() {
                                self.expect(TokenKind::LParen);
                                iff_guard = Some(self.parse_expression());
                                self.expect(TokenKind::RParen);
                            }
                            self.expect(TokenKind::Semicolon);
                            bins.push(crate::ast::decl::CrossBin {
                                name: bin_name,
                                kind,
                                select,
                                iff_guard,
                            });
                            continue;
                        }
                        if self.at(TokenKind::Identifier)
                            && (self.current().text == "option"
                                || self.current().text == "type_option")
                            && self.peek_kind() == TokenKind::Dot
                        {
                            self.bump();
                            self.bump();
                            let opt_name = self.parse_identifier().name;
                            if self.eat(TokenKind::Assign).is_some() {
                                options.push((opt_name, self.parse_expression()));
                            }
                            let _ = self.eat(TokenKind::Semicolon);
                            continue;
                        }
                        // Skip one token (depth-aware for nested braces).
                        if self.at(TokenKind::LBrace) {
                            let mut depth = 1usize;
                            self.bump();
                            while depth > 0 && !self.at(TokenKind::Eof) {
                                if self.at(TokenKind::LBrace) {
                                    depth += 1;
                                } else if self.at(TokenKind::RBrace) {
                                    depth -= 1;
                                }
                                self.bump();
                            }
                        } else {
                            self.bump();
                        }
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Cross(Cross {
                    name,
                    items: ids,
                    iff_guard,
                    bins,
                    options,
                    span: self.span_from(start),
                })
            }
            TokenKind::Identifier
                if self.current().text == "option" || self.current().text == "type_option" =>
            {
                let id = self.parse_identifier();
                let is_type = id.name == "type_option";
                self.expect(TokenKind::Dot);
                let opt_name = self.parse_identifier().name;
                self.expect(TokenKind::Assign);
                let val = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                if is_type {
                    CovergroupItem::TypeOption {
                        name: opt_name,
                        val,
                    }
                } else {
                    CovergroupItem::Option {
                        name: opt_name,
                        val,
                    }
                }
            }
            _ => {
                self.error(format!(
                    "unexpected token in covergroup: {:?}",
                    self.current().text
                ));
                self.bump();
                CovergroupItem::Option {
                    name: "error".to_string(),
                    val: Expression::new(ExprKind::Empty, self.span_from(start)),
                }
            }
        }
    }

    /// Parse a single term of a `solve ... before ...` list. SV allows the
    /// solve/before operands to be member-select and index-select lvalues
    /// (e.g. `mseccfg.mml`, `pmp_cfg[i].w`), not just bare identifiers.
    /// Returns the root identifier, which the elaborator's solve-ordering
    /// checks consult, and the whole operand as an identifier path (an
    /// index select held on its segment), which the solver orders by.
    fn parse_solve_term(&mut self) -> (Identifier, Expression) {
        let start = self.current().span.start;
        let root = self.parse_identifier();
        let mut path = vec![crate::ast::expr::HierPathSegment {
            name: root.clone(),
            selects: Vec::new(),
        }];
        loop {
            if self.at(TokenKind::Dot) {
                self.bump();
                let id = self.parse_identifier();
                path.push(crate::ast::expr::HierPathSegment {
                    name: id,
                    selects: Vec::new(),
                });
            } else if self.at(TokenKind::LBracket) {
                self.bump();
                let idx = self.parse_expression();
                self.expect(TokenKind::RBracket);
                if let Some(last) = path.last_mut() {
                    last.selects.push(idx);
                }
            } else {
                break;
            }
        }
        let span = self.span_from(start);
        let e = Expression::new(
            ExprKind::Ident(crate::ast::expr::HierarchicalIdentifier {
                root: None,
                path,
                span,
                cached_signal_id: std::cell::Cell::new(None),
                cached_resolved_name: std::cell::OnceCell::new(),
            }),
            span,
        );
        (root, e)
    }

    pub(crate) fn parse_constraint_item(&mut self) -> ConstraintItem {
        let start = self.current().span.start;
        match self.current_kind() {
            TokenKind::KwSolve => {
                self.bump();
                let mut before = Vec::new();
                let mut before_paths = Vec::new();
                loop {
                    let (id, e) = self.parse_solve_term();
                    before.push(id);
                    before_paths.push(e);
                    if !self.at(TokenKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                self.expect(TokenKind::KwBefore);
                let mut after = Vec::new();
                let mut after_paths = Vec::new();
                loop {
                    let (id, e) = self.parse_solve_term();
                    after.push(id);
                    after_paths.push(e);
                    if !self.at(TokenKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                self.expect(TokenKind::Semicolon);
                ConstraintItem::Solve {
                    before,
                    after,
                    before_paths,
                    after_paths,
                    span: self.span_from(start),
                }
            }
            TokenKind::KwIf => {
                self.bump();
                self.expect(TokenKind::LParen);
                let cond = self.parse_expression();
                self.expect(TokenKind::RParen);
                let then_item = self.parse_constraint_item();
                let else_item = if self.at(TokenKind::KwElse) {
                    self.bump();
                    Some(Box::new(self.parse_constraint_item()))
                } else {
                    None
                };
                ConstraintItem::IfElse {
                    condition: cond,
                    then_item: Box::new(then_item),
                    else_item,
                    span: self.span_from(start),
                }
            }
            TokenKind::KwForeach => {
                self.bump();
                self.expect(TokenKind::LParen);
                let array = self.parse_hierarchical_identifier();
                let array_expr = crate::ast::expr::Expression::new(
                    crate::ast::expr::ExprKind::Ident(array),
                    self.span_from(start),
                );
                self.expect(TokenKind::LBracket);
                let mut vars = Vec::new();
                loop {
                    if self.at(TokenKind::Identifier) {
                        vars.push(Some(self.parse_identifier()));
                    } else if self.at(TokenKind::Comma) {
                        vars.push(None);
                    } else if self.at(TokenKind::RBracket) {
                        break;
                    } else {
                        self.error("expected identifier or comma in foreach");
                        self.bump();
                    }
                    if !self.at(TokenKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                self.expect(TokenKind::RBracket);
                self.expect(TokenKind::RParen);
                let item = self.parse_constraint_item();
                ConstraintItem::Foreach {
                    array: array_expr,
                    vars,
                    item: Box::new(item),
                    span: self.span_from(start),
                }
            }
            TokenKind::KwSoft => {
                self.bump();
                ConstraintItem::Soft(Box::new(self.parse_constraint_item()))
            }
            TokenKind::KwDisable => {
                // `disable soft <expr>;` — accept and treat as a no-op block.
                self.bump();
                if self.at(TokenKind::KwSoft) {
                    self.bump();
                }
                let _expr = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                ConstraintItem::Block(Vec::new())
            }
            TokenKind::KwUnique => {
                // `unique { expr_list };` — LRM §18.5.5. Desugared at parse
                // time into the pairwise inequalities it denotes
                // (`e[i] != e[j]` for all i<j) so the constraint solver only
                // ever sees plain relational items.
                self.bump();
                let mut exprs: Vec<crate::ast::expr::Expression> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        exprs.push(self.parse_expression());
                        if self.at(TokenKind::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                    self.expect(TokenKind::RBrace);
                }
                if self.at(TokenKind::Semicolon) {
                    self.bump();
                }
                let span = self.span_from(start);
                if exprs.len() == 1 {
                    // A single-expression list names a whole array (`unique
                    // {gpr}`) — its element count is only known at solve
                    // time, so keep it as a dedicated item for the solver.
                    ConstraintItem::Unique { exprs, span }
                } else {
                    let mut items = Vec::new();
                    for i in 0..exprs.len() {
                        for j in (i + 1)..exprs.len() {
                            items.push(ConstraintItem::Expr(crate::ast::expr::Expression::new(
                                crate::ast::expr::ExprKind::Binary {
                                    op: crate::ast::expr::BinaryOp::Neq,
                                    left: Box::new(exprs[i].clone()),
                                    right: Box::new(exprs[j].clone()),
                                },
                                span,
                            )));
                        }
                    }
                    ConstraintItem::Block(items)
                }
            }
            TokenKind::LBrace => {
                self.bump();
                let mut items = Vec::new();
                while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                    items.push(self.parse_constraint_item());
                }
                self.expect(TokenKind::RBrace);
                ConstraintItem::Block(items)
            }
            _ => {
                // The paren-primary parser needs to accept `( expr dist {...} )`
                // only in constraint context.
                let saved_in_constraint = self.in_constraint;
                self.in_constraint = true;
                let expr = self.parse_expression();
                self.in_constraint = saved_in_constraint;
                // Nonstandard `-> ( expr dist {...} )`: the dist body was
                // captured inside the parentheses; the LogImplies chain that
                // `parse_expression` built around it becomes real constraint
                // implications so the solver applies the WEIGHTS only when the
                // guard holds (a reference simulator warns about the parens
                // and accepts exactly this reading).
                if let Some((range, dist_weights)) = self.pending_paren_dist.pop() {
                    let span = self.span_from(start);
                    self.expect(TokenKind::Semicolon);
                    return Self::dist_item_peeling_implications(expr, range, dist_weights, span);
                }
                if self.at(TokenKind::KwDist) {
                    // `expr dist { value (:= | :/ ) weight, ... };` — LRM
                    // §18.5.4. Weights are captured into a parallel vector
                    // so the runtime distribution picker can honor them.
                    // `expr` may be a LogImplies chain (`en -> kind dist {…}`):
                    // the expression parser binds `->` before we ever see
                    // `dist`, so peel those into constraint implications —
                    // otherwise the dist attached to the whole implication
                    // EXPRESSION, whose value nothing targets, and the weights
                    // were silently dropped (only membership survived, via the
                    // resample-until-satisfied loop).
                    self.bump();
                    let (range, dist_weights) = self.parse_dist_body();
                    let span = self.span_from(start);
                    self.expect(TokenKind::Semicolon);
                    return Self::dist_item_peeling_implications(expr, range, dist_weights, span);
                }
                if self.at(TokenKind::KwInside) {
                    self.bump();
                    self.expect(TokenKind::LBrace);
                    let mut range = Vec::new();
                    loop {
                        range.push(self.parse_constraint_range());
                        if !self.at(TokenKind::Comma) {
                            break;
                        }
                        self.bump();
                    }
                    self.expect(TokenKind::RBrace);
                    let span = self.span_from(start);
                    self.expect(TokenKind::Semicolon);
                    ConstraintItem::Inside {
                        expr,
                        range,
                        is_dist: false,
                        dist_weights: Vec::new(),
                        span,
                    }
                } else if self.at(TokenKind::Arrow) {
                    self.bump();
                    let constraint = self.parse_constraint_item();
                    ConstraintItem::Implication {
                        condition: expr,
                        constraint: Box::new(constraint),
                        span: self.span_from(start),
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                    ConstraintItem::Expr(expr)
                }
            }
        }
    }

    /// The `{ value (:= | :/) weight, ... }` body of a `dist` constraint,
    /// cursor on the LBrace. Shared by the plain form, the implication-chain
    /// form, and the parenthesized form the paren-primary captures.
    pub(super) fn parse_dist_body(
        &mut self,
    ) -> (
        Vec<ConstraintRange>,
        Vec<Option<crate::ast::decl::DistWeight>>,
    ) {
        self.expect(TokenKind::LBrace);
        let mut range = Vec::new();
        let mut dist_weights: Vec<Option<crate::ast::decl::DistWeight>> = Vec::new();
        loop {
            range.push(self.parse_constraint_range());
            if self.at(TokenKind::ColonAssign) {
                self.bump();
                let w = self.parse_expression();
                dist_weights.push(Some(crate::ast::decl::DistWeight::Each(w)));
            } else if self.at(TokenKind::ColonSlash) {
                self.bump();
                let w = self.parse_expression();
                dist_weights.push(Some(crate::ast::decl::DistWeight::Total(w)));
            } else {
                dist_weights.push(None);
            }
            if !self.at(TokenKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(TokenKind::RBrace);
        (range, dist_weights)
    }

    /// Wrap a dist body around `expr`, peeling any top-level `->` (which the
    /// EXPRESSION parser bound as LogImplies before the `dist` keyword was
    /// visible) back into constraint implications: `a -> b dist {…}` is
    /// `Implication{a, Inside{b, dist}}` per §18.5.6, not a dist over the
    /// 1-bit implication result.
    fn dist_item_peeling_implications(
        expr: crate::ast::expr::Expression,
        range: Vec<ConstraintRange>,
        dist_weights: Vec<Option<crate::ast::decl::DistWeight>>,
        span: crate::ast::Span,
    ) -> ConstraintItem {
        match expr.kind {
            crate::ast::expr::ExprKind::Binary {
                op: crate::ast::expr::BinaryOp::LogImplies,
                left,
                right,
            } => ConstraintItem::Implication {
                condition: *left,
                constraint: Box::new(Self::dist_item_peeling_implications(
                    *right,
                    range,
                    dist_weights,
                    span,
                )),
                span,
            },
            crate::ast::expr::ExprKind::Paren(inner) => {
                Self::dist_item_peeling_implications(*inner, range, dist_weights, span)
            }
            _ => ConstraintItem::Inside {
                expr,
                range,
                is_dist: true,
                dist_weights,
                span,
            },
        }
    }

    fn parse_constraint_range(&mut self) -> ConstraintRange {
        if self.at(TokenKind::LBracket) {
            self.bump();
            let lo = self.parse_expression();
            self.expect(TokenKind::Colon);
            let hi = self.parse_expression();
            self.expect(TokenKind::RBracket);
            ConstraintRange::Range { lo, hi }
        } else {
            ConstraintRange::Value(self.parse_expression())
        }
    }
}

impl Parser {
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
