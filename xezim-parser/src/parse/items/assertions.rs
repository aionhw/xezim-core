use super::*;

impl<'a> Parser<'a> {
    /// §16.10: the `assertion_variable_declaration`s at the head of a
    /// property or sequence body, each kept as
    /// `$sva_local(<type>, <name> [, <init>])` for the simulator, which gives
    /// every evaluation attempt its own copy.
    pub(super) fn parse_sva_local_declarations(&mut self) -> Vec<Expression> {
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
            let tstart = self.current_span().start;
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
                // A.2.4 / §16.10: `variable_identifier { variable_dimension }`:
                // a local may be an unpacked array (`bit flags[3:0];`). It was
                // a parse error (#618). Its element selects read as the packed
                // equivalent's, so the dimensions fold into the type.
                let dims = if self.at(TokenKind::LBracket) {
                    self.parse_unpacked_dimensions()
                } else {
                    Vec::new()
                };
                let local_type = self.sva_local_array_type(&data_type, &name, dims);
                let mut args = vec![
                    Expression::new(ExprKind::TypeLiteral(Box::new(local_type)), span),
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

    /// An assertion local declared with unpacked dimensions, as the packed
    /// type that selects the same elements: each fixed unpacked dimension
    /// (`[3:0]`, `[N]` as `[0:N-1]`) outside the element's own packed ones,
    /// an integer atom element as its sized vector. Any other element type,
    /// or a dynamic dimension, is an error rather than a silently scalar local.
    fn sva_local_array_type(
        &mut self,
        dt: &DataType,
        name: &Identifier,
        dims: Vec<UnpackedDimension>,
    ) -> DataType {
        if dims.is_empty() {
            return dt.clone();
        }
        let unsupported = |this: &mut Self, what: &str| {
            this.diagnostics.push(crate::diagnostics::Diagnostic::error(
                format!(
                    "unpacked dimensions on assertion local '{}' {what} are not supported \
                     (IEEE 1800-2023 §16.10)",
                    name.name
                ),
                name.span,
            ));
            dt.clone()
        };
        let int = |v: i64, span: crate::ast::Span| {
            Expression::new(
                ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
                    size: None,
                    signed: false,
                    base: crate::ast::expr::NumberBase::Decimal,
                    value: v.to_string(),
                    cached_val: crate::ast::cache::LiteralCache::new(None),
                }),
                span,
            )
        };
        let mut outer = Vec::new();
        for d in dims {
            match d {
                UnpackedDimension::Range { left, right, span } => {
                    outer.push(PackedDimension::Range { left, right, span });
                }
                UnpackedDimension::Expression { expr, span } => {
                    let hi = Expression::new(
                        ExprKind::Binary {
                            op: crate::ast::expr::BinaryOp::Sub,
                            left: expr,
                            right: Box::new(int(1, span)),
                        },
                        span,
                    );
                    outer.push(PackedDimension::Range {
                        left: Box::new(int(0, span)),
                        right: Box::new(hi),
                        span,
                    });
                }
                _ => return unsupported(self, "that are not fixed-size"),
            }
        }
        let (kind, signing, inner, span) = match dt {
            DataType::IntegerVector {
                kind,
                signing,
                dimensions,
                span,
            } => (*kind, *signing, dimensions.clone(), *span),
            DataType::IntegerAtom {
                kind,
                signing,
                span,
            } => {
                use crate::ast::types::IntegerAtomType as A;
                let (w, four, signed) = match kind {
                    A::Byte => (8, false, true),
                    A::ShortInt => (16, false, true),
                    A::Int => (32, false, true),
                    A::LongInt => (64, false, true),
                    A::Integer => (32, true, true),
                    A::Time => (64, true, false),
                };
                let sign = signing.or(signed.then_some(crate::ast::types::Signing::Signed));
                let elem = PackedDimension::Range {
                    left: Box::new(int(w - 1, *span)),
                    right: Box::new(int(0, *span)),
                    span: *span,
                };
                let k = if four {
                    crate::ast::types::IntegerVectorType::Logic
                } else {
                    crate::ast::types::IntegerVectorType::Bit
                };
                (k, sign, vec![elem], *span)
            }
            _ => return unsupported(self, "of this element type"),
        };
        // §11.8.1: a select of a packed array is unsigned, so a signed
        // element (`int counts[4]`) reads back unsigned.
        if signing == Some(crate::ast::types::Signing::Signed) {
            self.diagnostics
                .push(crate::diagnostics::Diagnostic::warning(
                    format!(
                        "element selects of assertion local '{}' read unsigned: its unpacked \
                         dimensions fold into a packed array (IEEE 1800-2023 §16.10, §11.8.1)",
                        name.name
                    ),
                    name.span,
                ));
        }
        outer.extend(inner);
        DataType::IntegerVector {
            kind,
            signing,
            dimensions: outer,
            span,
        }
    }

    /// §16.8.2 local variable formal arguments (`local input int v`): the
    /// formal is a local variable of each attempt initialised from its
    /// actual. The body's references are renamed to a local `v$lf`, declared
    /// with the formal (substituted by the actual at instantiation) as its
    /// initialiser, so the attempt can assign it without touching the actual.
    pub(super) fn sva_bind_local_formals(
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
    pub(super) fn infer_procedural_assertion_clocks(stmt: &mut crate::ast::stmt::Statement) {
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
                    a.inferred_clock = Some(Box::new(clock.clone()));
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
    pub(super) fn expr_idents(e: &Expression, out: &mut Vec<String>) {
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
            ExprKind::SvaClocked { events, body } => {
                for event in events {
                    Self::expr_idents(&event.expr, out);
                    if let Some(g) = &event.iff {
                        Self::expr_idents(g, out);
                    }
                }
                Self::expr_idents(body, out);
            }
            _ => {}
        }
    }

    /// §16.10: only a local variable can be assigned in a match item list
    /// (`(seq, v = e)`); `locals` are the names the body may assign (its
    /// local variables and formals).
    pub(in crate::parse) fn check_sva_match_assignments(
        &mut self,
        e: &Expression,
        locals: &[String],
    ) {
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
    pub(super) fn sva_assignable_names(decls: &[Expression], ports: &[Identifier]) -> Vec<String> {
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
                cached_signal_id: crate::ast::cache::SignalCache::new(None),
                cached_resolved_name: crate::ast::cache::NameCache::new(),
                bound: crate::ast::binding::Bound::UNSET,
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
            ExprKind::SvaClocked { events, body } => {
                for event in events {
                    Self::sva_rename_ident(&mut event.expr, from, to);
                    if let Some(g) = &mut event.iff {
                        Self::sva_rename_ident(g, from, to);
                    }
                }
                Self::sva_rename_ident(body, from, to);
            }
            _ => {}
        }
    }

    /// Wrap a property or sequence body in its local variable declarations
    /// (`$sva_locals(<decl>..., <body>)`), if it has any.
    pub(super) fn sva_wrap_locals(decls: Vec<Expression>, body: Expression) -> Expression {
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

    /// §16.5/§16.6: consume an SVA property/sequence port list and return
    /// the FORMAL NAMES in declaration order. Each top-level comma-separated
    /// segment may carry `local`/direction keywords, a type, and a default
    /// (`= expr`); the port name is the last identifier before the default
    /// (or before the segment end). Called with the cursor ON the `(`.
    /// The formal port names of a property or sequence declaration, its
    /// §16.8.2 `local [input]` formals with their types, and the §16.8
    /// default actual argument of each formal (parallel to the names).
    #[allow(clippy::type_complexity)]
    pub(super) fn parse_sva_port_names(
        &mut self,
    ) -> (
        Vec<Identifier>,
        Vec<(Identifier, DataType)>,
        Vec<Option<Expression>>,
    ) {
        let mut ports: Vec<Identifier> = Vec::new();
        let mut local_ports: Vec<(Identifier, DataType)> = Vec::new();
        let mut defaults: Vec<Option<Expression>> = Vec::new();
        // The default of the formal being read.
        let mut default: Option<Expression> = None;
        // Whether the formal being read is declared with a type.
        let mut typed = false;
        self.bump(); // (
        let mut depth: i32 = 1;
        let mut last_ident: Option<Identifier> = None;
        let mut in_default = false;
        let mut port_start = true;
        // The type of the current formal when it is a `local [input]` one.
        let mut local_type: Option<DataType> = None;
        let finish = |last: &mut Option<Identifier>,
                      local: &mut Option<DataType>,
                      default: &mut Option<Expression>,
                      ports: &mut Vec<Identifier>,
                      local_ports: &mut Vec<(Identifier, DataType)>,
                      defaults: &mut Vec<Option<Expression>>| {
            let default = default.take();
            if let Some(id) = last.take() {
                if let Some(dt) = local.take() {
                    local_ports.push((id.clone(), dt));
                }
                ports.push(id);
                defaults.push(default);
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
                let tstart = self.current_span().start;
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
                typed = !matches!(dt, DataType::Implicit { .. });
                local_type = input.then_some(dt);
            }
            port_start = false;
            match self.current_kind() {
                TokenKind::LParen | TokenKind::LBracket => {
                    typed |= !in_default;
                    depth += 1;
                    self.bump();
                }
                TokenKind::RParen | TokenKind::RBracket => {
                    depth -= 1;
                    if depth == 0 {
                        finish(
                            &mut last_ident,
                            &mut local_type,
                            &mut default,
                            &mut ports,
                            &mut local_ports,
                            &mut defaults,
                        );
                    }
                    self.bump();
                }
                TokenKind::Comma if depth == 1 => {
                    finish(
                        &mut last_ident,
                        &mut local_type,
                        &mut default,
                        &mut ports,
                        &mut local_ports,
                        &mut defaults,
                    );
                    in_default = false;
                    typed = false;
                    port_start = true;
                    self.bump();
                }
                TokenKind::Assign if depth == 1 => {
                    // default value: the name is already in last_ident;
                    // idents inside the default must not overwrite it.
                    in_default = true;
                    self.bump();
                    // §16.8: keep the default actual argument when it parses
                    // as one expression up to the end of the formal; any
                    // other shape (an edge event) is skipped token by token
                    // below, as before.
                    let save_pos = self.pos;
                    let save_diag = self.diagnostics.len();
                    let save_seq = self.in_sva_seq;
                    self.in_sva_seq = true;
                    let e = self.parse_expression();
                    self.in_sva_seq = save_seq;
                    if self.diagnostics.len() == save_diag
                        && matches!(self.current_kind(), TokenKind::Comma | TokenKind::RParen)
                    {
                        default = Some(if typed {
                            e
                        } else {
                            Self::sva_self_determined(e)
                        });
                    } else {
                        self.diagnostics.truncate(save_diag);
                        self.pos = save_pos;
                    }
                }
                TokenKind::Identifier | TokenKind::EscapedIdentifier => {
                    if !in_default {
                        // `my_t x`: a name after a name is typed by the first.
                        typed |= last_ident.is_some();
                        last_ident = Some(self.parse_identifier());
                    } else {
                        self.bump();
                    }
                }
                kind => {
                    typed |= !in_default && kind != TokenKind::KwUntyped;
                    self.bump();
                }
            }
        }
        (ports, local_ports, defaults)
    }

    /// §16.8: the actual argument of an untyped formal is cast to its
    /// self-determined type before it is substituted, so an operator
    /// expression does not take the width of the place the formal is used
    /// in (`x == 8'hff` with `~v` for `x`). A size cast to the operand's own
    /// width evaluates it that way and keeps its signedness (§6.24.1).
    /// Operands that are sized by themselves, and sequence or property
    /// expressions, are left as written.
    fn sva_self_determined(e: Expression) -> Expression {
        use crate::ast::expr::NumberLiteral;
        let context_sized = match &e.kind {
            ExprKind::Unary { op, .. } => {
                matches!(op, UnaryOp::BitNot | UnaryOp::Minus | UnaryOp::Plus)
            }
            ExprKind::Binary { op, .. } => matches!(
                op,
                BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod
                    | BinaryOp::Power
                    | BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::BitXnor
                    | BinaryOp::ShiftLeft
                    | BinaryOp::ShiftRight
                    | BinaryOp::ArithShiftLeft
                    | BinaryOp::ArithShiftRight
            ),
            ExprKind::Conditional { .. } => true,
            ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => true,
            _ => false,
        };
        if !context_sized {
            return e;
        }
        let span = e.span;
        let bits = Expression::new(
            ExprKind::SystemCall {
                name: "$bits".to_string(),
                args: vec![e.clone()],
            },
            span,
        );
        Expression::new(
            ExprKind::SystemCall {
                name: "$__xz_size_cast".to_string(),
                args: vec![bits, e],
            },
            span,
        )
    }
}
