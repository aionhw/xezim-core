use super::*;

impl<'a> Parser<'a> {
    /// §18.5.1, A.1.11: `constraint C::name { ... }` in a package defines the
    /// body of the `extern constraint name;` its class `C` of the same package
    /// declares; the body is put on that prototype (#654).
    pub(super) fn parse_package_ooc_constraint(&mut self, items: &mut [PackageItem]) {
        let start = self.current_span().start;
        self.expect(TokenKind::KwConstraint);
        let hid = self.parse_hierarchical_identifier();
        let mut body = Vec::new();
        if self.at(TokenKind::LBrace) {
            self.bump();
            while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                body.push(self.parse_constraint_item(ConstraintPos::BlockItem));
            }
            self.expect(TokenKind::RBrace);
        }
        self.eat(TokenKind::Semicolon);
        let [.., class, name] = hid.path.as_slice() else {
            self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                "an out-of-block constraint names its class: `constraint C::name { ... }` \
                 (IEEE 1800-2023 §18.5.1)",
                self.span_from(start),
            ));
            return;
        };
        let prototype = items.iter_mut().find_map(|it| match it {
            PackageItem::Class(c) if c.name.name == class.name.name => {
                c.items.iter_mut().find_map(|ci| match ci {
                    crate::ast::decl::ClassItem::Constraint(k)
                        if k.name.name == name.name.name && !k.has_body =>
                    {
                        Some(std::sync::Arc::make_mut(k))
                    }
                    _ => None,
                })
            }
            _ => None,
        });
        match prototype {
            Some(k) => {
                k.items = body;
                k.has_body = true;
            }
            None => self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                format!(
                    "class '{}' of this package declares no `extern constraint {};` \
                     (IEEE 1800-2023 §18.5.1)",
                    class.name.name, name.name.name
                ),
                self.span_from(start),
            )),
        }
    }

    /// Parse a single term of a `solve ... before ...` list. SV allows the
    /// solve/before operands to be member-select and index-select lvalues
    /// (e.g. `mseccfg.mml`, `pmp_cfg[i].w`), not just bare identifiers.
    /// Returns the root identifier, which the elaborator's solve-ordering
    /// checks consult, and the whole operand as an identifier path (an
    /// index select held on its segment), which the solver orders by.
    fn parse_solve_term(&mut self) -> (Identifier, Expression) {
        let start = self.current_span().start;
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
        // §18.5.10: `constraint_primary` ends in an optional `( )`, which
        // orders an array's size: `solve sel before arr.size();`. It is the
        // call `arr.size()` the constraints themselves read.
        let call =
            self.at(TokenKind::LParen) && self.peek_kind() == TokenKind::RParen && path.len() > 1;
        if call {
            self.bump();
            self.bump();
        }
        let span = self.span_from(start);
        let ident = |path: Vec<crate::ast::expr::HierPathSegment>, span: crate::ast::Span| {
            Expression::new(
                ExprKind::Ident(crate::ast::expr::HierarchicalIdentifier {
                    root: None,
                    path,
                    span,
                    cached_signal_id: crate::ast::cache::SignalCache::new(None),
                    cached_resolved_name: crate::ast::cache::NameCache::new(),
                    bound: crate::ast::binding::Bound::UNSET,
                }),
                span,
            )
        };
        let e = if call {
            let method = path.pop().expect("a path of two segments or more").name;
            let receiver_span = crate::ast::Span {
                start,
                end: method.span.start.saturating_sub(1).max(start),
            };
            let func = Expression::new(
                ExprKind::MemberAccess {
                    expr: Box::new(ident(path, receiver_span)),
                    member: method,
                },
                span,
            );
            Expression::new(
                ExprKind::Call {
                    func: Box::new(func),
                    args: Vec::new(),
                },
                span,
            )
        } else {
            ident(path, span)
        };
        (root, e)
    }

    /// Decide whether the `{` at the cursor opens a constraint block or a
    /// concatenation expression (§11.4.12 / §18.5.2).
    ///
    /// Both readings start with a bare `LBrace`, and the grammar itself has
    /// no fixed position for the choice, so it is settled by the token after
    /// the matching `}`: an expression continues (an operator, `inside` /
    /// `dist`, a select) or ends the item with `;`, while a block ends at
    /// whatever terminates the enclosing item.
    fn constraint_lbrace_is_block(&self) -> bool {
        let mut depth = 0usize;
        let mut i = self.pos;
        while let Some(tok) = self.tokens.get(i) {
            match tok.kind {
                TokenKind::LBrace | TokenKind::ApostropheLBrace => depth += 1,
                TokenKind::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return !matches!(
                            self.tokens.get(i + 1).map(|t| t.kind),
                            Some(
                                TokenKind::Semicolon
                                    | TokenKind::KwInside
                                    | TokenKind::KwDist
                                    | TokenKind::LBracket
                                    | TokenKind::Dot
                                    | TokenKind::Increment
                                    | TokenKind::Decrement
                                    | TokenKind::Plus
                                    | TokenKind::Minus
                                    | TokenKind::Star
                                    | TokenKind::Slash
                                    | TokenKind::Percent
                                    | TokenKind::DoubleStar
                                    | TokenKind::Eq
                                    | TokenKind::Neq
                                    | TokenKind::CaseEq
                                    | TokenKind::CaseNeq
                                    | TokenKind::WildcardEq
                                    | TokenKind::WildcardNeq
                                    | TokenKind::Lt
                                    | TokenKind::Gt
                                    | TokenKind::Leq
                                    | TokenKind::Geq
                                    | TokenKind::ShiftLeft
                                    | TokenKind::ShiftRight
                                    | TokenKind::ArithShiftLeft
                                    | TokenKind::ArithShiftRight
                                    | TokenKind::LogAnd
                                    | TokenKind::LogOr
                                    | TokenKind::LogImplies
                                    | TokenKind::LogEquiv
                                    | TokenKind::BitAnd
                                    | TokenKind::BitOr
                                    | TokenKind::BitXor
                                    | TokenKind::BitNand
                                    | TokenKind::BitNor
                                    | TokenKind::BitXnor
                                    | TokenKind::Arrow
                                    | TokenKind::Question
                            )
                        );
                    }
                }
                TokenKind::Eof => break,
                _ => {}
            }
            i += 1;
        }
        // Unterminated: let the expression parser report the stray `{`.
        false
    }

    pub(crate) fn parse_constraint_item(&mut self, pos: ConstraintPos) -> ConstraintItem {
        let start = self.current_span().start;
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
                let then_item = self.parse_constraint_item(ConstraintPos::ConstraintSet);
                let else_item = if self.at(TokenKind::KwElse) {
                    self.bump();
                    Some(Box::new(
                        self.parse_constraint_item(ConstraintPos::ConstraintSet),
                    ))
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
                let item = self.parse_constraint_item(ConstraintPos::ConstraintSet);
                ConstraintItem::Foreach {
                    array: array_expr,
                    vars,
                    item: Box::new(item),
                    span: self.span_from(start),
                }
            }
            TokenKind::KwSoft => {
                self.bump();
                // `[ soft ] expression_or_dist ;` — only the first
                // `constraint_expression` alternative takes `soft`, and that
                // one is an expression, never a brace block.
                ConstraintItem::Soft(Box::new(
                    self.parse_constraint_item(ConstraintPos::BlockItem),
                ))
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
            // A bare `{` is only ambiguous where the grammar allows a
            // `constraint_set` (`if`/`else`/`foreach`/`->`). Inside a
            // `constraint_block` a bare block is not a block item at all, so
            // the `{` can only start an expression (a concatenation), which
            // the `_` arm below parses with no lookahead.
            //
            // In `constraint_set` position both readings are legal:
            //   if (c) { a == 1; }           -- a nested set
            //   if (c) {a,b} inside {1,2};   -- a concatenation expression
            // so tell them apart by what follows the matching `}`.
            TokenKind::LBrace
                if pos == ConstraintPos::ConstraintSet && self.constraint_lbrace_is_block() =>
            {
                self.bump();
                let mut items = Vec::new();
                while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                    items.push(self.parse_constraint_item(ConstraintPos::BlockItem));
                }
                self.expect(TokenKind::RBrace);
                ConstraintItem::Block(items)
            }
            _ => {
                // The paren-primary parser needs to accept `( expr dist {...} )`
                // only in constraint context.
                let saved_in_constraint = self.in_constraint;
                self.in_constraint = true;
                // §18.5.3: a constraint expression is
                // `expression [ -> constraint_set ]`. `->` is the constraint
                // separator, not `LogImplies`, so the left side stops at it.
                let expr = self.parse_constraint_left_expr();
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
                    let constraint = self.parse_constraint_item(ConstraintPos::ConstraintSet);
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
    pub(in crate::parse) fn parse_dist_body(
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

    pub(super) fn parse_constraint_range(&mut self) -> ConstraintRange {
        // §18.5.3, §19.5.1: a distribution item and a covergroup bin take a
        // `value_range`, which includes the tolerance forms (§11.4.13).
        if self.at(TokenKind::LBracket) && crate::is_sv2023() && self.range_has_tolerance() {
            let (lo, hi) = self.parse_value_range_bounds(self.current_span().start);
            return ConstraintRange::Range { lo, hi };
        }
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
