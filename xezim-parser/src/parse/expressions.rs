//! Expression parsing (IEEE 1800-2017 §A.8) with Pratt precedence climbing.

use super::Parser;
use crate::ast::expr::*;
use crate::ast::Span;
use crate::ast::Identifier;
use crate::lexer::token::TokenKind;
use crate::diagnostics::Diagnostic;
use std::cell::Cell;

impl Parser {
    pub(super) fn parse_expression(&mut self) -> Expression {
        self.parse_expr_bp(0)
    }

    /// Parse an expression that could be an lvalue in a statement context.
    /// Parses only up to identifier/select/concat without consuming `<=` or `=`.
    /// Falls back to full expression if the result doesn't look like an lvalue.
    pub(super) fn parse_lvalue_or_expr(&mut self) -> Expression {
        let save_pos = self.pos;
        // Parse primary + all postfix selects (bit/part/index selects, member access)
        let mut lval = self.parse_prefix();

        // Parse postfix selects: [idx], [l:r], [idx+:w], [idx-:w], .member
        loop {
            if self.at(TokenKind::LBracket) {
                let s = self.current().span.start;
                self.bump();
                let idx = self.parse_expression();
                if self.eat(TokenKind::Colon).is_some() {
                    let right = self.parse_expression();
                    self.expect(TokenKind::RBracket);
                    lval = Expression::new(ExprKind::RangeSelect {
                        expr: Box::new(lval), kind: RangeKind::Constant,
                        left: Box::new(idx), right: Box::new(right),
                    }, self.span_from(s));
                } else if self.eat(TokenKind::PlusColon).is_some() {
                    let width = self.parse_expression();
                    self.expect(TokenKind::RBracket);
                    lval = Expression::new(ExprKind::RangeSelect {
                        expr: Box::new(lval), kind: RangeKind::IndexedUp,
                        left: Box::new(idx), right: Box::new(width),
                    }, self.span_from(s));
                } else if self.eat(TokenKind::MinusColon).is_some() {
                    let width = self.parse_expression();
                    self.expect(TokenKind::RBracket);
                    lval = Expression::new(ExprKind::RangeSelect {
                        expr: Box::new(lval), kind: RangeKind::IndexedDown,
                        left: Box::new(idx), right: Box::new(width),
                    }, self.span_from(s));
                } else {
                    self.expect(TokenKind::RBracket);
                    lval = Expression::new(ExprKind::Index {
                        expr: Box::new(lval), index: Box::new(idx),
                    }, self.span_from(s));
                }
            } else if self.at(TokenKind::Dot) {
                let s = self.current().span.start;
                self.bump();
                let member = if matches!(self.current().kind,
                    TokenKind::KwNew | TokenKind::KwAnd | TokenKind::KwOr | TokenKind::KwXor
                    | TokenKind::KwUnique
                ) {
                    let tok = self.bump();
                    Identifier { name: tok.text.clone(), span: Span { start: tok.span.start, end: tok.span.end } }
                } else {
                    self.parse_identifier()
                };
                lval = Expression::new(ExprKind::MemberAccess {
                    expr: Box::new(lval), member,
                }, self.span_from(s));
            } else if self.at(TokenKind::DoubleColon) {
                let s = self.current().span.start;
                self.bump();
                let member = if self.at(TokenKind::KwNew) {
                    let tok = self.bump();
                    crate::ast::Identifier { name: "new".to_string(), span: tok.span }
                } else {
                    self.parse_identifier()
                };
                lval = Expression::new(ExprKind::MemberAccess {
                    expr: Box::new(lval), member,
                }, self.span_from(s));
            } else {
                break;
            }
        }

        // If followed by `<=` or `=` or compound assign, this is likely an lvalue
        if self.at(TokenKind::Leq) || self.at(TokenKind::Assign) || self.at_any(&[
            TokenKind::PlusAssign, TokenKind::MinusAssign,
            TokenKind::StarAssign, TokenKind::SlashAssign,
            TokenKind::PercentAssign, TokenKind::AndAssign,
            TokenKind::OrAssign, TokenKind::XorAssign,
            TokenKind::ShiftLeftAssign, TokenKind::ShiftRightAssign,
        ]) {
            return lval;
        }

        // Otherwise, the prefix alone wasn't enough; rewind and parse as a full expression
        self.pos = save_pos;
        self.parse_expr_bp(0)
    }

    /// Pratt parser: parse expression with minimum binding power.
    /// §12.6 pattern (used by `matches` / `case … matches`). Parse-accept only
    /// — consumes the pattern structure; bindings/semantics aren't modelled.
    ///   pattern ::= `.` ident | `.*` | `tagged` ident [pattern]
    ///             | `'{` pattern {, [name:] pattern} `}` | expression
    /// §12.6 pattern. Returns the parsed structure so `case … matches` can
    /// actually test it at run time (it used to be consumed and discarded,
    /// which left every pattern item unmatchable).
    pub(super) fn parse_pattern(&mut self) -> crate::ast::stmt::Pattern {
        use crate::ast::stmt::Pattern;
        if self.eat(TokenKind::KwTagged).is_some() {
            let tag = self.parse_identifier();
            // Optional member sub-pattern.
            let inner = if matches!(self.current_kind(),
                TokenKind::ApostropheLBrace | TokenKind::KwTagged | TokenKind::Dot) {
                Some(Box::new(self.parse_pattern()))
            } else {
                None
            };
            Pattern::Tagged { tag, inner }
        } else if self.eat(TokenKind::Dot).is_some() {
            // `.field` binding or `.*` wildcard. `.name` introduces a pattern
            // variable (§12.6) visible in the matched statement — record it so
            // the enclosing if/case can declare it.
            if self.eat(TokenKind::Star).is_some() {
                Pattern::Wildcard
            } else {
                let id = self.parse_identifier();
                self.pending_pattern_bindings.push(id.clone());
                Pattern::Binding(id)
            }
        } else if self.eat(TokenKind::ApostropheLBrace).is_some() {
            let mut members = Vec::new();
            loop {
                if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }
                // optional `name:` member tag
                let name = if (self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier))
                    && self.peek_kind() == TokenKind::Colon {
                    let id = self.parse_identifier();
                    self.bump(); // :
                    Some(id)
                } else {
                    None
                };
                members.push((name, self.parse_pattern()));
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            self.expect(TokenKind::RBrace);
            Pattern::Struct(members)
        } else {
            // Constant-expression pattern.
            Pattern::Expr(self.parse_expr_bp(16))
        }
    }

    pub(super) fn parse_expr_bp(&mut self, min_bp: u8) -> Expression {
        let start = self.current().span.start;
        let mut lhs = self.parse_prefix();

        loop {
            // §12.6: `expr matches pattern` — a boolean conditional-pattern
            // match. Binding power 15 (like relational). Parse-accept: consume
            // the pattern and yield a placeholder boolean (the match semantics
            // are not modelled).
            if self.at(TokenKind::KwMatches) {
                if 15 < min_bp { break; }
                self.bump();
                let pattern = self.parse_pattern();
                lhs = Expression::new(
                    ExprKind::Matches {
                        expr: Box::new(lhs),
                        pattern: Box::new(pattern),
                    },
                    self.span_from(start),
                );
                continue;
            }
            // inside operator: expr inside { range_list }
            // Binding power 15 (same as relational)
            if self.at(TokenKind::KwInside) {
                if 15 < min_bp { break; }
                self.bump();
                self.expect(TokenKind::LBrace);
                let mut ranges = Vec::new();
                loop {
                    if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }
                    // Handle [lo:hi] ranges
                    if self.at(TokenKind::LBracket) {
                        self.bump();
                        // Parse the lower/centre expression with a binding
                        // power that excludes `+`/`-`/`%`, so `+/-` and `+%-`
                        // tokens stay available for tolerance detection.
                        // Simple operands or parenthesised expressions
                        // remain supported.
                        let center = if crate::is_sv2023() {
                            let mut center = self.parse_expr_bp(21);
                            // A bare `+`/`-` here (not the start of a
                            // `+/-`/`+%-` tolerance marker) means the
                            // lower/centre bound is itself an additive
                            // expression, e.g. `[A+B:C]` — fold it into
                            // `center` instead of leaving it for the
                            // tolerance check below to misparse.
                            loop {
                                let is_tol_abs = self.at(TokenKind::Plus)
                                    && self.peek_kind() == TokenKind::Slash
                                    && self.peek_kind_n(2) == TokenKind::Minus;
                                let is_tol_pct = self.at(TokenKind::Plus)
                                    && self.peek_kind() == TokenKind::Percent
                                    && self.peek_kind_n(2) == TokenKind::Minus;
                                if is_tol_abs || is_tol_pct {
                                    break;
                                }
                                let op = if self.at(TokenKind::Plus) {
                                    BinaryOp::Add
                                } else if self.at(TokenKind::Minus) {
                                    BinaryOp::Sub
                                } else {
                                    break;
                                };
                                self.bump();
                                let rhs = self.parse_expr_bp(20);
                                center = Expression::new(ExprKind::Binary {
                                    op,
                                    left: Box::new(center),
                                    right: Box::new(rhs),
                                }, self.span_from(start));
                            }
                            center
                        } else {
                            self.parse_expression()
                        };
                        // IEEE 1800-2023 §11.4.13: tolerance ranges
                        // `[A +/- B]` → `[A-B : A+B]`
                        // `[A +%- B]` → `[A*(100-B)/100 : A*(100+B)/100]`
                        // `+/-` and `+%-` lex as three separate tokens
                        // (Plus, Slash|Percent, Minus); we detect the triple.
                        let is_tol_abs = crate::is_sv2023()
                            && self.at(TokenKind::Plus)
                            && self.peek_kind() == TokenKind::Slash
                            && self.peek_kind_n(2) == TokenKind::Minus;
                        let is_tol_pct = crate::is_sv2023()
                            && self.at(TokenKind::Plus)
                            && self.peek_kind() == TokenKind::Percent
                            && self.peek_kind_n(2) == TokenKind::Minus;
                        if is_tol_abs || is_tol_pct {
                            self.bump(); self.bump(); self.bump();
                            let delta = self.parse_expression();
                            self.expect(TokenKind::RBracket);
                            let (lo, hi) = if is_tol_abs {
                                let lo = Expression::new(ExprKind::Binary {
                                    op: BinaryOp::Sub,
                                    left: Box::new(center.clone()),
                                    right: Box::new(delta.clone()),
                                }, self.span_from(start));
                                let hi = Expression::new(ExprKind::Binary {
                                    op: BinaryOp::Add,
                                    left: Box::new(center),
                                    right: Box::new(delta),
                                }, self.span_from(start));
                                (lo, hi)
                            } else {
                                let hundred = || Expression::new(
                                    ExprKind::Number(NumberLiteral::Integer {
                                        signed: false,
                                        size: None,
                                        base: NumberBase::Decimal,
                                        value: "100".into(),
                                        cached_val: Cell::new(None),
                                    }),
                                    self.span_from(start),
                                );
                                let make = |sign_neg: bool, c: Expression, d: Expression| {
                                    let op = if sign_neg { BinaryOp::Sub } else { BinaryOp::Add };
                                    let pm = Expression::new(ExprKind::Binary {
                                        op,
                                        left: Box::new(hundred()),
                                        right: Box::new(d),
                                    }, c.span);
                                    let mul = Expression::new(ExprKind::Binary {
                                        op: BinaryOp::Mul,
                                        left: Box::new(c),
                                        right: Box::new(pm),
                                    }, self.span_from(start));
                                    Expression::new(ExprKind::Binary {
                                        op: BinaryOp::Div,
                                        left: Box::new(mul),
                                        right: Box::new(hundred()),
                                    }, self.span_from(start))
                                };
                                (make(true, center.clone(), delta.clone()),
                                 make(false, center, delta))
                            };
                            ranges.push(Expression::new(ExprKind::Range(Box::new(lo), Box::new(hi)), self.span_from(start)));
                        } else {
                            self.expect(TokenKind::Colon);
                            let hi = self.parse_expression();
                            self.expect(TokenKind::RBracket);
                            ranges.push(Expression::new(ExprKind::Range(Box::new(center), Box::new(hi)), self.span_from(start)));
                        }
                    } else {
                        ranges.push(self.parse_expression());
                    }
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::RBrace);
                lhs = Expression::new(ExprKind::Inside { expr: Box::new(lhs), ranges }, self.span_from(start));
                continue;
            }

            // Check for postfix: ++ --
            if self.at(TokenKind::Increment) || self.at(TokenKind::Decrement) {
                let op = if self.at(TokenKind::Increment) { UnaryOp::PostIncr } else { UnaryOp::PostDecr };
                let (l_bp, _) = postfix_bp();
                if l_bp < min_bp { break; }
                self.bump();
                lhs = Expression::new(ExprKind::Unary { op, operand: Box::new(lhs) }, self.span_from(start));
                continue;
            }

            // Binary/ternary operators
            if let Some((op, l_bp, r_bp)) = self.infix_bp() {
                if l_bp < min_bp { break; }
                self.bump();

                // Ternary operator
                if op == BinaryOp::Add && self.at(TokenKind::Colon) {
                    // This shouldn't happen here; ternary handled below
                }

                // LRM §16.8: infix `a ##N b` — the cycle count `N`
                // sits between the `##` token and the right operand.
                // Parse the count, the operand, and synthesise
                // `Binary{HashHash, a, Binary{HashHash, N, b}}` so the
                // SVA executor sees `a` then an N-cycle-delayed `b`.
                // `a ##[m:n] b` range form is collapsed to the lower
                // bound for now.
                if op == BinaryOp::HashHash {
                    // Optional `[m:n]` / `[*]` / `[+]` range form: skip
                    // to the closing bracket and use the first number.
                    let count_expr = if self.at(TokenKind::LBracket) {
                        self.bump();
                        let lo = if self.at(TokenKind::IntegerLiteral) {
                            self.parse_prefix()
                        } else {
                            // `[*]`/`[+]` — default to 1 cycle.
                            Expression::new(ExprKind::Number(
                                crate::ast::expr::NumberLiteral::Integer {
                                    size: None, signed: false,
                                    base: crate::ast::expr::NumberBase::Decimal,
                                    value: "1".to_string(),
                                    cached_val: std::cell::Cell::new(None),
                                }), self.span_from(start))
                        };
                        while !self.at(TokenKind::RBracket) && !self.at(TokenKind::Eof) {
                            self.bump();
                        }
                        let _ = self.eat(TokenKind::RBracket);
                        lo
                    } else {
                        // Bare count `##1`.
                        self.parse_prefix()
                    };
                    let rhs = self.parse_expr_bp(r_bp);
                    let delayed = Expression::new(ExprKind::Binary {
                        op: BinaryOp::HashHash,
                        left: Box::new(count_expr),
                        right: Box::new(rhs),
                    }, self.span_from(start));
                    lhs = Expression::new(ExprKind::Binary {
                        op: BinaryOp::SeqAnd,
                        left: Box::new(lhs),
                        right: Box::new(delayed),
                    }, self.span_from(start));
                    continue;
                }

                let rhs = self.parse_expr_bp(r_bp);
                lhs = Expression::new(ExprKind::Binary {
                    op, left: Box::new(lhs), right: Box::new(rhs),
                }, self.span_from(start));
                continue;
            }

            // Ternary: ? :
            if self.at(TokenKind::Question) {
                let (l_bp, _) = ternary_bp();
                if l_bp < min_bp { break; }
                self.bump();
                let then_expr = self.parse_expr_bp(0);
                self.expect(TokenKind::Colon);
                let else_expr = self.parse_expr_bp(l_bp);
                lhs = Expression::new(ExprKind::Conditional {
                    condition: Box::new(lhs),
                    then_expr: Box::new(then_expr),
                    else_expr: Box::new(else_expr),
                }, self.span_from(start));
                continue;
            }

            // Member access: .ident or .new
            if self.at(TokenKind::Dot) {
                self.bump();
                // Allow 'new'/'and'/'or'/'xor'/'unique' as member names (e.g. arr.and, arr.unique)
                let member = if matches!(self.current().kind,
                    TokenKind::KwNew | TokenKind::KwAnd | TokenKind::KwOr | TokenKind::KwXor
                    | TokenKind::KwUnique
                ) {
                    let tok = self.bump();
                    Identifier { name: tok.text.clone(), span: Span { start: tok.span.start, end: tok.span.end } }
                } else {
                    self.parse_identifier()
                };
                // Method call: .method(args)
                if self.at(TokenKind::LParen) {
                    let member_expr = Expression::new(ExprKind::MemberAccess {
                        expr: Box::new(lhs), member,
                    }, self.span_from(start));
                    let args = self.parse_call_args();
                    let mut call_expr = Expression::new(ExprKind::Call {
                        func: Box::new(member_expr), args,
                    }, self.span_from(start));
                    if self.eat(TokenKind::KwWith).is_some() {
                        if self.at(TokenKind::LParen) {
                            self.expect(TokenKind::LParen);
                            let filter = self.parse_expression();
                            self.expect(TokenKind::RParen);
                            call_expr = Expression::new(ExprKind::WithClause {
                                expr: Box::new(call_expr),
                                filter: Box::new(filter),
                            }, self.span_from(start));
                        }
                        // Inline constraint block `with { ... }`
                        // (randomize-with). Parse it into ConstraintItems so
                        // the simulator's `solve_forced` honours each. The
                        // earlier brace-skip dropped these entirely — every
                        // `obj.randomize() with { ... }` was silently
                        // unconstrained.
                        if self.eat(TokenKind::LBrace).is_some() {
                            let mut constraints = Vec::new();
                            while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                                constraints.push(self.parse_constraint_item());
                            }
                            self.expect(TokenKind::RBrace);
                            call_expr = Expression::new(ExprKind::RandomizeWith {
                                call: Box::new(call_expr),
                                constraints,
                            }, self.span_from(start));
                        }
                    }
                    lhs = call_expr;
                } else {
                    lhs = Expression::new(ExprKind::MemberAccess {
                        expr: Box::new(lhs), member,
                    }, self.span_from(start));
                }
                continue;
            }

            // Scope resolution: :: (e.g. pkg::name, class::static_member)
            if self.at(TokenKind::DoubleColon) {
                self.bump();
                // §8.8: `Class::new` typed-constructor reference.
                let member = if self.at(TokenKind::KwNew) {
                    let tok = self.bump();
                    crate::ast::Identifier { name: "new".to_string(), span: tok.span }
                } else {
                    self.parse_identifier()
                };
                // §8.25: parameterized-class specialization in a scoped chain —
                // `pkg::Class#(params)::method` (UVM's
                // `uvm_pkg::uvm_config_db#(virtual if)::get/set`). The bare
                // primary consumes a trailing `#(...)`, but after a `::` it must
                // be consumed here too. Capture the canonical param-list text so
                // a `Specialization` node can key per-specialization statics
                // (PURE_SV_LRM); the simulator treats it as `base` otherwise.
                let mut member_expr = Expression::new(ExprKind::MemberAccess {
                    expr: Box::new(lhs), member,
                }, self.span_from(start));
                if self.at(TokenKind::Hash) && self.peek_kind() == TokenKind::LParen {
                    self.bump(); // #
                    self.bump(); // (
                    let mut depth = 1;
                    let mut text = String::new();
                    while depth > 0 && !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LParen => depth += 1,
                            TokenKind::RParen => depth -= 1,
                            _ => {}
                        }
                        if depth > 0 {
                            if !text.is_empty() { text.push(' '); }
                            text.push_str(&self.current().text);
                        }
                        self.bump();
                    }
                    member_expr = Expression::new(ExprKind::Specialization {
                        base: Box::new(member_expr),
                        type_args_text: text,
                    }, self.span_from(start));
                }
                lhs = member_expr;
                continue;
            }

            // Function call: (args)
            if self.at(TokenKind::LParen) {
                let args = self.parse_call_args();
                let mut call_expr = Expression::new(ExprKind::Call {
                    func: Box::new(lhs), args,
                }, self.span_from(start));
                if self.eat(TokenKind::KwWith).is_some() {
                    if self.at(TokenKind::LParen) {
                        self.expect(TokenKind::LParen);
                        let filter = self.parse_expression();
                        self.expect(TokenKind::RParen);
                        call_expr = Expression::new(ExprKind::WithClause {
                            expr: Box::new(call_expr),
                            filter: Box::new(filter),
                        }, self.span_from(start));
                    }
                    // Inline constraint block `with { ... }` (randomize-with).
                    // Parse it into constraint items so the simulator can honor
                    // it (instruction selection relies on `inside` here).
                    if self.eat(TokenKind::LBrace).is_some() {
                        let mut constraints = Vec::new();
                        while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                            constraints.push(self.parse_constraint_item());
                        }
                        self.expect(TokenKind::RBrace);
                        call_expr = Expression::new(ExprKind::RandomizeWith {
                            call: Box::new(call_expr),
                            constraints,
                        }, self.span_from(start));
                    }
                }
                lhs = call_expr;
                continue;
            }

            // Index/range select: [expr] or [expr:expr] or [expr+:expr] or new[size]
            if self.at(TokenKind::LBracket) {
                self.bump();
                // IEEE 1800-2017 §16.9 SVA sequence repetition immediately
                // after a sequence operand: `[*n:m]` (consecutive), `[=n:m]`
                // (non-consecutive), `[->n:m]` (goto). The leading `*`/`=`/`->`
                // can't begin a normal index expression, so this is
                // unambiguous. Parse-accept: consume to the matching `]` and
                // leave the operand unchanged (repetition count not modelled).
                if self.at(TokenKind::Star) || self.at(TokenKind::Assign) || self.at(TokenKind::Arrow) {
                    let mut depth = 1i32;
                    while depth > 0 && !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LBracket => depth += 1,
                            TokenKind::RBracket => depth -= 1,
                            _ => {}
                        }
                        self.bump();
                    }
                    continue;
                }
                let idx = self.parse_expression();

                // Special case: new[size] for dynamic arrays
                let is_new = if let ExprKind::Ident(ref hier) = lhs.kind {
                    hier.path.len() == 1 && hier.path[0].name.name == "new"
                } else { false };

                if is_new {
                    self.expect(TokenKind::RBracket);
                    lhs = Expression::new(ExprKind::Call {
                        func: Box::new(lhs),
                        args: vec![idx],
                    }, self.span_from(start));
                } else if self.eat(TokenKind::Colon).is_some() {
                    let right = self.parse_expression();
                    self.expect(TokenKind::RBracket);
                    lhs = Expression::new(ExprKind::RangeSelect {
                        expr: Box::new(lhs),
                        kind: RangeKind::Constant,
                        left: Box::new(idx),
                        right: Box::new(right),
                    }, self.span_from(start));
                } else if self.eat(TokenKind::PlusColon).is_some() {
                    let width = self.parse_expression();
                    self.expect(TokenKind::RBracket);
                    lhs = Expression::new(ExprKind::RangeSelect {
                        expr: Box::new(lhs),
                        kind: RangeKind::IndexedUp,
                        left: Box::new(idx),
                        right: Box::new(width),
                    }, self.span_from(start));
                } else if self.eat(TokenKind::MinusColon).is_some() {
                    let width = self.parse_expression();
                    self.expect(TokenKind::RBracket);
                    lhs = Expression::new(ExprKind::RangeSelect {
                        expr: Box::new(lhs),
                        kind: RangeKind::IndexedDown,
                        left: Box::new(idx),
                        right: Box::new(width),
                    }, self.span_from(start));
                } else {
                    self.expect(TokenKind::RBracket);
                    lhs = Expression::new(ExprKind::Index {
                        expr: Box::new(lhs),
                        index: Box::new(idx),
                    }, self.span_from(start));
                }
                continue;
            }

            // with clause: `expr with ( filter_expr )` (array methods), or the
            // §11.4.14 stream-expression form `expr with [ array_range ]`
            // (`<<8{ data with [0 +: len] }`). The bracketed range selects a
            // slice of the operand inside a streaming concatenation.
            if self.at(TokenKind::KwWith) && self.peek_kind() == TokenKind::LBracket {
                self.bump(); // with
                self.bump(); // [
                let _lo = self.parse_expression();
                // optional `: hi` / `+: width` / `-: width`
                if self.at(TokenKind::Colon) || self.at(TokenKind::PlusColon)
                    || self.at(TokenKind::MinusColon) {
                    self.bump();
                    let _hi = self.parse_expression();
                }
                self.expect(TokenKind::RBracket);
                // Pass the operand through unchanged — the range is a slice hint.
                lhs = Expression::new(ExprKind::Paren(Box::new(lhs)), self.span_from(start));
                continue;
            }
            if self.eat(TokenKind::KwWith).is_some() {
                self.expect(TokenKind::LParen);
                let filter = self.parse_expression();
                self.expect(TokenKind::RParen);
                lhs = Expression::new(ExprKind::WithClause {
                    expr: Box::new(lhs),
                    filter: Box::new(filter),
                }, self.span_from(start));
                continue;
            }

            // Sized / type cast postfix: <expr>'(value)
            // Covers (expr)'(value), pkg::type'(value), id'(value), array_select'(value), etc.
            // Treated as pass-through (cast is a width/type hint at parse time).
            if self.current().text == "'" && self.peek_kind() == TokenKind::LParen {
                self.bump(); // skip '
                self.bump(); // skip (
                let inner = self.parse_expression();
                self.expect(TokenKind::RParen);
                // §6.24.1: a LITERAL casting size (`4'(x)`) resizes the
                // operand — lower it to an internal resize call so the width
                // survives (it was dropped, so `4'(8'hAB)` kept all 8 bits).
                // Non-literal casting types (pkg::type'(v), id'(v)) stay a
                // pass-through width/type hint as before.
                if matches!(lhs.kind, ExprKind::Number(_)) {
                    lhs = Expression::new(ExprKind::SystemCall {
                        name: "$__xz_size_cast".to_string(),
                        args: vec![lhs, inner],
                    }, self.span_from(start));
                } else if matches!(lhs.kind, ExprKind::TypeLiteral(_)) {
                    // §6.24.1 TYPE cast `int'(2.7)` / `real'(3)` — it CONVERTS
                    // (a real to int rounds; an int to real widens). It used
                    // to be a pass-through, so the operand kept its own type
                    // and only an assignment to a typed target coerced it.
                    lhs = Expression::new(ExprKind::SystemCall {
                        name: "$__xz_type_cast".to_string(),
                        args: vec![lhs, inner],
                    }, self.span_from(start));
                } else if matches!(&lhs.kind, ExprKind::Ident(h)
                    if h.path.len() == 1 && h.path[0].selects.is_empty())
                {
                    // §6.24.1: `id'(v)` where `id` is a bare identifier is either
                    // a TYPE cast (id is a typedef) or a SIZE cast (id is a
                    // constant/parameter). The two are indistinguishable without
                    // the type/parameter tables, so defer to the simulator via a
                    // named-cast intrinsic that carries the identifier. Formerly
                    // this dropped the cast entirely (`size1'(x)` kept x's width,
                    // `my_t'(x)` skipped the conversion).
                    lhs = Expression::new(ExprKind::SystemCall {
                        name: "$__xz_named_cast".to_string(),
                        args: vec![lhs, inner],
                    }, self.span_from(start));
                } else {
                    lhs = Expression::new(ExprKind::Paren(Box::new(inner)), self.span_from(start));
                }
                continue;
            }

            break;
        }

        lhs
    }

    /// The `DataType` a cast keyword denotes (`int'(x)`, `byte'(x)`, …).
    fn cast_keyword_type(kw: TokenKind, span: crate::ast::Span) -> crate::ast::types::DataType {
        use crate::ast::types::{DataType, IntegerAtomType, IntegerVectorType, RealType, SimpleType};
        let atom = |k| DataType::IntegerAtom { kind: k, signing: None, span };
        let vec_ = |k| DataType::IntegerVector { kind: k, signing: None, dimensions: Vec::new(), span };
        match kw {
            TokenKind::KwInt => atom(IntegerAtomType::Int),
            TokenKind::KwByte => atom(IntegerAtomType::Byte),
            TokenKind::KwShortint => atom(IntegerAtomType::ShortInt),
            TokenKind::KwLongint => atom(IntegerAtomType::LongInt),
            TokenKind::KwInteger => atom(IntegerAtomType::Integer),
            TokenKind::KwReal | TokenKind::KwRealtime => {
                DataType::Real { kind: RealType::Real, span }
            }
            TokenKind::KwShortreal => DataType::Real { kind: RealType::ShortReal, span },
            TokenKind::KwString => DataType::Simple { kind: SimpleType::String, span },
            TokenKind::KwBit => vec_(IntegerVectorType::Bit),
            TokenKind::KwReg => vec_(IntegerVectorType::Reg),
            _ => vec_(IntegerVectorType::Logic),
        }
    }

    /// Parse prefix / primary expression.
    pub(super) fn parse_prefix(&mut self) -> Expression {
        let start = self.current().span.start;

        match self.current_kind() {
            // §16.13 multiclock sequence: a clocking-event prefix `@(event)` on
            // a (sub-)sequence operand — `… ##1 @(posedge clk1) out1`. Only in
            // an SVA sequence/property body; consume the event and continue with
            // the operand (the clock retiming is parse-accepted, not modelled).
            // §16.9.3 sampled-value function clocking argument:
            // `$rose(x, @(posedge clk))` — parse `@(edge sig)` into the
            // internal marker call `$__xz_clocking_arg(edge_code, sig)`
            // (0 = any change, 1 = posedge, 2 = negedge) so the simulator
            // can key its sampled history on the explicit clock.
            TokenKind::At if !self.in_sva_seq => {
                self.bump(); // @
                let mut edge_code: u64 = 0;
                let mut clk = Expression::new(ExprKind::Null, self.span_from(start));
                if self.eat(TokenKind::LParen).is_some() {
                    match self.current_kind() {
                        TokenKind::KwPosedge => { edge_code = 1; self.bump(); }
                        TokenKind::KwNegedge => { edge_code = 2; self.bump(); }
                        TokenKind::KwEdge => { self.bump(); }
                        _ => {}
                    }
                    clk = self.parse_expression();
                    self.expect(TokenKind::RParen);
                }
                let span = self.span_from(start);
                let edge_lit = Expression::new(
                    ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
                        size: None,
                        signed: false,
                        base: crate::ast::expr::NumberBase::Decimal,
                        value: edge_code.to_string(),
                        cached_val: std::cell::Cell::new(None),
                    }),
                    span,
                );
                return Expression::new(
                    ExprKind::SystemCall {
                        name: "$__xz_clocking_arg".to_string(),
                        args: vec![edge_lit, clk],
                    },
                    span,
                );
            }
            TokenKind::At if self.in_sva_seq => {
                self.bump(); // @
                if self.at(TokenKind::LParen) {
                    self.bump();
                    let mut depth = 1;
                    while depth > 0 && !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LParen => depth += 1,
                            TokenKind::RParen => depth -= 1,
                            _ => {}
                        }
                        self.bump();
                    }
                }
                self.parse_expr_bp(0)
            }
            // Unary operators
            TokenKind::Plus => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::Plus, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::Minus => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::Minus, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::LogNot => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::LogNot, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::BitNot => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::BitNot, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::BitAnd => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::BitAnd, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::BitOr => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::BitOr, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::BitXor => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::BitXor, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::BitNand => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::BitNand, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::BitNor => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::BitNor, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::BitXnor => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::BitXnor, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::Increment => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::PreIncr, operand: Box::new(e) }, self.span_from(start)) }
            TokenKind::Decrement => { self.bump(); let e = self.parse_expr_bp(prefix_bp()); Expression::new(ExprKind::Unary { op: UnaryOp::PreDecr, operand: Box::new(e) }, self.span_from(start)) }

            // Parenthesized expression or mintypmax — also handles
            // assignment-as-expression like `(a = b)` or `(a += 1)`.
            TokenKind::LParen => {
                self.bump();
                let inner = self.parse_expression();
                // §18.5.4 tolerated nonstandard form `( expr dist { ... } )`
                // inside a constraint (a reference simulator warns and
                // accepts). Capture the body for `parse_constraint_item`;
                // outside constraint context `dist` here stays an error.
                if self.in_constraint && self.at(TokenKind::KwDist) {
                    let dspan = self.current().span;
                    self.diagnostics.push(crate::diagnostics::Diagnostic::warning(
                        "parenthesized 'dist' constraint is nonstandard (accepted for \
                         compatibility)",
                        dspan,
                    ));
                    self.bump();
                    let body = self.parse_dist_body();
                    self.pending_paren_dist.push(body);
                    self.expect(TokenKind::RParen);
                    return inner;
                }
                let inner = if self.at_any(&[
                    TokenKind::Assign, TokenKind::PlusAssign, TokenKind::MinusAssign,
                    TokenKind::StarAssign, TokenKind::SlashAssign, TokenKind::PercentAssign,
                    TokenKind::AndAssign, TokenKind::OrAssign, TokenKind::XorAssign,
                    TokenKind::ShiftLeftAssign, TokenKind::ShiftRightAssign,
                    TokenKind::ArithShiftLeftAssign, TokenKind::ArithShiftRightAssign,
                ]) {
                    let op_kind = self.current().kind.clone();
                    self.bump();
                    let rhs = self.parse_expression();
                    let span = self.span_from(start);
                    let rvalue = match op_kind {
                        TokenKind::PlusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Add, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::MinusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Sub, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::StarAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mul, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::SlashAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Div, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::PercentAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mod, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::AndAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitAnd, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::OrAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitOr, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::XorAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitXor, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftLeft, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftRight, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ArithShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftLeft, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ArithShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftRight, left: Box::new(inner.clone()), right: Box::new(rhs) }, span),
                        _ => rhs,
                    };
                    Expression::new(ExprKind::AssignExpr { lvalue: Box::new(inner), rvalue: Box::new(rvalue) }, span)
                } else {
                    inner
                };
                self.expect(TokenKind::RParen);
                Expression::new(ExprKind::Paren(Box::new(inner)), self.span_from(start))
            }

            // IEEE 1800-2017 §6.23: the type operator `type(<type_or_expr>)` as
            // an expression — used in type comparisons (`type(T) == type(U)`)
            // and `case (type(T)) … type(logic[11:0]) : …`. Parse-accept: we
            // consume `type` + the balanced parenthesised operand and yield a
            // placeholder constant (type identity isn't modelled at runtime, so
            // comparisons fold to a constant — enough to elaborate).
            TokenKind::KwType if self.peek_kind() == TokenKind::LParen => {
                self.bump(); // type
                self.expect(TokenKind::LParen);
                let mut depth = 1i32;
                while depth > 0 && !self.at(TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::LParen => depth += 1,
                        TokenKind::RParen => depth -= 1,
                        _ => {}
                    }
                    if depth == 0 { break; }
                    self.bump();
                }
                self.expect(TokenKind::RParen);
                Expression::new(
                    ExprKind::Number(NumberLiteral::Integer {
                        size: Some(1), signed: false, base: NumberBase::Binary,
                        value: "0".to_string(),
                        cached_val: std::cell::Cell::new(Some((0u64, 0u64, 1u32))),
                    }),
                    self.span_from(start),
                )
            }

            // Concatenation / replication: { ... }
            TokenKind::LBrace => self.parse_concatenation(),

            // Tagged union member expression: `tagged Name`, `tagged Name(expr)`,
            // or — IEEE 1800-2023 §7.3.1 — the pattern literal
            // `tagged Name '{ ... }`. The inner of the last form is the
            // assignment pattern `'{ ... }` parsed by the shared item loop.
            TokenKind::KwTagged => {
                self.bump();
                let tag = if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
                    self.parse_identifier()
                } else {
                    // Synthesize an empty tag
                    crate::ast::Identifier { name: String::new(), span: self.span_from(start) }
                };
                let inner = if self.eat(TokenKind::LParen).is_some() {
                    let e = self.parse_expression();
                    self.expect(TokenKind::RParen);
                    Some(Box::new(e))
                } else if self.eat(TokenKind::ApostropheLBrace).is_some() {
                    let items = self.parse_assignment_pattern_items();
                    self.expect(TokenKind::RBrace);
                    Some(Box::new(Expression::new(
                        ExprKind::AssignmentPattern(items),
                        self.span_from(start),
                    )))
                } else {
                    None
                };
                Expression::new(ExprKind::Tagged { tag, inner }, self.span_from(start))
            }

            // Assignment pattern: '{ ... }
            TokenKind::ApostropheLBrace => {
                self.bump();
                let items = self.parse_assignment_pattern_items();
                self.expect(TokenKind::RBrace);
                Expression::new(ExprKind::AssignmentPattern(items), self.span_from(start))
            }

            // Number literals
            TokenKind::IntegerLiteral | TokenKind::RealLiteral | TokenKind::TimeLiteral => {
                // IEEE 1800-2017 §5.7: reject malformed literals that would
                // otherwise be silently coerced to a wrong value (zero-size
                // based literal, decimal with multiple/mixed x·z). The span of
                // the current (pre-bump) token points at the literal itself.
                if let Some(msg) = validate_number_literal(&self.current().text) {
                    self.error(msg);
                }
                let tok = self.bump();
                let num = parse_number_literal(&tok.text);
                // IEEE 1800-2017 §5.7.1: reject based literals whose value is
                // empty or contains digits outside the base alphabet (e.g. the
                // illegal `8'd-6`, tokenised as `8'd` `-` `6`).
                if tok.text.contains('\'') {
                    if let NumberLiteral::Integer { base, value, .. } = &num {
                        if let Some(msg) = validate_based_literal_value(*base, value) {
                            self.diagnostics.push(Diagnostic::error(
                                format!("{}: '{}'", msg, tok.text),
                                tok.span,
                            ));
                        }
                    }
                }
                let expr = Expression::new(ExprKind::Number(num), self.span_from(start));
                if self.current().kind == TokenKind::IntegerLiteral
                    && self.current().text == "'"
                    && self.peek_kind() == TokenKind::LParen
                {
                    self.bump();
                    self.expect(TokenKind::LParen);
                    let inner = self.parse_expression();
                    self.expect(TokenKind::RParen);
                    // §6.24.1: a literal casting size RESIZES the operand —
                    // lowered to an internal resize call (the width was
                    // dropped before, so `4'(8'hAB)` kept all 8 bits).
                    Expression::new(ExprKind::SystemCall {
                        name: "$__xz_size_cast".to_string(),
                        args: vec![expr, inner],
                    }, self.span_from(start))
                } else {
                    expr
                }
            }
            TokenKind::UnbasedUnsizedLiteral => {
                let tok = self.bump();
                let ch = tok.text.chars().last().unwrap_or('0');
                Expression::new(ExprKind::Number(NumberLiteral::UnbasedUnsized(ch)), self.span_from(start))
            }

            // String literal
            TokenKind::StringLiteral => {
                let tok = self.bump();
                let (s, diags) = decode_string_escapes_checked(&tok.text[1..tok.text.len()-1]);
                self.push_string_escape_diags(diags, tok.span);
                Expression::new(ExprKind::StringLiteral(s), self.span_from(start))
            }

            // IEEE 1800-2023 §5.9: triple-quoted string literal.
            TokenKind::TripleStringLiteral => {
                let tok = self.bump();
                let (s, diags) = decode_string_escapes_checked(&tok.text[3..tok.text.len()-3]);
                self.push_string_escape_diags(diags, tok.span);
                Expression::new(ExprKind::StringLiteral(s), self.span_from(start))
            }

            // IEEE 1800-2023 §3.12.1 / §22.4: `$unit::name` is a QUALIFIED
            // reference to a compilation-unit declaration, not a system call —
            // the parser rejected it outright. A module that declares `name`
            // itself shadows the $unit object, so the qualifier has to survive
            // into the identifier: the compilation-unit copy is injected under
            // the reserved name `$unit::name` wherever it is shadowed (see
            // xezim-core/src/lib.rs), and resolution falls back to the bare
            // name where it is not.
            // A CALL (`$unit::f(...)`) keeps the bare name: $unit subroutines
            // are injected into every module under their own name and are
            // never shadow-renamed, so the qualifier has nothing to select.
            TokenKind::SystemIdentifier
                if self.current().text == "$unit"
                    && self.peek_kind() == TokenKind::DoubleColon =>
            {
                self.bump(); // $unit
                self.bump(); // ::
                let mut hier = self.parse_hierarchical_identifier();
                if !self.at(TokenKind::LParen) {
                    if let Some(seg) = hier.path.first_mut() {
                        seg.name.name = crate::unit_scope_name(&seg.name.name);
                    }
                }
                Expression::new(ExprKind::Ident(hier), self.span_from(start))
            }

            // System call: $display, etc.
            TokenKind::SystemIdentifier => {
                // §23.6: `$root.tb.x` is a HIERARCHICAL reference, not a
                // system call — as a SystemCall it warned "unknown system
                // task" and read/wrote nothing (every `$root.` reference was
                // a silent 32-bit zero). Route it into the hierarchical
                // parser, which accepts `$root` as an ordinary first segment.
                if self.current().text == "$root" && self.peek_kind() == TokenKind::Dot {
                    let hier = self.parse_hierarchical_identifier();
                    return Expression::new(ExprKind::Ident(hier), self.span_from(start));
                }
                let tok = self.bump();
                let name = tok.text.clone();
                let args = if self.at(TokenKind::LParen) {
                    self.parse_call_args()
                } else { Vec::new() };
                Expression::new(ExprKind::SystemCall { name, args }, self.span_from(start))
            }

            // $
            TokenKind::Dollar => {
                self.bump();
                Expression::new(ExprKind::Dollar, self.span_from(start))
            }

            // null
            TokenKind::KwNull => {
                self.bump();
                Expression::new(ExprKind::Null, self.span_from(start))
            }

            // this
            TokenKind::KwThis => {
                self.bump();
                Expression::new(ExprKind::This, self.span_from(start))
            }

            // super — treated as an identifier for super.new(), super.method()
            TokenKind::KwSuper => {
                let tok = self.bump();
                let id = Identifier { name: tok.text.clone(), span: Span { start: tok.span.start, end: tok.span.end } };
                let hier = HierarchicalIdentifier {
                    root: None,
                    path: vec![HierPathSegment { name: id, selects: Vec::new() }],
                    span: self.span_from(start),
                    cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
                };
                Expression::new(ExprKind::Ident(hier), self.span_from(start))
            }

            // §18.7.1 local::name — qualified reference to a variable in the
            // owning class of a constraint block (used inside `with { ... }`
            // to disambiguate from the rand vars of the object being
            // randomized). Treat the same as `name` — name resolution falls
            // back to enclosing class fields, which is the desired effect.
            TokenKind::KwLocal if self.peek_kind() == TokenKind::DoubleColon => {
                self.bump(); // local
                self.bump(); // ::
                let hier = self.parse_hierarchical_identifier();
                Expression::new(ExprKind::Ident(hier), self.span_from(start))
            }

            // Identifier (possibly followed by function call or class scope)
            TokenKind::Identifier | TokenKind::EscapedIdentifier => {
                let id = self.parse_identifier();
                // Optional parameterized type list #(...) for class scope.
                // Capture the canonical param text so a `Specialization` node
                // can key per-specialization statics (PURE_SV_LRM); shape is
                // unchanged for dispatch (the simulator strips it).
                let mut spec_text: Option<String> = None;
                if self.eat(TokenKind::Hash).is_some() {
                    if self.eat(TokenKind::LParen).is_some() {
                        let mut depth = 1;
                        let mut text = String::new();
                        while depth > 0 && !self.at(TokenKind::Eof) {
                            if self.at(TokenKind::LParen) { depth += 1; }
                            else if self.at(TokenKind::RParen) { depth -= 1; }
                            if depth > 0 {
                                if !text.is_empty() { text.push(' '); }
                                text.push_str(&self.current().text);
                            }
                            self.bump();
                        }
                        spec_text = Some(text);
                    }
                }
                let hier = HierarchicalIdentifier {
                    root: None,
                    path: vec![HierPathSegment { name: id, selects: Vec::new() }],
                    span: self.span_from(start),
                    cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
                };
                let mut expr = Expression::new(ExprKind::Ident(hier), self.span_from(start));
                if let Some(text) = spec_text {
                    expr = Expression::new(ExprKind::Specialization {
                        base: Box::new(expr),
                        type_args_text: text,
                    }, self.span_from(start));
                }
                // §6.24.1 cast: identifier'(expr) — `id` is either a typedef
                // (TYPE cast: convert/resize/re-sign the operand) or a constant
                // (SIZE cast: resize to that width). The two are indistinguishable
                // at parse time, so carry the identifier into a named-cast
                // intrinsic that the simulator resolves against its typedef and
                // parameter tables. Formerly this dropped the cast (returned the
                // bare operand), so `size1'(x)` kept x's width and `my_t'(x)`
                // skipped the sign/width conversion.
                if self.current().text == "'" && self.peek_kind() == TokenKind::LParen {
                    self.bump(); // skip '
                    self.bump(); // skip (
                    let inner = self.parse_expression();
                    self.expect(TokenKind::RParen);
                    if matches!(&expr.kind, ExprKind::Ident(h)
                        if h.path.len() == 1 && h.path[0].selects.is_empty())
                    {
                        return Expression::new(ExprKind::SystemCall {
                            name: "$__xz_named_cast".to_string(),
                            args: vec![expr, inner],
                        }, self.span_from(start));
                    }
                    return Expression::new(ExprKind::Paren(Box::new(inner)), self.span_from(start));
                }
                // Check for function call
                if self.at(TokenKind::LParen) {
                    let args = self.parse_call_args();
                    if self.eat(TokenKind::KwWith).is_some() {
                        if self.eat(TokenKind::LBrace).is_some() {
                            let mut depth = 1;
                            while depth > 0 && !self.at(TokenKind::Eof) {
                                if self.at(TokenKind::LBrace) { depth += 1; }
                                else if self.at(TokenKind::RBrace) { depth -= 1; }
                                self.bump();
                            }
                        }
                    }
                    Expression::new(ExprKind::Call {
                        func: Box::new(expr), args,
                    }, self.span_from(start))
                } else {
                    expr
                }
            }

            // Type cast: type'(expr) — e.g., logic'(x), int'(x), bit'(x), void'(x)
            // These are SystemVerilog casting expressions (IEEE 1800-2017 §6.24.1)
            // For simulation, treat as pass-through (the cast is a type/size hint).
            TokenKind::KwLogic | TokenKind::KwBit | TokenKind::KwByte |
            TokenKind::KwInt | TokenKind::KwShortint | TokenKind::KwLongint |
            TokenKind::KwInteger | TokenKind::KwReg | TokenKind::KwSigned | TokenKind::KwUnsigned |
            TokenKind::KwVoid | TokenKind::KwString |
            TokenKind::KwReal | TokenKind::KwShortreal | TokenKind::KwRealtime
                if {
                    // Look ahead: is this type_keyword'(expr) ?
                    let next = self.peek_kind();
                    next == TokenKind::IntegerLiteral && {
                        let next_text = self.tokens.get(self.pos + 1).map(|t| t.text.as_str()).unwrap_or("");
                        next_text == "'"
                    }
                } =>
            {
                let cast_kw = self.current_kind();
                self.bump(); // skip type keyword
                self.bump(); // skip '
                self.expect(TokenKind::LParen);
                let inner = self.parse_expression();
                self.expect(TokenKind::RParen);
                // §6.24.1: `signed'(e)` / `unsigned'(e)` REINTERPRET the operand's
                // signedness — `signed'(4'hF)` is -1. Every other type cast is a
                // width/type hint the assignment context already applies, so it
                // stays a pass-through. Lower the two signedness casts onto the
                // equivalent system functions rather than dropping them.
                match cast_kw {
                    TokenKind::KwSigned => Expression::new(
                        ExprKind::SystemCall { name: "$signed".to_string(), args: vec![inner] },
                        self.span_from(start),
                    ),
                    TokenKind::KwUnsigned => Expression::new(
                        ExprKind::SystemCall { name: "$unsigned".to_string(), args: vec![inner] },
                        self.span_from(start),
                    ),
                    TokenKind::KwVoid => {
                        Expression::new(ExprKind::Paren(Box::new(inner)), self.span_from(start))
                    }
                    // §6.24.1: every other type cast CONVERTS — `int'(2.7)` is 3
                    // (§6.12.2 rounds), `real'(3)` is 3.0, `byte'(x)` truncates.
                    // It used to be a pass-through, so the value kept its own
                    // type unless an assignment context happened to coerce it.
                    kw => {
                        let dt = Self::cast_keyword_type(kw, self.span_from(start));
                        let tl = Expression::new(
                            ExprKind::TypeLiteral(Box::new(dt)),
                            self.span_from(start),
                        );
                        Expression::new(
                            ExprKind::SystemCall {
                                name: "$__xz_type_cast".to_string(),
                                args: vec![tl, inner],
                            },
                            self.span_from(start),
                        )
                    }
                }
            }

            // new expression: new(args) or new[size] or just new
            TokenKind::KwNew => {
                let tok = self.bump();
                let name_id = Identifier { name: tok.text.clone(), span: Span { start: tok.span.start, end: tok.span.end } };
                let hier = HierarchicalIdentifier {
                    root: None,
                    path: vec![HierPathSegment { name: name_id, selects: Vec::new() }],
                    span: self.span_from(start),
                    cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
                };
                let new_expr = Expression::new(ExprKind::Ident(hier), self.span_from(start));
                // `new <expr>` shallow-copy constructor (SV 8.8, Syntax 8-2):
                // `obj = new src;` copies `src` into a fresh object (footnote 23
                // — `<expr>` evaluates to an object handle). This PARENTHESELESS
                // form is distinct from the ordinary constructor call `new(args)`
                // (which the postfix parser handles as a regular `Call`): it is
                // emitted as an explicit `ShallowCopy` node so the simulator can
                // tell a copy from a `new(handle_ctor_arg)` constructor call.
                if matches!(
                    self.current_kind(),
                    TokenKind::Identifier | TokenKind::KwThis | TokenKind::KwSuper
                ) {
                    let src = self.parse_expr_bp(30);
                    Expression::new(
                        ExprKind::ShallowCopy { source: Box::new(src) },
                        self.span_from(start),
                    )
                } else {
                    new_expr
                }
            }

            // Data type keywords used as expressions (e.g. $bits(int),
            // $size(logic [7:0])) — §20.6. The parsed type is RETAINED; the
            // packed range was previously thrown away with the expression.
            k if self.is_data_type_keyword() || k == TokenKind::KwVoid => {
                let dt = self.parse_data_type();
                Expression::new(ExprKind::TypeLiteral(Box::new(dt)), self.span_from(start))
            }

            // LRM §16.12.6 strong temporal operators in property context.
            // Parse as a prefix unary expression: `s_eventually <expr>`,
            // `s_always <expr>`. The SVA executor treats these as
            // future-cycle obligations.
            TokenKind::KwS_eventually => {
                let start = self.current().span.start; self.bump();
                let operand = self.parse_expr_bp(3);
                Expression::new(
                    ExprKind::Unary {
                        op: UnaryOp::SEventually,
                        operand: Box::new(operand),
                    },
                    self.span_from(start),
                )
            }
            TokenKind::KwS_always => {
                let start = self.current().span.start; self.bump();
                let operand = self.parse_expr_bp(3);
                Expression::new(
                    ExprKind::Unary {
                        op: UnaryOp::SAlways,
                        operand: Box::new(operand),
                    },
                    self.span_from(start),
                )
            }
            // LRM §16.12.5 — `nexttime <expr>` and `s_nexttime <expr>`.
            // Desugar to `Binary{HashHash, 1, expr}` which the SVA
            // executor already treats as a 1-cycle delay.
            TokenKind::KwNexttime | TokenKind::KwS_nexttime => {
                let start = self.current().span.start; self.bump();
                let operand = self.parse_expr_bp(3);
                let one = Expression::new(
                    ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
                        size: None,
                        signed: false,
                        base: crate::ast::expr::NumberBase::Decimal,
                        value: "1".to_string(),
                        cached_val: std::cell::Cell::new(None),
                    }),
                    self.span_from(start),
                );
                Expression::new(
                    ExprKind::Binary {
                        op: BinaryOp::HashHash,
                        left: Box::new(one),
                        right: Box::new(operand),
                    },
                    self.span_from(start),
                )
            }
            // LRM §16.12.9 — `not property_expr`: the property holds iff the
            // operand does NOT. For a boolean property (the common assertion
            // form, e.g. `not (a && b)`) this is logical negation, so desugar to
            // `!(expr)`, which the SVA executor evaluates directly. Full
            // temporal-sequence negation is not modeled — the approximate
            // handling matches nexttime/always above. `not` in gate-primitive
            // position is caught at item level (items.rs) before reaching here.
            TokenKind::KwNot => {
                let start = self.current().span.start;
                self.bump();
                let operand = self.parse_expr_bp(3);
                Expression::new(
                    ExprKind::Unary {
                        op: UnaryOp::LogNot,
                        operand: Box::new(operand),
                    },
                    self.span_from(start),
                )
            }
            TokenKind::HashHash => {
                // LRM §16.8: `##N <rest>` — a cycle-delay sequence
                // operator. Parse the cycle count, then the following
                // sub-expression, and synthesize a Binary{HashHash,
                // cycles, rest}. Without consuming the right-hand side
                // here, the bare `##N` would leave the trailing operand
                // dangling (e.g. `a |-> ##1 b` errored on `b`).
                let start = self.current().span.start; self.bump();
                // LRM §16.8: prefix `##N rest` or a cycle-delay RANGE
                // `##[m:n]` / `##[m:$]` / `##[*]` / `##[+]` (e.g. after `|->`:
                // `a |-> ##[1:$] b`). Mirror the infix range handling: collapse
                // the range to its lower bound (the SVA executor is approximate).
                let cycles = if self.at(TokenKind::LBracket) {
                    self.bump();
                    let lo = if self.at(TokenKind::IntegerLiteral) {
                        self.parse_prefix()
                    } else {
                        Expression::new(ExprKind::Number(
                            crate::ast::expr::NumberLiteral::Integer {
                                size: None, signed: false,
                                base: crate::ast::expr::NumberBase::Decimal,
                                value: "1".to_string(),
                                cached_val: std::cell::Cell::new(None),
                            }), self.span_from(start))
                    };
                    while !self.at(TokenKind::RBracket) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
                    let _ = self.eat(TokenKind::RBracket);
                    lo
                } else {
                    self.parse_expr_bp(30)
                };
                // The next token is either another operand (a bare
                // sequence) or end-of-expression. We greedily parse one
                // following sub-expression at low precedence — same as
                // the `|->` body — so chains like `a |-> ##1 b ##2 c`
                // associate left-to-right inside the implication.
                let allow_rhs = matches!(
                    self.current_kind(),
                    TokenKind::Identifier
                        | TokenKind::LParen
                        | TokenKind::IntegerLiteral
                        | TokenKind::HashHash
                );
                if allow_rhs {
                    let rest = self.parse_expr_bp(3);
                    Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::HashHash,
                            left: Box::new(cycles),
                            right: Box::new(rest),
                        },
                        self.span_from(start),
                    )
                } else {
                    Expression::new(
                        ExprKind::Unary {
                            op: UnaryOp::HashHash,
                            operand: Box::new(cycles),
                        },
                        self.span_from(start),
                    )
                }
            }

            _ => {
                self.error(format!("expected expression, found {:?} '{}'", self.current_kind(), self.current().text));
                self.bump();
                Expression::new(ExprKind::Empty, self.span_from(start))
            }
        }
    }

    /// Parse the items of an assignment pattern (`'{ ... }`) up to — but not
    /// including — the closing `}`. The opening `'{` must already be consumed.
    /// Shared by the `'{ ... }` and the tagged-union pattern-literal forms
    /// (`tagged member '{ ... }`, IEEE 1800-2023 §7.3.1).
    fn parse_assignment_pattern_items(&mut self) -> Vec<AssignmentPatternItem> {
        let start = self.current().span.start;
        let mut items = Vec::new();
        let mut first = true;
        loop {
            if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }

            // Possible items:
            // 1. default: expr
            // 2. type: expr
            // 3. name: expr
            // 4. expr (ordered)
            // 5. count { expr {, expr} } — replication form,
            //    only as the first item: `'{N{expr}}` (IEEE 1800-2017 §10.10.1).

            if self.at(TokenKind::KwDefault) {
                self.bump();
                self.expect(TokenKind::Colon);
                let expr = self.parse_expression();
                items.push(AssignmentPatternItem::Default(expr));
            } else if self.is_data_type_keyword() && self.peek_kind() == TokenKind::Colon {
                let dt = self.parse_data_type();
                self.expect(TokenKind::Colon);
                let expr = self.parse_expression();
                items.push(AssignmentPatternItem::Typed(dt, expr));
            } else if (self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier)) && self.peek_kind() == TokenKind::Colon {
                let name = self.parse_identifier();
                self.expect(TokenKind::Colon);
                let expr = self.parse_expression();
                items.push(AssignmentPatternItem::Named(name, expr));
            } else if self.at(TokenKind::StringLiteral) && self.peek_kind() == TokenKind::Colon {
                // IEEE 1800-2023 §10.10: associative-array literal
                // with a string key — `'{"key": value, ...}`.
                let key = self.parse_expression();
                self.expect(TokenKind::Colon);
                let val = self.parse_expression();
                items.push(AssignmentPatternItem::Keyed(key, val));
            } else {
                let count_expr = self.parse_expression();
                if self.at(TokenKind::Colon) {
                    // Expression-keyed entry `1 : val` — an
                    // associative-array / integer-indexed literal key
                    // (§10.9.2), e.g. `'{1:1, default:0}`.
                    self.bump();
                    let val = self.parse_expression();
                    items.push(AssignmentPatternItem::Keyed(count_expr, val));
                } else if first && self.at(TokenKind::LBrace) {
                    // Replication form: count { e1, e2, ... }
                    self.bump(); // '{'
                    let mut rep_items = Vec::new();
                    loop {
                        rep_items.push(self.parse_expression());
                        if self.eat(TokenKind::Comma).is_none() { break; }
                    }
                    self.expect(TokenKind::RBrace);
                    items.push(AssignmentPatternItem::Ordered(Expression::new(
                        ExprKind::Replication { count: Box::new(count_expr), exprs: rep_items },
                        self.span_from(start),
                    )));
                } else {
                    // An explicit-brace concat/replication ITEM —
                    // `'{{3{y}}}` is ONE element whose value is the
                    // 24-bit concat — parses to the same Replication
                    // node as the multiplier form `'{3{y}}` (three
                    // elements). Wrap the explicit form in Paren so
                    // the expansion sites can tell them apart: a bare
                    // Ordered(Replication) always means the
                    // §10.10.1 multiplier.
                    let item_expr = if matches!(count_expr.kind, ExprKind::Replication { .. })
                    {
                        Expression::new(
                            ExprKind::Paren(Box::new(count_expr)),
                            self.span_from(start),
                        )
                    } else {
                        count_expr
                    };
                    items.push(AssignmentPatternItem::Ordered(item_expr));
                }
            }
            first = false;

            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        items
    }

    fn parse_concatenation(&mut self) -> Expression {
        let start = self.current().span.start;
        self.expect(TokenKind::LBrace);
        
        // Handle streaming operators { >> [slice_size] { ... } } or { << [slice_size] { ... } }
        if self.at(TokenKind::ShiftRight) || self.at(TokenKind::ShiftLeft) {
            let left_to_right = self.at(TokenKind::ShiftLeft);
            self.bump();
            let slice_size = if !self.at(TokenKind::LBrace) {
                // Slice can be a type keyword (byte, shortint, int, longint, logic[N:0], etc.)
                // or an expression. Convert common type keywords to their bit widths.
                let tk = self.current().kind.clone();
                let type_width: Option<u32> = match tk {
                    TokenKind::KwByte => Some(8),
                    TokenKind::KwShortint => Some(16),
                    TokenKind::KwInt | TokenKind::KwInteger => Some(32),
                    TokenKind::KwLongint => Some(64),
                    _ => None,
                };
                if let Some(w) = type_width {
                    let start_s = self.current().span.start;
                    self.bump();
                    let lit = Expression::new(
                        ExprKind::Number(NumberLiteral::Integer {
                            size: Some(32), signed: false,
                            base: NumberBase::Decimal,
                            value: w.to_string(),
                            cached_val: std::cell::Cell::new(None),
                        }),
                        self.span_from(start_s),
                    );
                    Some(Box::new(lit))
                } else {
                    Some(Box::new(self.parse_expression()))
                }
            } else { None };
            self.expect(TokenKind::LBrace);
            let mut exprs = Vec::new();
            loop {
                if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }
                exprs.push(self.parse_expression());
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            self.expect(TokenKind::RBrace);
            self.expect(TokenKind::RBrace);
            return Expression::new(ExprKind::StreamOp { left_to_right, slice_size, exprs }, self.span_from(start));
        }

        if self.at(TokenKind::RBrace) {
            self.bump();
            return Expression::new(ExprKind::Concatenation(Vec::new()), self.span_from(start));
        }
        let first = self.parse_expression();
        // Check for replication: { count { ... } }
        if self.at(TokenKind::LBrace) {
            self.bump();
            let mut exprs = Vec::new();
            loop {
                if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }
                exprs.push(self.parse_expression());
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            self.expect(TokenKind::RBrace);
            self.expect(TokenKind::RBrace);
            return Expression::new(ExprKind::Replication {
                count: Box::new(first), exprs,
            }, self.span_from(start));
        }
        let mut exprs = vec![first];
        while self.eat(TokenKind::Comma).is_some() {
            if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }
            exprs.push(self.parse_expression());
        }
        self.expect(TokenKind::RBrace);
        Expression::new(ExprKind::Concatenation(exprs), self.span_from(start))
    }

    pub(super) fn parse_call_args(&mut self) -> Vec<Expression> {
        let mut args = Vec::new();
        self.expect(TokenKind::LParen);
        if self.at(TokenKind::RParen) { self.bump(); return args; }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
            
            let start = self.current().span.start;
            if self.at(TokenKind::Comma) {
                // Empty argument: foo(a, , b)
                args.push(Expression::new(ExprKind::Empty, self.span_from(start)));
            } else if self.is_data_type_keyword()
                && matches!(self.peek_kind(), TokenKind::RParen | TokenKind::Comma) {
                // §20.6.2: a bare built-in type keyword as a call argument, e.g.
                // `$bits(integer)` / `$bits(byte)`. The expression grammar can't
                // parse a lone type keyword, so capture it as an Ident carrying
                // the type name — `$bits`/`$size` map it to the type's width.
                let tok = self.bump();
                let span = tok.span;
                let ident = HierarchicalIdentifier {
                    root: None,
                    path: vec![HierPathSegment {
                        name: Identifier { name: tok.text.clone(), span },
                        selects: Vec::new(),
                    }],
                    span,
                    cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
                };
                args.push(Expression::new(ExprKind::Ident(ident), self.span_from(start)));
            } else if self.eat(TokenKind::Dot).is_some() {
                let name = self.parse_identifier();
                let expr = if self.eat(TokenKind::LParen).is_some() {
                    let e = if !self.at(TokenKind::RParen) { Some(Box::new(self.parse_expression())) } else { None };
                    self.expect(TokenKind::RParen);
                    e
                } else { None };
                args.push(Expression::new(ExprKind::NamedArg { name, expr }, self.span_from(start)));
            } else {
                args.push(self.parse_expression());
            }

            if self.eat(TokenKind::Comma).is_none() {
                // Check if we have a trailing comma before the closing paren: foo(a,)
                // In SV this is valid and means an empty trailing argument.
                break;
            } else if self.at(TokenKind::RParen) {
                // Trailing comma case
                args.push(Expression::new(ExprKind::Empty, self.span_from(self.current().span.start)));
                break;
            }
        }
        self.expect(TokenKind::RParen);
        args
    }

    /// Parse a hierarchical identifier (handles pkg::name and obj.member).
    /// Handles internal indices [expr] as well (e.g. successors[s].m_predecessors).
    pub(super) fn parse_hierarchical_identifier(&mut self) -> HierarchicalIdentifier {
        let start = self.current().span.start;
        // IEEE 1800-2023 §23.6: `$root`, `$unit`, `local::`-style roots can
        // start a hierarchical reference. `$root.foo.bar` shows up frequently
        // in cv32e40p macros expanding to absolute paths.
        let id = if self.at(TokenKind::KwThis) || self.at(TokenKind::KwSuper)
            || self.at(TokenKind::SystemIdentifier)
        {
            let tok = self.bump();
            Identifier { name: tok.text, span: tok.span }
        } else {
            self.parse_identifier()
        };
        let mut path = vec![HierPathSegment { name: id, selects: Vec::new() }];
        
        loop {
            if self.at(TokenKind::Dot) {
                self.bump();
                let member = self.parse_identifier();
                path.push(HierPathSegment { name: member, selects: Vec::new() });
            } else if self.at(TokenKind::DoubleColon) {
                self.bump();
                // §8.8: `Class::new` typed-constructor reference — `new` is a
                // keyword but names the constructor here.
                let member = if self.at(TokenKind::KwNew) {
                    let tok = self.bump();
                    crate::ast::Identifier { name: "new".to_string(), span: tok.span }
                } else {
                    self.parse_identifier()
                };
                path.push(HierPathSegment { name: member, selects: Vec::new() });
            } else if self.at(TokenKind::LBracket) {
                // Peek after the balanced bracket
                let mut p = self.pos + 1;
                let mut depth = 1;
                while depth > 0 && p < self.tokens.len() {
                    if self.tokens[p].kind == TokenKind::LBracket { depth += 1; }
                    else if self.tokens[p].kind == TokenKind::RBracket { depth -= 1; }
                    p += 1;
                }
                if let Some(t) = self.tokens.get(p) {
                    if t.kind == TokenKind::Dot || t.kind == TokenKind::DoubleColon || t.kind == TokenKind::LBracket {
                        // It's an internal index, consume it
                        self.bump();
                        let idx = self.parse_expression();
                        self.expect(TokenKind::RBracket);
                        if let Some(last) = path.last_mut() {
                            last.selects.push(idx);
                        }
                        continue;
                    }
                }
                break;
            } else {
                break;
            }
        }
        HierarchicalIdentifier {
            root: None,
            path,
            span: self.span_from(start),
            cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
        }
    }
    /// Handles indices [expr] as well.
    pub(super) fn parse_hierarchical_identifier_expr(&mut self) -> Expression {
        let start = self.current().span.start;
        let id = self.parse_identifier();
        let hier = HierarchicalIdentifier {
            root: None,
            path: vec![HierPathSegment { name: id, selects: Vec::new() }],
            span: self.span_from(start),
            cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
        };
        let mut res = Expression::new(ExprKind::Ident(hier), self.span_from(start));
        
        loop {
            if self.at(TokenKind::Dot) {
                self.bump();
                let member = self.parse_identifier();
                res = Expression::new(ExprKind::MemberAccess {
                    expr: Box::new(res), member,
                }, self.span_from(start));
            } else if self.at(TokenKind::DoubleColon) {
                self.bump();
                let member = self.parse_identifier();
                res = Expression::new(ExprKind::MemberAccess {
                    expr: Box::new(res), member,
                }, self.span_from(start));
            } else if self.at(TokenKind::LBracket) {
                self.bump();
                let idx = self.parse_expression();
                self.expect(TokenKind::RBracket);
                res = Expression::new(ExprKind::Index {
                    expr: Box::new(res), index: Box::new(idx),
                }, self.span_from(start));
            } else {
                break;
            }
        }
        res
    }
    fn infix_bp(&self) -> Option<(BinaryOp, u8, u8)> {
        let kind = self.current_kind();
        match kind {
            TokenKind::OrMinusArrow => Some((BinaryOp::OrMinusArrow, 1, 2)),
            TokenKind::OrFatArrow => Some((BinaryOp::OrFatArrow, 1, 2)),
            TokenKind::HashHash => Some((BinaryOp::HashHash, 28, 27)), // High precedence
            TokenKind::KwIff => Some((BinaryOp::Iff, 1, 2)),
            // LRM §16.9 sequence operators. Low precedence (just above
            // `|->`/`|=>`) so a property `a |-> (b throughout c)` parses
            // the way the parens suggest. `intersect`/sequence-`and`/`or`
            // bind tighter than `throughout`/`within`/`until`.
            TokenKind::KwThroughout => Some((BinaryOp::Throughout, 2, 3)),
            TokenKind::KwWithin => Some((BinaryOp::Within, 2, 3)),
            TokenKind::KwUntil => Some((BinaryOp::Until, 2, 3)),
            TokenKind::KwS_until => Some((BinaryOp::SUntil, 2, 3)),
            TokenKind::KwIntersect => Some((BinaryOp::Intersect, 4, 5)),
            // §16.9 sequence `and`/`or` — only inside a property/sequence body
            // (the `in_sva_seq` flag), else `or` is an event-list separator and
            // `and` a gate primitive. Bind just above intersect/below throughout.
            TokenKind::KwAnd if self.in_sva_seq => Some((BinaryOp::SeqAnd, 4, 5)),
            TokenKind::KwOr if self.in_sva_seq => Some((BinaryOp::SeqOr, 3, 4)),
            // Logical implication / equivalence (IEEE 1800-2017 Table
            // 11-2): lowest-precedence binary ops, below `||`, above the
            // ternary. `->` is right-associative.
            TokenKind::Arrow => Some((BinaryOp::LogImplies, 2, 1)),
            TokenKind::LogEquiv => Some((BinaryOp::LogEquiv, 1, 2)),
            TokenKind::LogOr => Some((BinaryOp::LogOr, 3, 4)),
            TokenKind::LogAnd => Some((BinaryOp::LogAnd, 5, 6)),
            TokenKind::BitOr => Some((BinaryOp::BitOr, 7, 8)),
            TokenKind::BitXor => Some((BinaryOp::BitXor, 9, 10)),
            TokenKind::BitXnor => Some((BinaryOp::BitXnor, 9, 10)),
            TokenKind::BitAnd => Some((BinaryOp::BitAnd, 11, 12)),
            TokenKind::Eq => Some((BinaryOp::Eq, 13, 14)),
            TokenKind::Neq => Some((BinaryOp::Neq, 13, 14)),
            TokenKind::CaseEq => Some((BinaryOp::CaseEq, 13, 14)),
            TokenKind::CaseNeq => Some((BinaryOp::CaseNeq, 13, 14)),
            TokenKind::WildcardEq => Some((BinaryOp::WildcardEq, 13, 14)),
            TokenKind::WildcardNeq => Some((BinaryOp::WildcardNeq, 13, 14)),
            TokenKind::Lt => Some((BinaryOp::Lt, 15, 16)),
            TokenKind::Gt => Some((BinaryOp::Gt, 15, 16)),
            TokenKind::Leq => Some((BinaryOp::Leq, 15, 16)),
            TokenKind::Geq => Some((BinaryOp::Geq, 15, 16)),
            TokenKind::ShiftLeft => Some((BinaryOp::ShiftLeft, 17, 18)),
            TokenKind::ShiftRight => Some((BinaryOp::ShiftRight, 17, 18)),
            TokenKind::ArithShiftLeft => Some((BinaryOp::ArithShiftLeft, 17, 18)),
            TokenKind::ArithShiftRight => Some((BinaryOp::ArithShiftRight, 17, 18)),
            TokenKind::Plus => Some((BinaryOp::Add, 19, 20)),
            TokenKind::Minus => Some((BinaryOp::Sub, 19, 20)),
            TokenKind::Star => Some((BinaryOp::Mul, 21, 22)),
            TokenKind::Slash => Some((BinaryOp::Div, 21, 22)),
            TokenKind::Percent => Some((BinaryOp::Mod, 21, 22)),
            // §11.3.2: ALL binary operators associate left to right — only
            // the conditional operator is right-associative. `2 ** 3 ** 2`
            // is (2**3)**2 = 64, unlike the right-associative `**` of most
            // general-purpose languages (which gave 512 here).
            TokenKind::DoubleStar => Some((BinaryOp::Power, 23, 24)), // left-assoc
            _ => None,
        }
    }

    /// Attach string-escape diagnostics (from `decode_string_escapes_checked`)
    /// at the given span. `is_error == true` becomes an Error, otherwise Warning.
    fn push_string_escape_diags(&mut self, diags: Vec<(bool, String)>, span: Span) {
        for (is_error, msg) in diags {
            self.diagnostics.push(if is_error {
                Diagnostic::error(msg, span)
            } else {
                Diagnostic::warning(msg, span)
            });
        }
    }
}

fn prefix_bp() -> u8 { 25 }
fn postfix_bp() -> (u8, ()) { (27, ()) }
fn ternary_bp() -> (u8, u8) { (1, 1) }

/// Parse a number literal string into our AST representation.
fn parse_number_literal(text: &str) -> NumberLiteral {
    // Time literal: <number><suffix> where suffix is one of fs/ps/ns/us/ms/s.
    // Stored in ABSOLUTE SECONDS as `NumberLiteral::Time` (LRM §22.7); the
    // simulator converts it against the global tick precision. Kept distinct
    // from a bare numeric delay (scaled by the module timeunit) so relative
    // timing is correct under sub-ns timescales.
    let time_suffixes: &[(&str, f64)] = &[
        ("fs", 1e-15), ("ps", 1e-12), ("ns", 1e-9),
        ("us", 1e-6),  ("ms", 1e-3),  ("s",  1.0),
    ];
    for (suf, scale) in time_suffixes {
        if text.ends_with(suf)
            && text.len() > suf.len()
            && text.as_bytes()[text.len() - suf.len() - 1].is_ascii_digit()
        {
            let mantissa = &text[..text.len() - suf.len()];
            if let Ok(v) = mantissa.replace('_', "").parse::<f64>() {
                return NumberLiteral::Time(v * *scale);
            }
        }
    }
    // Try to parse as real
    if text.contains('.') || (text.contains('e') && !text.contains('\'')) || (text.contains('E') && !text.contains('\'')) {
        if let Ok(v) = text.replace('_', "").parse::<f64>() {
            return NumberLiteral::Real(v);
        }
    }
    // Based literal
    if let Some(apos) = text.find('\'') {
        let size_str = &text[..apos];
        let size = if size_str.is_empty() { None } else { size_str.replace('_', "").parse().ok() };
        let rest = &text[apos+1..];
        let (signed, rest) = if rest.starts_with('s') || rest.starts_with('S') {
            (true, &rest[1..])
        } else { (false, rest) };
        let (base, value) = if rest.len() > 1 {
            let b = match rest.as_bytes()[0] {
                b'h' | b'H' => NumberBase::Hex,
                b'b' | b'B' => NumberBase::Binary,
                b'o' | b'O' => NumberBase::Octal,
                b'd' | b'D' => NumberBase::Decimal,
                _ => NumberBase::Decimal,
            };
            (b, rest[1..].to_string())
        } else {
            // `rest` is just the base specifier (e.g. "d", "b", "h", "o") with
            // no value digits — an illegal based literal per §5.7.1. Record the
            // base (so downstream validation reports the right alphabet) and
            // leave the value empty; the caller flags the missing value.
            let b = match rest.as_bytes().first().copied().unwrap_or(0) {
                b'h' | b'H' => NumberBase::Hex,
                b'b' | b'B' => NumberBase::Binary,
                b'o' | b'O' => NumberBase::Octal,
                b'd' | b'D' => NumberBase::Decimal,
                _ => NumberBase::Decimal,
            };
            (b, String::new())
        };
        return NumberLiteral::Integer { size, signed, base, value, cached_val: Cell::new(None) };
    }
    // Plain decimal — signed per Verilog standard (LRM section 5.7.1)
    NumberLiteral::Integer {
        size: None,
        signed: true,
        base: NumberBase::Decimal,
        value: text.replace('_', ""),
        cached_val: Cell::new(None),
    }
}

/// Validate a numeric literal token per IEEE 1800-2017 §5.7. Returns an error
/// message for a malformed literal that the value layer would otherwise coerce
/// to a wrong value; a well-formed literal returns `None`. Only based literals
/// (`<size>'<base><value>`) carry the structure inspected here — plain
/// decimals, reals and time literals have no apostrophe and return `None`.
fn validate_number_literal(text: &str) -> Option<String> {
    let apos = text.find('\'')?;
    // §5.7.1: a size, when present, must be a positive nonzero constant.
    let size_str = text[..apos].trim().replace('_', "");
    if !size_str.is_empty() {
        if let Ok(sz) = size_str.parse::<u128>() {
            if sz == 0 {
                return Some(format!(
                    "size of based literal '{}' must be greater than zero (IEEE 1800-2017 §5.7.1)",
                    text.trim()
                ));
            }
        }
    }
    // Split off an optional signed marker, then the base specifier.
    let rest = &text[apos + 1..];
    let rest = if rest.starts_with('s') || rest.starts_with('S') { &rest[1..] } else { rest };
    let base = match rest.as_bytes().first() {
        Some(b) => *b,
        None => return None, // bare `'` (cast operator) — nothing to validate
    };
    // §5.7.1: a decimal literal's value is either digits, OR a single `x`, OR a
    // single `z`/`?` (optionally with `_`) — never multiple, never mixed with
    // numeric digits, never a mix of x and z.
    if matches!(base, b'd' | b'D') {
        let value: String = rest[1..]
            .chars()
            .filter(|c| !c.is_whitespace() && *c != '_')
            .collect();
        let has_xz = value.chars().any(|c| matches!(c, 'x' | 'X' | 'z' | 'Z' | '?'));
        if has_xz {
            let single_x = value.len() == 1 && matches!(value.as_bytes()[0], b'x' | b'X');
            let single_z = value.len() == 1 && matches!(value.as_bytes()[0], b'z' | b'Z' | b'?');
            if !single_x && !single_z {
                return Some(format!(
                    "malformed decimal literal '{}': a decimal x/z value must be a single 'x' or a single 'z' (IEEE 1800-2017 §5.7.1)",
                    text.trim()
                ));
            }
        }
    }
    None
}

/// Validate the value digits of a *based* integer literal against its base
/// (IEEE 1800-2017 §5.7.1). Returns `Some(message)` when the literal is
/// illegal: an empty value (`8'd`), or a digit outside the base's alphabet
/// (`4'b2`, `3'o8`, `8'hg`). The scanner accepts any alphanumeric/`?xz_` run as
/// the value, so the base-specific legality check must happen here.
///
/// Tolerances, matching `Value::from_str_radix` and reference simulators:
///  - whitespace between the base and the value is legal (`8'd 6`),
///  - underscores are digit separators,
///  - `x`/`z`/`?` (unknown / high-Z) are legal in every base, including decimal.
fn validate_based_literal_value(base: NumberBase, value: &str) -> Option<String> {
    let digits: String = value.chars().filter(|c| !c.is_whitespace() && *c != '_').collect();
    if digits.is_empty() {
        return Some("missing value digits in based number literal".to_string());
    }
    let in_base = |c: char| match base {
        NumberBase::Binary  => matches!(c, '0' | '1' | 'x' | 'X' | 'z' | 'Z' | '?'),
        NumberBase::Octal   => matches!(c, '0'..='7' | 'x' | 'X' | 'z' | 'Z' | '?'),
        NumberBase::Decimal => matches!(c, '0'..='9' | 'x' | 'X' | 'z' | 'Z' | '?'),
        NumberBase::Hex     => matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F' | 'x' | 'X' | 'z' | 'Z' | '?'),
    };
    digits.chars().find(|&c| !in_base(c))
        .map(|bad| format!("invalid digit '{}' for {:?} base in number literal", bad, base))
}

/// Decode SystemVerilog string-literal escape sequences (IEEE 1800-2017 §5.9).
/// Input is the *interior* of the literal (no surrounding quotes). Returns the
/// decoded bytes plus any diagnostics (an error for `\x` with no hex digit, a
/// warning for an unknown letter escape); the caller attaches them at the
/// string token's span.
fn decode_string_escapes_checked(raw: &str) -> (String, Vec<(bool, String)>) {
    let mut diags: Vec<(bool, String)> = Vec::new();
    let s = decode_string_escapes_inner(raw, &mut diags);
    (s, diags)
}

fn decode_string_escapes_inner(raw: &str, diags: &mut Vec<(bool, String)>) -> String {
    let bytes = raw.as_bytes();
    // A SystemVerilog string is a BYTE string (§5.9/§6.16). Every source
    // byte — literal text and escape-produced alike — is stored as its
    // Latin-1 char (U+0000..U+00FF, one char per byte), the exact inverse of
    // `Value::from_string`'s byte extraction; the stdout sink re-encodes
    // those chars as single bytes. NEVER route through a lossy UTF-8
    // conversion (it collapsed every escape byte >= 0x80 to U+FFFD, which
    // read back as 0xBD), and never keep multi-byte source chars as one Rust
    // char (the byte count — string width, len(), getc() — must match the
    // reference's byte semantics).
    let mut out = String::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'\\' || i + 1 >= bytes.len() {
            out.push(char::from(bytes[i]));
            i += 1;
            continue;
        }
        match bytes[i + 1] {
            b'n' => { out.push('\n'); i += 2; }
            b't' => { out.push('\t'); i += 2; }
            b'r' => { out.push('\r'); i += 2; }
            b'\\' => { out.push('\\'); i += 2; }
            b'"' => { out.push('"'); i += 2; }
            b'\'' => { out.push('\''); i += 2; }
            b'a' => { out.push('\u{07}'); i += 2; }
            b'b' => { out.push('\u{08}'); i += 2; }
            b'f' => { out.push('\u{0c}'); i += 2; }
            b'v' => { out.push('\u{0b}'); i += 2; }
            b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' => {
                // 1-3 octal digits
                let mut j = i + 1;
                let mut val: u32 = 0;
                let mut digits = 0;
                while j < bytes.len() && digits < 3 && (b'0'..=b'7').contains(&bytes[j]) {
                    val = val * 8 + (bytes[j] - b'0') as u32;
                    j += 1;
                    digits += 1;
                }
                out.push(char::from((val & 0xff) as u8));
                i = j;
            }
            b'x' => {
                // IEEE 1800-2017 §5.9: `\x` MUST be followed by at least one hex
                // digit. Previously an absent digit silently emitted a NUL and
                // let the trailing characters through (`"\xGG"` → NUL,`GG`); that
                // is a lexical error, not silent garbage.
                let mut j = i + 2;
                let mut val: u32 = 0;
                let mut digits = 0;
                while j < bytes.len() && digits < 2 {
                    let c = bytes[j];
                    let d = if c.is_ascii_digit() { c - b'0' }
                            else if (b'a'..=b'f').contains(&c) { c - b'a' + 10 }
                            else if (b'A'..=b'F').contains(&c) { c - b'A' + 10 }
                            else { break };
                    val = val * 16 + d as u32;
                    j += 1;
                    digits += 1;
                }
                if digits == 0 {
                    diags.push((true, "invalid \\x escape in string literal: expected at least one hex digit (IEEE 1800-2017 §5.9)".to_string()));
                    // Emit nothing for the malformed escape and skip the `\x` so
                    // the remaining characters are still processed normally.
                    i += 2;
                } else {
                    out.push(char::from((val & 0xff) as u8));
                    i = j;
                }
            }
            _ => {
                // Unknown letter escape: §5.9 leaves this implementation-defined.
                // a reference simulator (the oracle) drops the backslash and keeps the char, so
                // we match that VALUE, but emit a warning so the mangle is not
                // silent.
                diags.push((false, format!(
                    "unknown escape sequence '\\{}' in string literal (IEEE 1800-2017 §5.9)",
                    bytes[i + 1] as char
                )));
                out.push(char::from(bytes[i + 1]));
                i += 2;
            }
        }
    }
    out
}
