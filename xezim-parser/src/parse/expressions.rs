//! Expression parsing (IEEE 1800-2017 §A.8) with Pratt precedence climbing.

use super::Parser;
use crate::ast::expr::*;
use crate::ast::Span;
use crate::ast::Identifier;
use crate::lexer::token::TokenKind;
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
                let member = self.parse_identifier();
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
    fn parse_expr_bp(&mut self, min_bp: u8) -> Expression {
        let start = self.current().span.start;
        let mut lhs = self.parse_prefix();

        loop {
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
                        let lo = self.parse_expression();
                        self.expect(TokenKind::Colon);
                        let hi = self.parse_expression();
                        self.expect(TokenKind::RBracket);
                        ranges.push(Expression::new(ExprKind::Range(Box::new(lo), Box::new(hi)), self.span_from(start)));
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
                        if self.eat(TokenKind::LBrace).is_some() {
                            let mut depth = 1;
                            while depth > 0 && !self.at(TokenKind::Eof) {
                                if self.at(TokenKind::LBrace) { depth += 1; }
                                else if self.at(TokenKind::RBrace) { depth -= 1; }
                                self.bump();
                            }
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
                let member = self.parse_identifier();
                lhs = Expression::new(ExprKind::MemberAccess {
                    expr: Box::new(lhs), member,
                }, self.span_from(start));
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
                    // Optional constraint block after `with` or `with (...)`
                    if self.eat(TokenKind::LBrace).is_some() {
                        let mut depth = 1;
                        while depth > 0 && !self.at(TokenKind::Eof) {
                            if self.at(TokenKind::LBrace) { depth += 1; }
                            else if self.at(TokenKind::RBrace) { depth -= 1; }
                            self.bump();
                        }
                    }
                }
                lhs = call_expr;
                continue;
            }

            // Index/range select: [expr] or [expr:expr] or [expr+:expr] or new[size]
            if self.at(TokenKind::LBracket) {
                self.bump();
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

            // with clause: expr with ( filter_expr )
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
                lhs = Expression::new(ExprKind::Paren(Box::new(inner)), self.span_from(start));
                continue;
            }

            break;
        }

        lhs
    }

    /// Parse prefix / primary expression.
    pub(super) fn parse_prefix(&mut self) -> Expression {
        let start = self.current().span.start;

        match self.current_kind() {
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

            // Concatenation / replication: { ... }
            TokenKind::LBrace => self.parse_concatenation(),

            // Tagged union member expression: `tagged Name` or `tagged Name(expr)`.
            // We discard the tag and return the payload (or 0 for void members).
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
                } else {
                    None
                };
                Expression::new(ExprKind::Tagged { tag, inner }, self.span_from(start))
            }

            // Assignment pattern: '{ ... }
            TokenKind::ApostropheLBrace => {
                self.bump();
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
                    //    only as the first item: `'{N{expr}}` (IEEE 1800-2017
                    //    §10.10.1).

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
                    } else {
                        let count_expr = self.parse_expression();
                        if first && self.at(TokenKind::LBrace) {
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
                            items.push(AssignmentPatternItem::Ordered(count_expr));
                        }
                    }
                    first = false;

                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::RBrace);
                Expression::new(ExprKind::AssignmentPattern(items), self.span_from(start))
            }

            // Number literals
            TokenKind::IntegerLiteral | TokenKind::RealLiteral | TokenKind::TimeLiteral => {
                let tok = self.bump();
                let num = parse_number_literal(&tok.text);
                let expr = Expression::new(ExprKind::Number(num), self.span_from(start));
                if self.current().kind == TokenKind::IntegerLiteral
                    && self.current().text == "'"
                    && self.peek_kind() == TokenKind::LParen
                {
                    self.bump();
                    self.expect(TokenKind::LParen);
                    let inner = self.parse_expression();
                    self.expect(TokenKind::RParen);
                    Expression::new(ExprKind::Paren(Box::new(inner)), self.span_from(start))
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
                let s = tok.text[1..tok.text.len()-1].to_string();
                Expression::new(ExprKind::StringLiteral(s), self.span_from(start))
            }

            // System call: $display, etc.
            TokenKind::SystemIdentifier => {
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

            // Identifier (possibly followed by function call or class scope)
            TokenKind::Identifier | TokenKind::EscapedIdentifier => {
                let id = self.parse_identifier();
                // Skip optional parameterized type list #(...) for class scope
                if self.eat(TokenKind::Hash).is_some() {
                    if self.eat(TokenKind::LParen).is_some() {
                        let mut depth = 1;
                        while depth > 0 && !self.at(TokenKind::Eof) {
                            if self.at(TokenKind::LParen) { depth += 1; }
                            else if self.at(TokenKind::RParen) { depth -= 1; }
                            self.bump();
                        }
                    }
                }
                let hier = HierarchicalIdentifier {
                    root: None,
                    path: vec![HierPathSegment { name: id, selects: Vec::new() }],
                    span: self.span_from(start),
                    cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
                };
                let expr = Expression::new(ExprKind::Ident(hier), self.span_from(start));
                // Check for type cast: identifier'(expr)  e.g. my_type'(value)
                if self.current().text == "'" && self.peek_kind() == TokenKind::LParen {
                    self.bump(); // skip '
                    self.bump(); // skip (
                    let inner = self.parse_expression();
                    self.expect(TokenKind::RParen);
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
                self.bump(); // skip type keyword
                self.bump(); // skip '
                self.expect(TokenKind::LParen);
                let inner = self.parse_expression();
                self.expect(TokenKind::RParen);
                Expression::new(ExprKind::Paren(Box::new(inner)), self.span_from(start))
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
                Expression::new(ExprKind::Ident(hier), self.span_from(start))
            }

            // Data type keywords used as expressions (e.g. $bits(int))
            k if self.is_data_type_keyword() || k == TokenKind::KwVoid => {
                let _dt = self.parse_data_type();
                // Treat as empty expression for now, but we've consumed the type
                Expression::new(ExprKind::Empty, self.span_from(start))
            }

            TokenKind::HashHash => {
                let start = self.current().span.start; self.bump();
                let operand = self.parse_expr_bp(30);
                Expression::new(ExprKind::Unary { op: UnaryOp::HashHash, operand: Box::new(operand) }, self.span_from(start))
            }

            _ => {
                self.error(format!("expected expression, found {:?} '{}'", self.current_kind(), self.current().text));
                self.bump();
                Expression::new(ExprKind::Empty, self.span_from(start))
            }
        }
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
        let id = if self.at(TokenKind::KwThis) || self.at(TokenKind::KwSuper) {
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
                let member = self.parse_identifier();
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
        let mut hier = HierarchicalIdentifier {
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
            TokenKind::DoubleStar => Some((BinaryOp::Power, 24, 23)), // right-assoc
            _ => None,
        }
    }
}

fn prefix_bp() -> u8 { 25 }
fn postfix_bp() -> (u8, ()) { (27, ()) }
fn ternary_bp() -> (u8, u8) { (1, 1) }

/// Parse a number literal string into our AST representation.
fn parse_number_literal(text: &str) -> NumberLiteral {
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
            (NumberBase::Decimal, rest.to_string())
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
