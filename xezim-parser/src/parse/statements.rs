//! Statement parsing (IEEE 1800-2017 §A.6)

use super::Parser;
use crate::ast::stmt::*;
use crate::ast::expr::{ExprKind, BinaryOp, Expression, NumberLiteral, NumberBase};
use crate::ast::types::{DataType, Lifetime};
use crate::lexer::token::TokenKind;
use std::cell::Cell;
use std::collections::HashMap;

impl Parser {
    pub(super) fn parse_statement(&mut self) -> Statement {
        let start = self.current().span.start;

        match self.current_kind() {
            TokenKind::Directive => { self.bump(); self.parse_statement() }
            TokenKind::KwBegin => self.parse_seq_block(),
            TokenKind::KwFork => self.parse_par_block(),
            TokenKind::KwIf | TokenKind::KwUnique | TokenKind::KwUnique0 | TokenKind::KwPriority => {
                self.parse_if_or_case()
            }
            TokenKind::KwCase | TokenKind::KwCasex | TokenKind::KwCasez => self.parse_case_statement(),
            TokenKind::KwParameter | TokenKind::KwLocalparam => {
                // Local `parameter`/`localparam` inside a procedural block is
                // semantically equivalent to a const var decl with an init.
                let decl = self.parse_parameter_decl_stmt();
                let span = self.span_from(start);
                if let crate::ast::decl::ParameterKind::Data { data_type, assignments } = decl.kind {
                    let declarators: Vec<VarDeclarator> = assignments.into_iter().map(|a| {
                        VarDeclarator { name: a.name, dimensions: a.dimensions, init: a.init, span: a.span }
                    }).collect();
                    return Statement::new(StatementKind::VarDecl {
                        data_type, lifetime: None, declarators,
                    }, span);
                }
                return Statement::new(StatementKind::Null, span);
            }
            TokenKind::KwRandcase => self.parse_randcase(),
            TokenKind::KwRandsequence => self.parse_randsequence(),
            TokenKind::KwFor => self.parse_for_statement(),
            TokenKind::KwForeach => self.parse_foreach_statement(),
            TokenKind::KwWhile => self.parse_while_statement(),
            TokenKind::KwDo => self.parse_do_while_statement(),
            TokenKind::KwRepeat => self.parse_repeat_statement(),
            TokenKind::KwForever => {
                self.bump();
                let body = self.parse_statement();
                Statement::new(StatementKind::Forever { body: Box::new(body) }, self.span_from(start))
            }
            TokenKind::KwReturn => {
                self.bump();
                let expr = if !self.at(TokenKind::Semicolon) {
                    Some(self.parse_expression())
                } else { None };
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::Return(expr), self.span_from(start))
            }
            TokenKind::KwBreak => { self.bump(); self.expect(TokenKind::Semicolon); Statement::new(StatementKind::Break, self.span_from(start)) }
            TokenKind::KwContinue => { self.bump(); self.expect(TokenKind::Semicolon); Statement::new(StatementKind::Continue, self.span_from(start)) }
            TokenKind::KwWait => {
                self.bump();
                if self.eat(TokenKind::KwFork).is_some() {
                    self.expect(TokenKind::Semicolon);
                    Statement::new(StatementKind::WaitFork, self.span_from(start))
                } else {
                    self.expect(TokenKind::LParen);
                    let cond = self.parse_expression();
                    self.expect(TokenKind::RParen);
                    let stmt = self.parse_statement();
                    Statement::new(StatementKind::Wait { condition: cond, stmt: Box::new(stmt) }, self.span_from(start))
                }
            }
            TokenKind::KwStatic | TokenKind::KwAutomatic | TokenKind::KwLocal => {
                let mut lifetime = None;
                if self.at(TokenKind::KwStatic) { lifetime = Some(Lifetime::Static); self.bump(); }
                else if self.at(TokenKind::KwAutomatic) { lifetime = Some(Lifetime::Automatic); self.bump(); }
                else if self.at(TokenKind::KwLocal) { self.bump(); } // skip local
                
                if lifetime.is_none() {
                    if self.at(TokenKind::KwStatic) { lifetime = Some(Lifetime::Static); self.bump(); }
                    else if self.at(TokenKind::KwAutomatic) { lifetime = Some(Lifetime::Automatic); self.bump(); }
                }
                let data_type = if self.is_data_type_keyword() || self.at(TokenKind::Identifier) {
                    self.parse_data_type()
                } else {
                    DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
                };
                let mut declarators = Vec::new();
                loop {
                    let ds = self.current().span.start;
                    let name = self.parse_identifier();
                    let dimensions = self.parse_unpacked_dimensions();
                    let init = if self.eat(TokenKind::Assign).is_some() {
                        Some(self.parse_expression())
                    } else { None };
                    declarators.push(VarDeclarator { name, dimensions, init, span: self.span_from(ds) });
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::VarDecl { data_type, lifetime, declarators }, self.span_from(start))
            }
            TokenKind::KwTypedef => {
                let _ = self.parse_typedef_declaration();
                Statement::new(StatementKind::Null, self.span_from(start))
            }
            TokenKind::KwDisable => {
                self.bump();
                if self.eat(TokenKind::KwFork).is_some() {
                    self.expect(TokenKind::Semicolon);
                    Statement::new(StatementKind::Null, self.span_from(start))
                } else {
                    let name = self.parse_identifier();
                    self.expect(TokenKind::Semicolon);
                    Statement::new(StatementKind::Disable(name), self.span_from(start))
                }
            }
            TokenKind::KwAssert | TokenKind::KwAssume | TokenKind::KwCover | TokenKind::KwExpect => {
                Statement::new(StatementKind::Assertion(self.parse_assertion_statement()), self.span_from(start))
            }
            TokenKind::KwAssign => {
                self.bump();
                let lv = self.parse_expression();
                self.expect(TokenKind::Assign);
                let rv = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::ProceduralContinuous(
                    ProceduralContinuous::Assign { lvalue: lv, rvalue: rv }
                ), self.span_from(start))
            }
            TokenKind::KwForce => {
                self.bump();
                let lv = self.parse_expression();
                self.expect(TokenKind::Assign);
                let rv = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::ProceduralContinuous(
                    ProceduralContinuous::Force { lvalue: lv, rvalue: rv }
                ), self.span_from(start))
            }
            TokenKind::KwDeassign => {
                self.bump();
                let lv = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::ProceduralContinuous(
                    ProceduralContinuous::Deassign(lv)
                ), self.span_from(start))
            }
            TokenKind::KwCoverpoint => {
                self.bump();
                let expr = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::Coverpoint { name: None, expr, span: self.span_from(start) }, self.span_from(start))
            }
            TokenKind::KwCross => {
                self.bump();
                let mut items = Vec::new();
                loop {
                    items.push(self.parse_expression());
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::Cross { name: None, items, span: self.span_from(start) }, self.span_from(start))
            }
            TokenKind::KwRelease => {
                self.bump();
                let lv = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::ProceduralContinuous(
                    ProceduralContinuous::Release(lv)
                ), self.span_from(start))
            }
            // Timing control: @
            TokenKind::At => {
                let ctrl = self.parse_event_control();
                let stmt = self.parse_statement();
                Statement::new(StatementKind::TimingControl {
                    control: TimingControl::Event(ctrl),
                    stmt: Box::new(stmt),
                }, self.span_from(start))
            }
            // Event trigger: ->, ->>
            TokenKind::Arrow | TokenKind::DoubleArrow => {
                let nonblocking = self.bump().kind == TokenKind::DoubleArrow;
                let target = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                let name = match target.kind {
                    ExprKind::Ident(hier) => {
                        hier.path.last().map(|seg| seg.name.clone()).unwrap_or_else(|| crate::ast::Identifier {
                            name: "event".to_string(),
                            span: self.span_from(start),
                        })
                    }
                    _ => crate::ast::Identifier {
                        name: "event".to_string(),
                        span: self.span_from(start),
                    },
                };
                Statement::new(StatementKind::EventTrigger { nonblocking, name, span: self.span_from(start) }, self.span_from(start))
            }
            // Delay control: #
            TokenKind::Hash => {
                self.bump();
                let delay = self.parse_expression();
                let stmt = self.parse_statement();
                Statement::new(StatementKind::TimingControl {
                    control: TimingControl::Delay(delay),
                    stmt: Box::new(stmt),
                }, self.span_from(start))
            }
            // Variable declaration (data type keywords)
            k if self.is_data_type_keyword() && k != TokenKind::KwEvent &&
                 !(self.peek_kind() == TokenKind::IntegerLiteral && {
                     let next_text = self.tokens.get(self.pos + 1).map(|t| t.text.as_str()).unwrap_or("");
                     next_text == "'"
                 }) => {
                let data_type = self.parse_data_type();
                let lifetime = None;
                let mut declarators = Vec::new();
                loop {
                    let ds = self.current().span.start;
                    let name = self.parse_identifier();
                    let dimensions = self.parse_unpacked_dimensions();
                    let init = if self.eat(TokenKind::Assign).is_some() {
                        Some(self.parse_expression())
                    } else { None };
                    declarators.push(VarDeclarator { name, dimensions, init, span: self.span_from(ds) });
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::VarDecl { data_type, lifetime, declarators }, self.span_from(start))
            }
            TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef => {
                let start = self.current().span.start;
                self.bump();
                while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::Null, self.span_from(start))
            }
            // Null statement
            TokenKind::Semicolon => {
                self.bump();
                Statement::new(StatementKind::Null, self.span_from(start))
            }
            // Event declaration
            TokenKind::KwEvent => {
                self.bump();
                let mut names = Vec::new();
                loop {
                    names.push(self.parse_identifier());
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::Null, self.span_from(start)) // Skip for now
            }
            // User-defined type variable declaration: TypeName var [= expr];
            // Detected by: Identifier followed by Identifier, Hash (if followed by identifier),
            // or DoubleColon (if followed by identifier).
            // Expressions starting with Identifier: class_scope::member, pkg::member, obj.member
            // Also: `typedef_t [packed-dims] var;` — distinguish from `arr[idx] = ...`
            // by requiring an Identifier after the balanced [..] block.
            TokenKind::Identifier if !self.peek_is_class_scope() && (
                matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::Hash | TokenKind::DoubleColon)
                || (self.peek_kind() == TokenKind::LBracket && {
                    // Look-ahead: balance brackets and check what follows.
                    let mut depth: i32 = 0;
                    let mut k: usize = 0;
                    let mut next_after = TokenKind::Eof;
                    loop {
                        let kind = self.peek_kind_n(k + 1);
                        match kind {
                            TokenKind::LBracket => depth += 1,
                            TokenKind::RBracket => {
                                depth -= 1;
                                if depth == 0 {
                                    next_after = self.peek_kind_n(k + 2);
                                    break;
                                }
                            }
                            TokenKind::Eof => break,
                            _ => {}
                        }
                        k += 1;
                        if k > 64 { break; }
                    }
                    matches!(next_after, TokenKind::Identifier)
                })
            ) =>
            {
                let data_type = self.parse_data_type();
                let mut declarators = Vec::new();
                loop {
                    let ds = self.current().span.start;
                    let name = self.parse_identifier();
                    let dimensions = self.parse_unpacked_dimensions();
                    let init = if self.eat(TokenKind::Assign).is_some() {
                        Some(self.parse_expression())
                    } else { None };
                    declarators.push(VarDeclarator { name, dimensions, init, span: self.span_from(ds) });
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Semicolon);
                Statement::new(StatementKind::VarDecl { data_type, lifetime: None, declarators }, self.span_from(start))
            }
            // Expression statement (assignment, call, inc/dec)
            _ => {
                // Parse LHS expression, but stop at <= to allow nonblocking assignment
                let expr = self.parse_lvalue_or_expr();
                // Check for blocking/nonblocking assignment
                if self.at(TokenKind::Assign) || self.at_any(&[
                    TokenKind::PlusAssign, TokenKind::MinusAssign,
                    TokenKind::StarAssign, TokenKind::SlashAssign,
                    TokenKind::PercentAssign, TokenKind::AndAssign,
                    TokenKind::OrAssign, TokenKind::XorAssign,
                    TokenKind::ShiftLeftAssign, TokenKind::ShiftRightAssign,
                    TokenKind::ArithShiftLeftAssign, TokenKind::ArithShiftRightAssign,
                ]) {
                    let op_kind = self.current().kind.clone();
                    self.bump();
                    let rhs = self.parse_expression();
                    self.expect(TokenKind::Semicolon);
                    // Expand compound assignments: lhs += rhs => lhs = lhs + rhs
                    let rvalue = match op_kind {
                        TokenKind::PlusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Add, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::MinusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Sub, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::StarAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mul, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::SlashAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Div, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::PercentAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mod, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::AndAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitAnd, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::OrAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitOr, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::XorAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitXor, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::ShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftLeft, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::ShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftRight, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::ArithShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftLeft, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        TokenKind::ArithShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftRight, left: Box::new(expr.clone()), right: Box::new(rhs) }, self.span_from(start)),
                        _ => rhs, // TokenKind::Assign - plain assignment
                    };
                    Statement::new(StatementKind::BlockingAssign { lvalue: expr, rvalue }, self.span_from(start))
                } else if self.at(TokenKind::Leq) {
                    // Nonblocking assignment: lvalue <= rvalue
                    self.bump();
                    let rvalue = self.parse_expression();
                    self.expect(TokenKind::Semicolon);
                    Statement::new(StatementKind::NonblockingAssign {
                        lvalue: expr, delay: None, rvalue,
                    }, self.span_from(start))
                } else {
                    self.expect(TokenKind::Semicolon);
                    Statement::new(StatementKind::Expr(expr), self.span_from(start))
                }
            }
        }
    }

    fn parse_seq_block(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwBegin);
        let name = if self.eat(TokenKind::Colon).is_some() {
            Some(self.parse_identifier())
        } else { None };
        let mut stmts = Vec::new();
        while !self.at(TokenKind::KwEnd) && !self.at(TokenKind::Eof) {
            stmts.push(self.parse_statement());
        }
        self.expect(TokenKind::KwEnd);
        let _ = self.parse_end_label();
        Statement::new(StatementKind::SeqBlock { name, stmts }, self.span_from(start))
    }

    fn parse_par_block(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwFork);
        let name = if self.eat(TokenKind::Colon).is_some() {
            Some(self.parse_identifier())
        } else { None };
        let mut stmts = Vec::new();
        while !self.at_any(&[TokenKind::KwJoin, TokenKind::KwJoin_any, TokenKind::KwJoin_none, TokenKind::Eof]) {
            stmts.push(self.parse_statement());
        }
        let join_type = match self.current_kind() {
            TokenKind::KwJoin_any => { self.bump(); JoinType::JoinAny }
            TokenKind::KwJoin_none => { self.bump(); JoinType::JoinNone }
            _ => { self.expect(TokenKind::KwJoin); JoinType::Join }
        };
        let _ = self.parse_end_label();
        Statement::new(StatementKind::ParBlock { name, join_type, stmts }, self.span_from(start))
    }

    fn parse_if_or_case(&mut self) -> Statement {
        let up = self.parse_unique_priority();
        if self.at(TokenKind::KwIf) {
            self.parse_if_with_priority(up)
        } else if self.at_any(&[TokenKind::KwCase, TokenKind::KwCasex, TokenKind::KwCasez]) {
            self.parse_case_with_priority(up)
        } else {
            self.parse_if_with_priority(up)
        }
    }

    fn parse_unique_priority(&mut self) -> Option<UniquePriority> {
        match self.current_kind() {
            TokenKind::KwUnique => { self.bump(); Some(UniquePriority::Unique) }
            TokenKind::KwUnique0 => { self.bump(); Some(UniquePriority::Unique0) }
            TokenKind::KwPriority => { self.bump(); Some(UniquePriority::Priority) }
            _ => None,
        }
    }

    fn parse_if_with_priority(&mut self, up: Option<UniquePriority>) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwIf);
        self.expect(TokenKind::LParen);
        let condition = self.parse_expression();
        self.expect(TokenKind::RParen);
        let then_stmt = self.parse_statement();
        let else_stmt = if self.eat(TokenKind::KwElse).is_some() {
            Some(Box::new(self.parse_statement()))
        } else { None };
        Statement::new(StatementKind::If {
            condition, then_stmt: Box::new(then_stmt), else_stmt,
            unique_priority: up,
        }, self.span_from(start))
    }

    fn parse_case_statement(&mut self) -> Statement {
        self.parse_case_with_priority(None)
    }

    fn parse_case_with_priority(&mut self, up: Option<UniquePriority>) -> Statement {
        let start = self.current().span.start;
        let kind = match self.bump().kind {
            TokenKind::KwCasex => CaseKind::Casex,
            TokenKind::KwCasez => CaseKind::Casez,
            _ => CaseKind::Case,
        };
        self.expect(TokenKind::LParen);
        let expr = self.parse_expression();
        self.expect(TokenKind::RParen);
        // Check for "inside" keyword
        let kind = if kind == CaseKind::Case && self.eat(TokenKind::KwInside).is_some() {
            CaseKind::CaseInside
        } else { kind };

        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndcase) && !self.at(TokenKind::Eof) {
            let istart = self.current().span.start;
            if self.eat(TokenKind::KwDefault).is_some() {
                self.eat(TokenKind::Colon);
                let stmt = self.parse_statement();
                items.push(CaseItem { patterns: Vec::new(), is_default: true, stmt, span: self.span_from(istart) });
            } else {
                let mut patterns = Vec::new();
                loop {
                    // case_inside permits value_range patterns of the form
                    // `[lo:hi]`. Detect the bare-LBracket start and consume
                    // the range as a single Expr::Range value; downstream
                    // elaboration / case-eval can map it.
                    if matches!(kind, CaseKind::CaseInside) && self.at(TokenKind::LBracket) {
                        let bstart = self.current().span.start;
                        self.bump(); // [
                        let lo = self.parse_expression();
                        self.expect(TokenKind::Colon);
                        let hi = self.parse_expression();
                        self.expect(TokenKind::RBracket);
                        patterns.push(Expression::new(
                            ExprKind::Range(Box::new(lo), Box::new(hi)),
                            self.span_from(bstart),
                        ));
                    } else {
                        patterns.push(self.parse_expression());
                    }
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Colon);
                let stmt = self.parse_statement();
                items.push(CaseItem { patterns, is_default: false, stmt, span: self.span_from(istart) });
            }
        }
        self.expect(TokenKind::KwEndcase);
        Statement::new(StatementKind::Case {
            unique_priority: up, kind, expr, items,
        }, self.span_from(start))
    }

    fn parse_for_statement(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwFor);
        self.expect(TokenKind::LParen);
        // Init
        let mut init = Vec::new();
        if !self.at(TokenKind::Semicolon) {
            if self.is_data_type_keyword() ||
                (self.at(TokenKind::Identifier) &&
                    matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash)) {
                let dt = self.parse_data_type();
                let name = self.parse_identifier();
                self.expect(TokenKind::Assign);
                let val = self.parse_expression();
                init.push(ForInit::VarDecl { data_type: dt, name, init: val });
            } else {
                let lv = self.parse_expression();
                self.expect(TokenKind::Assign);
                let rv = self.parse_expression();
                init.push(ForInit::Assign { lvalue: lv, rvalue: rv });
            }
        }
        self.expect(TokenKind::Semicolon);
        let condition = if !self.at(TokenKind::Semicolon) {
            Some(self.parse_expression())
        } else { None };
        self.expect(TokenKind::Semicolon);
        let mut step = Vec::new();
        if !self.at(TokenKind::RParen) {
            loop {
                // Step can be assignment (i = i + 1 / i += 2) or expression (i++).
                let expr = self.parse_lvalue_or_expr();
                if self.at(TokenKind::Assign) || self.at_any(&[
                    TokenKind::PlusAssign, TokenKind::MinusAssign,
                    TokenKind::StarAssign, TokenKind::SlashAssign,
                    TokenKind::PercentAssign, TokenKind::AndAssign,
                    TokenKind::OrAssign, TokenKind::XorAssign,
                    TokenKind::ShiftLeftAssign, TokenKind::ShiftRightAssign,
                    TokenKind::ArithShiftLeftAssign, TokenKind::ArithShiftRightAssign,
                ]) {
                    let op_kind = self.current().kind;
                    self.bump();
                    let rhs = self.parse_expression();
                    let span = self.span_from(start);
                    let rvalue = match op_kind {
                        TokenKind::PlusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Add, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::MinusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Sub, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::StarAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mul, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::SlashAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Div, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::PercentAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mod, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::AndAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitAnd, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::OrAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitOr, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::XorAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitXor, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftLeft, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftRight, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ArithShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftLeft, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        TokenKind::ArithShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftRight, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                        _ => rhs,
                    };
                    step.push(Expression::new(
                        ExprKind::AssignExpr { lvalue: Box::new(expr), rvalue: Box::new(rvalue) },
                        span,
                    ));
                } else {
                    step.push(expr);
                }
                if !self.eat(TokenKind::Comma).is_some() { break; }
            }
        }
        self.expect(TokenKind::RParen);
        let body = self.parse_statement();
        Statement::new(StatementKind::For {
            init, condition, step, body: Box::new(body),
        }, self.span_from(start))
    }

    fn parse_foreach_statement(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwForeach);
        self.expect(TokenKind::LParen);
        
        // Array name: can be hierarchical, but NO indices yet.
        let array_hier = self.parse_hierarchical_identifier();
        let array_expr = Expression::new(ExprKind::Ident(array_hier), self.span_from(start));
        // Actually, parse_expression_prefix might be too limited.
        // Let's just parse a HierarchicalIdentifier manually or via a new helper.
        // For UVM, most are simple or pkg::name.
        
        let mut vars = Vec::new();
        self.expect(TokenKind::LBracket);
        loop {
            if self.at(TokenKind::RBracket) { break; }
            if self.at(TokenKind::Comma) {
                vars.push(None);
            } else {
                vars.push(Some(self.parse_identifier()));
            }
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::RBracket);
        
        self.expect(TokenKind::RParen);
        let body = self.parse_statement();
        Statement::new(StatementKind::Foreach {
            array: array_expr, vars, body: Box::new(body),
        }, self.span_from(start))
    }

    fn parse_while_statement(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwWhile);
        self.expect(TokenKind::LParen);
        let condition = self.parse_expression();
        self.expect(TokenKind::RParen);
        let body = self.parse_statement();
        Statement::new(StatementKind::While { condition, body: Box::new(body) }, self.span_from(start))
    }

    fn parse_do_while_statement(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwDo);
        let body = self.parse_statement();
        self.expect(TokenKind::KwWhile);
        self.expect(TokenKind::LParen);
        let condition = self.parse_expression();
        self.expect(TokenKind::RParen);
        self.expect(TokenKind::Semicolon);
        Statement::new(StatementKind::DoWhile { body: Box::new(body), condition }, self.span_from(start))
    }

    fn parse_repeat_statement(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwRepeat);
        self.expect(TokenKind::LParen);
        let count = self.parse_expression();
        self.expect(TokenKind::RParen);
        let body = self.parse_statement();
        Statement::new(StatementKind::Repeat { count, body: Box::new(body) }, self.span_from(start))
    }

    pub(super) fn parse_event_control(&mut self) -> EventControl {
        self.expect(TokenKind::At);
        if self.eat(TokenKind::Star).is_some() {
            return EventControl::Star;
        }
        if self.eat(TokenKind::LParen).is_some() {
            if self.eat(TokenKind::Star).is_some() {
                self.expect(TokenKind::RParen);
                return EventControl::ParenStar;
            }
            let mut events = Vec::new();
            loop {
                let estart = self.current().span.start;
                let edge = match self.current_kind() {
                    TokenKind::KwPosedge => { self.bump(); Some(Edge::Posedge) }
                    TokenKind::KwNegedge => { self.bump(); Some(Edge::Negedge) }
                    TokenKind::KwEdge => { self.bump(); Some(Edge::Edge) }
                    _ => None,
                };
                let expr = self.parse_expression();
                let iff = if self.eat(TokenKind::KwIff).is_some() {
                    Some(self.parse_expression())
                } else { None };
                events.push(EventExpr { edge, expr, iff, span: self.span_from(estart) });
                if self.eat(TokenKind::KwOr).is_some() || self.eat(TokenKind::Comma).is_some() {
                    continue;
                }
                break;
            }
            self.expect(TokenKind::RParen);
            EventControl::EventExpr(events)
        } else {
            let expr = self.parse_hierarchical_identifier_expr();
            EventControl::HierIdentifier(expr)
        }
    }

    pub(super) fn parse_assertion_statement(&mut self) -> AssertionStatement {
        let start = self.current().span.start;
        let kind = match self.bump().kind {
            TokenKind::KwAssume => AssertionKind::Assume,
            TokenKind::KwCover => AssertionKind::Cover,
            _ => AssertionKind::Assert,
        };
        // Handle `assert final` and `assert #0`
        self.eat(TokenKind::KwFinal);
        if self.at(TokenKind::Hash) {
            self.bump();
            // Skip delay value (could be `#0` or `#(0)`)
            if self.at(TokenKind::LParen) {
                let mut d = 1; self.bump();
                while !self.at(TokenKind::Eof) && d > 0 {
                    match self.current_kind() { TokenKind::LParen => d += 1, TokenKind::RParen => d -= 1, _ => {} }
                    self.bump();
                }
            } else { self.bump(); }
        }
        let _is_property = self.eat(TokenKind::KwProperty).is_some();
        self.expect(TokenKind::LParen);
        // For property expressions starting with a clocking event `@(...)`,
        // skip the whole assertion (we don't model SVA semantics).
        if self.at(TokenKind::At) {
            let mut depth = 1i32;
            while !self.at(TokenKind::Eof) && depth > 0 {
                match self.current_kind() {
                    TokenKind::LParen => depth += 1,
                    TokenKind::RParen => { depth -= 1; if depth == 0 { break; } }
                    _ => {}
                }
                self.bump();
            }
            self.expect(TokenKind::RParen);
            // Skip optional action and else action
            if !self.at(TokenKind::Semicolon) && !self.at(TokenKind::KwElse) {
                let _ = self.parse_statement_skip();
            }
            if self.eat(TokenKind::KwElse).is_some() {
                let _ = self.parse_statement_skip();
            }
            self.eat(TokenKind::Semicolon);
            let s0 = self.current().span.start;
            let dummy = Expression::new(ExprKind::Number(crate::ast::expr::NumberLiteral::Integer { size: None, signed: false, base: crate::ast::expr::NumberBase::Decimal, value: "1".to_string(), cached_val: std::cell::Cell::new(None) }), self.span_from(s0));
            return AssertionStatement { kind, expr: dummy, action: None, else_action: None, span: self.span_from(start) };
        }
        let expr = self.parse_expression();
        self.expect(TokenKind::RParen);
        let action = if !self.at(TokenKind::Semicolon) && !self.at(TokenKind::KwElse) {
            Some(Box::new(self.parse_statement()))
        } else {
            if self.at(TokenKind::Semicolon) { self.bump(); }
            None
        };
        let else_action = if self.eat(TokenKind::KwElse).is_some() {
            Some(Box::new(self.parse_statement()))
        } else { None };
        AssertionStatement { kind, expr, action, else_action, span: self.span_from(start) }
    }

    /// `randcase { weight : statement }+ endcase`
    /// Lowered to `if (w0 != 0) s0 else if (w1 != 0) s1 else ...`.
    fn parse_randcase(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwRandcase);
        let mut items: Vec<(Expression, Statement)> = Vec::new();
        while !self.at(TokenKind::KwEndcase) && !self.at(TokenKind::Eof) {
            let w = self.parse_expression();
            self.expect(TokenKind::Colon);
            let s = self.parse_statement();
            items.push((w, s));
        }
        self.expect(TokenKind::KwEndcase);
        let span = self.span_from(start);
        // Build chain from the back.
        let mut acc: Option<Statement> = None;
        for (w, s) in items.into_iter().rev() {
            let zero = Expression::new(ExprKind::Number(NumberLiteral::Integer {
                size: None, signed: true, base: NumberBase::Decimal,
                value: "0".into(), cached_val: Cell::new(None),
            }), w.span);
            let cond = Expression::new(ExprKind::Binary {
                op: BinaryOp::Neq, left: Box::new(w.clone()), right: Box::new(zero),
            }, w.span);
            acc = Some(Statement::new(StatementKind::If {
                unique_priority: None,
                condition: cond,
                then_stmt: Box::new(s),
                else_stmt: acc.map(Box::new),
            }, span));
        }
        acc.unwrap_or(Statement::new(StatementKind::Null, span))
    }

    /// `randsequence ( name ) production_list endsequence`.
    /// Lowered by recursively expanding `name`. Productions are kept in a map.
    fn parse_randsequence(&mut self) -> Statement {
        let start = self.current().span.start;
        self.expect(TokenKind::KwRandsequence);
        let main_name = if self.eat(TokenKind::LParen).is_some() {
            let id = self.parse_identifier();
            self.expect(TokenKind::RParen);
            id.name
        } else { "main".to_string() };

        let mut prods: HashMap<String, (Vec<(DataType, String)>, RsAlt)> = HashMap::new();
        let mut first_name: Option<String> = None;
        while !self.at(TokenKind::KwEndsequence) && !self.at(TokenKind::Eof) {
            // production: [data_type] name [( param_list )] [: production_item] ;
            // Skip optional return type.
            if self.is_data_type_keyword() && self.peek_kind() == TokenKind::Identifier {
                let _ = self.parse_data_type();
            } else if self.at(TokenKind::KwVoid) {
                self.bump();
            }
            if !self.at(TokenKind::Identifier) {
                // Skip unknown token to avoid infinite loop
                self.bump();
                continue;
            }
            let pname = self.parse_identifier().name;
            // Parameter list: `( [ref] data_type name, ... )`. Captured so
            // call-sites can bind args to fresh locals before executing the
            // body (IEEE 1800 §18.17.7).
            let mut params: Vec<(DataType, String)> = Vec::new();
            if self.eat(TokenKind::LParen).is_some() {
                while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                    // Optional direction qualifier
                    if matches!(self.current_kind(), TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef) {
                        self.bump();
                    }
                    let dt = if self.is_data_type_keyword() { self.parse_data_type() }
                        else {
                            // Fallback: treat as int.
                            DataType::IntegerAtom {
                                kind: crate::ast::types::IntegerAtomType::Int,
                                signing: None,
                                span: self.current().span,
                            }
                        };
                    if !self.at(TokenKind::Identifier) { self.bump(); continue; }
                    let pn = self.parse_identifier().name;
                    params.push((dt, pn));
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::RParen);
            }
            let alt = if self.eat(TokenKind::Colon).is_some() {
                let a = self.parse_rs_alt();
                a
            } else {
                RsAlt { alts: vec![(RsSeq { items: Vec::new() }, None)] }
            };
            self.eat(TokenKind::Semicolon);
            if first_name.is_none() { first_name = Some(pname.clone()); }
            prods.insert(pname, (params, alt));
        }
        self.expect(TokenKind::KwEndsequence);
        let span = self.span_from(start);
        let main = if prods.contains_key(&main_name) { main_name }
                   else if let Some(f) = first_name { f }
                   else { return Statement::new(StatementKind::Null, span); };
        let mut depth = 0u32;
        let body = expand_rs_ref(&prods, &main, &mut depth, span);
        // Wrap in `repeat (1) ...` so a `break` inside a production aborts the
        // sequence without leaking the break_flag out to enclosing code.
        let one = Expression::new(ExprKind::Number(NumberLiteral::Integer {
            size: None, signed: true, base: NumberBase::Decimal,
            value: "1".into(), cached_val: Cell::new(None),
        }), span);
        Statement::new(StatementKind::Repeat { count: one, body: Box::new(body) }, span)
    }

    /// rs_alt ::= rs_seq ('|' rs_seq)* with optional `:= weight` after each seq.
    fn parse_rs_alt(&mut self) -> RsAlt {
        let mut alts = Vec::new();
        loop {
            let seq = self.parse_rs_seq();
            let weight = if self.eat(TokenKind::ColonAssign).is_some() {
                Some(self.parse_expression())
            } else { None };
            alts.push((seq, weight));
            if self.eat(TokenKind::BitOr).is_none() { break; }
        }
        RsAlt { alts }
    }

    fn parse_rs_seq(&mut self) -> RsSeq {
        let mut items = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::BitOr | TokenKind::Semicolon | TokenKind::KwEndsequence
                | TokenKind::ColonAssign | TokenKind::Eof | TokenKind::RParen
                | TokenKind::RBrace | TokenKind::KwEndcase | TokenKind::KwElse => break,
                _ => {}
            }
            let item = self.parse_rs_prod();
            items.push(item);
        }
        RsSeq { items }
    }

    fn parse_rs_prod(&mut self) -> RsProd {
        match self.current_kind() {
            TokenKind::LBrace => {
                // Code block: `{ statement_or_null* }`. Lower to seq block.
                // Per IEEE 1800 §18.17.6, `return` inside a randsequence
                // action block exits the production and proceeds to the
                // next one — NOT returning from the enclosing subroutine.
                // Rewrite bare `return` as `RsReturn` and wrap the block
                // in an `RsAction` that catches it at the production
                // boundary. `break` inside the block keeps its usual
                // meaning (abort the whole sequence).
                let start = self.current().span.start;
                self.bump();
                let mut stmts = Vec::new();
                while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                    stmts.push(self.parse_statement());
                }
                self.expect(TokenKind::RBrace);
                for s in &mut stmts { rs_rewrite_return_as_rsreturn(s); }
                let span = self.span_from(start);
                let inner = Statement::new(StatementKind::SeqBlock {
                    name: None, stmts,
                }, span);
                RsProd::Block(Statement::new(
                    StatementKind::RsAction { body: Box::new(inner) },
                    span,
                ))
            }
            TokenKind::KwIf => {
                self.bump();
                self.expect(TokenKind::LParen);
                let cond = self.parse_expression();
                self.expect(TokenKind::RParen);
                let then_a = self.parse_rs_alt();
                let else_a = if self.eat(TokenKind::KwElse).is_some() {
                    Some(Box::new(self.parse_rs_alt()))
                } else { None };
                RsProd::If(cond, Box::new(then_a), else_a)
            }
            TokenKind::KwCase => {
                self.bump();
                self.expect(TokenKind::LParen);
                let head = self.parse_expression();
                self.expect(TokenKind::RParen);
                let mut items: Vec<(Vec<Expression>, Box<RsAlt>)> = Vec::new();
                let mut default: Option<Box<RsAlt>> = None;
                while !self.at(TokenKind::KwEndcase) && !self.at(TokenKind::Eof) {
                    if self.eat(TokenKind::KwDefault).is_some() {
                        self.eat(TokenKind::Colon);
                        let a = self.parse_rs_alt();
                        self.eat(TokenKind::Semicolon);
                        default = Some(Box::new(a));
                    } else {
                        let mut pats = Vec::new();
                        loop {
                            pats.push(self.parse_expression());
                            if self.eat(TokenKind::Comma).is_none() { break; }
                        }
                        self.expect(TokenKind::Colon);
                        let a = self.parse_rs_alt();
                        self.eat(TokenKind::Semicolon);
                        items.push((pats, Box::new(a)));
                    }
                }
                self.expect(TokenKind::KwEndcase);
                RsProd::Case(head, items, default)
            }
            TokenKind::KwRepeat => {
                self.bump();
                self.expect(TokenKind::LParen);
                let n = self.parse_expression();
                self.expect(TokenKind::RParen);
                let body = self.parse_rs_alt();
                RsProd::Repeat(n, Box::new(body))
            }
            TokenKind::KwRand => {
                self.bump();
                self.eat(TokenKind::KwJoin);
                if self.at(TokenKind::LParen) {
                    let mut depth = 0i32;
                    loop {
                        match self.current_kind() {
                            TokenKind::LParen => { depth += 1; self.bump(); }
                            TokenKind::RParen => { depth -= 1; self.bump(); if depth == 0 { break; } }
                            TokenKind::Eof => break,
                            _ => { self.bump(); }
                        }
                    }
                }
                let body = self.parse_rs_seq();
                RsProd::RandJoin(body.items)
            }
            TokenKind::KwBreak => { self.bump(); RsProd::Break }
            TokenKind::KwReturn => {
                self.bump();
                if !self.at(TokenKind::Semicolon) && !self.at(TokenKind::BitOr) {
                    let _ = self.parse_expression();
                }
                RsProd::Return
            }
            TokenKind::Identifier => {
                let id = self.parse_identifier();
                let mut args: Vec<Expression> = Vec::new();
                if self.eat(TokenKind::LParen).is_some() {
                    while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                        args.push(self.parse_expression());
                        if self.eat(TokenKind::Comma).is_none() { break; }
                    }
                    self.expect(TokenKind::RParen);
                }
                RsProd::Ref(id.name, args)
            }
            _ => {
                self.bump();
                RsProd::Break
            }
        }
    }

    fn parse_statement_skip(&mut self) -> () {
        // Skip a single statement, balancing braces/parens. Used when we don't
        // care about content (e.g. action of an SVA assertion we don't model).
        let mut depth = 0i32;
        let mut block_depth = 0i32;
        while !self.at(TokenKind::Eof) {
            match self.current_kind() {
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => { depth += 1; self.bump(); }
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if depth > 0 { depth -= 1; self.bump(); } else { break; }
                }
                TokenKind::KwBegin => { block_depth += 1; self.bump(); }
                TokenKind::KwEnd => {
                    if block_depth > 0 { block_depth -= 1; self.bump(); if block_depth == 0 && depth == 0 { break; } } else { break; }
                }
                TokenKind::Semicolon => {
                    self.bump();
                    if depth == 0 && block_depth == 0 { break; }
                }
                _ => { self.bump(); }
            }
        }
    }
}

// ============================================================================
// randsequence lowering helpers
// ============================================================================

#[derive(Clone)]
struct RsAlt {
    alts: Vec<(RsSeq, Option<Expression>)>,
}

#[derive(Clone)]
struct RsSeq {
    items: Vec<RsProd>,
}

#[derive(Clone)]
enum RsProd {
    Block(Statement),
    Ref(String, Vec<Expression>),
    If(Expression, Box<RsAlt>, Option<Box<RsAlt>>),
    Case(Expression, Vec<(Vec<Expression>, Box<RsAlt>)>, Option<Box<RsAlt>>),
    Repeat(Expression, Box<RsAlt>),
    RandJoin(Vec<RsProd>),
    Break,
    Return,
}

/// Recursively rewrite `return;` inside a randsequence action block into
/// `break` so it exits just the production rather than the enclosing
/// subroutine. Stops at nested loops (where `break` would already be
/// captured), so only bare returns in the straight-line body are touched.
fn rs_rewrite_return_as_rsreturn(s: &mut Statement) {
    match &mut s.kind {
        StatementKind::Return(None) => { s.kind = StatementKind::RsReturn; }
        StatementKind::SeqBlock { stmts, .. } => {
            for c in stmts { rs_rewrite_return_as_rsreturn(c); }
        }
        StatementKind::If { then_stmt, else_stmt, .. } => {
            rs_rewrite_return_as_rsreturn(then_stmt);
            if let Some(e) = else_stmt { rs_rewrite_return_as_rsreturn(e); }
        }
        StatementKind::Case { items, .. } => {
            for it in items { rs_rewrite_return_as_rsreturn(&mut it.stmt); }
        }
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            rs_rewrite_return_as_rsreturn(stmt);
        }
        _ => {}
    }
}

fn is_zero_const(e: &Expression) -> bool {
    if let ExprKind::Number(NumberLiteral::Integer { value, .. }) = &e.kind {
        let v = value.trim();
        return v == "0" || v.parse::<i64>().ok() == Some(0);
    }
    false
}

type ProdMap = HashMap<String, (Vec<(DataType, String)>, RsAlt)>;

fn expand_alt(prods: &ProdMap, alt: &RsAlt, depth: &mut u32, span: crate::ast::Span) -> Statement {
    // Pick first alternative whose weight isn't a constant zero.
    for (seq, w) in &alt.alts {
        if let Some(e) = w { if is_zero_const(e) { continue; } }
        return expand_seq(prods, seq, depth, span);
    }
    if let Some((seq, _)) = alt.alts.first() {
        return expand_seq(prods, seq, depth, span);
    }
    Statement::new(StatementKind::Null, span)
}

fn expand_seq(prods: &ProdMap, seq: &RsSeq, depth: &mut u32, span: crate::ast::Span) -> Statement {
    let stmts: Vec<Statement> = seq.items.iter().map(|p| expand_prod(prods, p, depth, span)).collect();
    Statement::new(StatementKind::SeqBlock { name: None, stmts }, span)
}

fn expand_prod(prods: &ProdMap, p: &RsProd, depth: &mut u32, span: crate::ast::Span) -> Statement {
    if *depth > 64 {
        return Statement::new(StatementKind::Null, span);
    }
    match p {
        RsProd::Block(s) => s.clone(),
        RsProd::Ref(name, args) => {
            let body = expand_rs_ref(prods, name, depth, span);
            let params = prods.get(name).map(|(p, _)| p.clone()).unwrap_or_default();
            if params.is_empty() && args.is_empty() { return body; }
            // Bind call args to fresh local variables inside a begin/end
            // wrapper so the production body sees them.
            let mut stmts: Vec<Statement> = Vec::new();
            for ((dt, pname), arg) in params.iter().zip(args.iter()) {
                let declarator = VarDeclarator {
                    name: crate::ast::Identifier { name: pname.clone(), span },
                    dimensions: Vec::new(),
                    init: Some(arg.clone()),
                    span,
                };
                stmts.push(Statement::new(
                    StatementKind::VarDecl {
                        data_type: dt.clone(),
                        lifetime: Some(Lifetime::Automatic),
                        declarators: vec![declarator],
                    },
                    span,
                ));
            }
            stmts.push(body);
            Statement::new(StatementKind::SeqBlock { name: None, stmts }, span)
        }
        RsProd::If(cond, then_a, else_a) => {
            *depth += 1;
            let then_s = expand_alt(prods, then_a, depth, span);
            let else_s = else_a.as_ref().map(|a| Box::new(expand_alt(prods, a, depth, span)));
            *depth -= 1;
            Statement::new(StatementKind::If {
                unique_priority: None,
                condition: cond.clone(),
                then_stmt: Box::new(then_s),
                else_stmt: else_s,
            }, span)
        }
        RsProd::Case(head, items, default) => {
            *depth += 1;
            let mut case_items: Vec<CaseItem> = items.iter().map(|(pats, alt)| {
                CaseItem {
                    patterns: pats.clone(),
                    is_default: false,
                    stmt: expand_alt(prods, alt, depth, span),
                    span,
                }
            }).collect();
            if let Some(d) = default {
                case_items.push(CaseItem {
                    patterns: Vec::new(),
                    is_default: true,
                    stmt: expand_alt(prods, d, depth, span),
                    span,
                });
            }
            *depth -= 1;
            Statement::new(StatementKind::Case {
                unique_priority: None,
                kind: CaseKind::Case,
                expr: head.clone(),
                items: case_items,
            }, span)
        }
        RsProd::Repeat(n, body) => {
            *depth += 1;
            let b = expand_alt(prods, body, depth, span);
            *depth -= 1;
            Statement::new(StatementKind::Repeat { count: n.clone(), body: Box::new(b) }, span)
        }
        RsProd::RandJoin(items) => {
            // Treat as sequential for now.
            let stmts: Vec<Statement> = items.iter().map(|p| expand_prod(prods, p, depth, span)).collect();
            Statement::new(StatementKind::SeqBlock { name: None, stmts }, span)
        }
        RsProd::Break => Statement::new(StatementKind::Break, span),
        RsProd::Return => Statement::new(StatementKind::Return(None), span),
    }
}

fn expand_rs_ref(prods: &ProdMap, name: &str, depth: &mut u32, span: crate::ast::Span) -> Statement {
    if *depth > 64 {
        return Statement::new(StatementKind::Null, span);
    }
    if let Some((_params, alt)) = prods.get(name) {
        *depth += 1;
        let s = expand_alt(prods, alt, depth, span);
        *depth -= 1;
        s
    } else {
        Statement::new(StatementKind::Null, span)
    }
}
