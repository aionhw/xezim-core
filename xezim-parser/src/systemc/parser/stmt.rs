//! Statements, including the SystemC process-registration statements of a
//! module constructor (IEEE 1666-2023 §5.2.9–§5.2.16).

use super::decl::{Ctx, Decl, UsingResult, is_builtin_type_keyword};
use super::expr::PREC_SHIFT;
use super::*;

impl Parser {
    pub(super) fn parse_block(&mut self) -> PResult<Block> {
        let start = self.expect("{")?;
        let stmts = self.nested(|p| {
            let mut stmts = Vec::new();
            while !p.at("}") && !p.at_eof() {
                match p.parse_stmt() {
                    Ok(s) => stmts.push(s),
                    Err(Fail) => p.recover(),
                }
            }
            Ok(stmts)
        })?;
        self.expect("}")?;
        Ok(Block {
            stmts,
            span: self.span_from(start),
        })
    }

    pub(super) fn parse_stmt(&mut self) -> PResult<Stmt> {
        self.skip_attributes();
        let start = self.cur_span();
        let t = self.peek().clone();
        match t.kind {
            ScTokenKind::Punct if t.text == "{" => return self.parse_block().map(Stmt::Block),
            ScTokenKind::Punct if t.text == ";" => {
                self.bump();
                return Ok(Stmt::Empty(start));
            }
            ScTokenKind::Keyword => match t.text.as_str() {
                "if" => return self.parse_if(),
                "switch" => return self.parse_switch(),
                "for" => return self.parse_for(),
                "while" => {
                    self.bump();
                    self.expect("(")?;
                    let cond = self.nested(|p| p.parse_condition())?;
                    self.expect(")")?;
                    let body = self.parse_stmt()?;
                    return Ok(Stmt::While {
                        cond: Box::new(cond),
                        body: Box::new(body),
                        span: self.span_from(start),
                    });
                }
                "do" => {
                    self.bump();
                    let body = self.parse_stmt()?;
                    if !self.eat_kw("while") {
                        return Err(self.err_expected("'while'"));
                    }
                    self.expect("(")?;
                    let cond = self.nested(|p| p.parse_expr())?;
                    self.expect(")")?;
                    self.expect(";")?;
                    return Ok(Stmt::DoWhile {
                        body: Box::new(body),
                        cond,
                        span: self.span_from(start),
                    });
                }
                "break" | "continue" => {
                    self.bump();
                    self.expect(";")?;
                    let span = self.span_from(start);
                    return Ok(if t.text == "break" {
                        Stmt::Break(span)
                    } else {
                        Stmt::Continue(span)
                    });
                }
                "return" => {
                    self.bump();
                    let value = if self.at(";") {
                        None
                    } else if self.at("{") {
                        Some(self.parse_init_list_expr()?)
                    } else {
                        Some(self.parse_expr()?)
                    };
                    self.expect(";")?;
                    return Ok(Stmt::Return(value, self.span_from(start)));
                }
                "try" => return self.parse_try(),
                "case" | "default" => {
                    return Err(self.error(format!("'{}' label outside a switch", t.text), start));
                }
                "goto" => return Err(self.error("'goto' is not supported", start)),
                "static_assert" => {
                    return self
                        .parse_static_assert()
                        .map(|s| Stmt::StaticAssert(Box::new(s)));
                }
                "typedef" => return self.parse_typedef().map(Stmt::Typedef),
                "using" => {
                    return Ok(match self.parse_using()? {
                        UsingResult::Using(u) => Stmt::Using(u),
                        UsingResult::Alias(t) => Stmt::Typedef(t),
                    });
                }
                _ => {}
            },
            ScTokenKind::Ident => {
                if let Some(s) = self.try_systemc_stmt()? {
                    return Ok(s);
                }
                if self.nth(1).is_punct(":") {
                    let label = self.expect_ident()?;
                    self.bump(); // :
                    let stmt = self.parse_stmt()?;
                    return Ok(Stmt::Labeled {
                        label,
                        stmt: Box::new(stmt),
                        span: self.span_from(start),
                    });
                }
            }
            _ => {}
        }
        if self.is_declaration_start() {
            return Ok(match self.parse_simple_decl(Ctx::Block)? {
                Decl::Var(v) => Stmt::Decl(v),
                Decl::Class(c) => Stmt::Class(Box::new(c)),
                Decl::Enum(e) => Stmt::Enum(e),
                Decl::Typedef(t) => Stmt::Typedef(t),
                Decl::Function(f) => Stmt::Empty(f.span),
                Decl::Forward { span, .. } | Decl::Empty(span) => Stmt::Empty(span),
            });
        }
        let e = self.parse_expr()?;
        self.expect(";")?;
        Ok(Stmt::Expr(e))
    }

    /// The SystemC registration statements, recognized by name.
    fn try_systemc_stmt(&mut self) -> PResult<Option<Stmt>> {
        let start = self.cur_span();
        let name = self.peek().text.clone();
        let next = self.nth(1).clone();
        let stmt = match name.as_str() {
            "SC_METHOD" | "SC_THREAD" | "SC_CTHREAD" if next.is_punct("(") => {
                let kind = match name.as_str() {
                    "SC_METHOD" => ProcessKind::Method,
                    "SC_THREAD" => ProcessKind::Thread,
                    _ => ProcessKind::CThread,
                };
                self.bump();
                self.bump();
                let func = self.expect_ident()?;
                let clock = if kind == ProcessKind::CThread {
                    self.expect(",")?;
                    Some(self.nested(|p| p.parse_assign())?)
                } else {
                    None
                };
                self.expect(")")?;
                // The macros expand to a `{ … }` block (SystemC 2.3), so the
                // `;` after them is optional.
                self.eat(";");
                Stmt::ScProcess {
                    kind,
                    func,
                    clock,
                    span: self.span_from(start),
                }
            }
            "sensitive" | "sensitive_pos" | "sensitive_neg"
                if next.is_punct("<<") || next.is_punct("(") =>
            {
                let edge = match name.as_str() {
                    "sensitive" => SensitivityEdge::Any,
                    "sensitive_pos" => SensitivityEdge::Pos,
                    _ => SensitivityEdge::Neg,
                };
                self.bump();
                let mut items = Vec::new();
                if self.at("(") {
                    items = self.parse_call_args()?;
                } else {
                    // Each `<<` operand binds tighter than the shift.
                    while self.eat("<<") {
                        items.push(self.parse_binary(PREC_SHIFT)?);
                    }
                }
                self.expect(";")?;
                Stmt::Sensitive {
                    edge,
                    items,
                    span: self.span_from(start),
                }
            }
            // `SC_FORK p1, p2, … SC_JOIN` (§5.6); a trailing comma is usual.
            "SC_FORK" => {
                self.bump();
                let mut spawns = Vec::new();
                let at_join =
                    |p: &Self| p.peek().is_ident("SC_JOIN") || p.peek().is_ident("SC_CJOIN");
                let clocked = loop {
                    if at_join(self) {
                        break self.bump().text == "SC_CJOIN";
                    }
                    spawns.push(self.nested(|p| p.parse_assign())?);
                    if !self.eat(",") && !at_join(self) {
                        return Err(self.err_expected("',' or 'SC_JOIN'"));
                    }
                };
                self.eat(";");
                Stmt::ScFork {
                    spawns,
                    clocked,
                    span: self.span_from(start),
                }
            }
            "dont_initialize" if next.is_punct("(") && self.nth(2).is_punct(")") => {
                self.bump();
                self.bump();
                self.bump();
                self.expect(";")?;
                Stmt::DontInitialize(self.span_from(start))
            }
            "reset_signal_is" | "async_reset_signal_is" if next.is_punct("(") => {
                self.bump();
                let args = self.parse_call_args()?;
                self.expect(";")?;
                let span = self.span_from(start);
                let [signal, level]: [Expr; 2] = args.try_into().map_err(|_| {
                    self.error(format!("{} takes a signal and a level", name), span)
                })?;
                Stmt::ResetSignalIs {
                    is_async: name == "async_reset_signal_is",
                    signal,
                    level,
                    span,
                }
            }
            _ => return Ok(None),
        };
        Ok(Some(stmt))
    }

    /// Whether the statement at the cursor is a declaration. C++ resolves
    /// this with full name lookup (§9.8); here a statement is a declaration
    /// when it starts with a declaration keyword, or with a name followed by
    /// a declarator: `T x;`, `T* p = …`, `T x(…)`, `T x{…}`.
    pub(super) fn is_declaration_start(&mut self) -> bool {
        let t = self.peek().clone();
        if t.kind == ScTokenKind::Keyword {
            if is_builtin_type_keyword(&t) {
                // `int(x)` is a functional cast.
                return !(self.nth(1).is_punct("(") || self.nth(1).is_punct("{"));
            }
            return matches!(
                t.text.as_str(),
                "const"
                    | "volatile"
                    | "static"
                    | "extern"
                    | "mutable"
                    | "inline"
                    | "register"
                    | "thread_local"
                    | "constexpr"
                    | "auto"
                    | "typename"
                    | "class"
                    | "struct"
                    | "union"
                    | "enum"
                    | "decltype"
            );
        }
        if t.kind != ScTokenKind::Ident && !t.is_punct("::") {
            return false;
        }
        let cp = self.checkpoint();
        let result = self.looks_like_declarator_follows();
        self.restore(cp);
        result
    }

    fn looks_like_declarator_follows(&mut self) -> bool {
        if self.parse_qualified_name(true).is_err() {
            return false;
        }
        while self.eat_kw("const") || self.eat_kw("volatile") {}
        let _ = self.parse_ptr_ops();
        if !self.at_ident() {
            return false;
        }
        if self.peek().is_ident("SC_NAMED") {
            return true;
        }
        let after = self.nth(1);
        after.kind == ScTokenKind::Punct
            && matches!(after.text.as_str(), ";" | "=" | "," | "[" | "{" | "(")
    }

    /// The condition of `if`/`while`/`switch`/`for`.
    fn parse_condition(&mut self) -> PResult<Condition> {
        if self.is_declaration_start() {
            match self.parse_simple_decl(Ctx::Condition)? {
                Decl::Var(v) => Ok(Condition::Decl(v)),
                _ => {
                    let span = self.cur_span();
                    Err(self.error("expected a variable declaration in condition", span))
                }
            }
        } else {
            Ok(Condition::Expr(self.parse_expr()?))
        }
    }

    /// `[init-statement ;] condition` (C++17 §9.4).
    fn parse_condition_with_init(&mut self) -> PResult<(Option<Box<Stmt>>, Condition)> {
        let first = self.parse_condition()?;
        if self.eat(";") {
            let init = match first {
                Condition::Expr(e) => Stmt::Expr(e),
                Condition::Decl(d) => Stmt::Decl(d),
            };
            let cond = self.parse_condition()?;
            return Ok((Some(Box::new(init)), cond));
        }
        Ok((None, first))
    }

    fn parse_if(&mut self) -> PResult<Stmt> {
        let start = self.cur_span();
        self.bump(); // if
        let constexpr = self.eat_kw("constexpr");
        self.expect("(")?;
        let (init, cond) = self.nested(|p| p.parse_condition_with_init())?;
        self.expect(")")?;
        let then_branch = self.parse_stmt()?;
        let else_branch = if self.eat_kw("else") {
            Some(Box::new(self.parse_stmt()?))
        } else {
            None
        };
        Ok(Stmt::If {
            constexpr,
            init,
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch,
            span: self.span_from(start),
        })
    }

    fn at_switch_label(&self) -> bool {
        self.at_kw("case") || (self.at_kw("default") && self.nth(1).is_punct(":"))
    }

    fn parse_switch(&mut self) -> PResult<Stmt> {
        let start = self.cur_span();
        self.bump(); // switch
        self.expect("(")?;
        let (init, cond) = self.nested(|p| p.parse_condition_with_init())?;
        self.expect(")")?;
        self.expect("{")?;
        let arms = self.nested(|p| {
            let mut arms = Vec::new();
            while !p.at("}") && !p.at_eof() {
                let arm_start = p.cur_span();
                let mut labels = Vec::new();
                while p.at_switch_label() {
                    if p.eat_kw("case") {
                        let e = p.parse_conditional()?;
                        p.expect(":")?;
                        labels.push(Some(e));
                    } else {
                        p.bump();
                        p.bump();
                        labels.push(None);
                    }
                }
                if labels.is_empty() {
                    p.err_expected("'case' or 'default'");
                    p.recover();
                    continue;
                }
                let mut body = Vec::new();
                while !p.at("}") && !p.at_eof() && !p.at_switch_label() {
                    match p.parse_stmt() {
                        Ok(s) => body.push(s),
                        Err(Fail) => p.recover(),
                    }
                }
                arms.push(SwitchArm {
                    labels,
                    body,
                    span: p.span_from(arm_start),
                });
            }
            Ok(arms)
        })?;
        self.expect("}")?;
        Ok(Stmt::Switch {
            init,
            cond: Box::new(cond),
            arms,
            span: self.span_from(start),
        })
    }

    fn parse_for(&mut self) -> PResult<Stmt> {
        let start = self.cur_span();
        self.bump(); // for
        self.expect("(")?;
        let saved = self.no_gt;
        self.no_gt = 0;
        let r = self.parse_for_rest(start);
        self.no_gt = saved;
        r
    }

    fn parse_for_rest(&mut self, start: ScSpan) -> PResult<Stmt> {
        let init = if self.eat(";") {
            None
        } else if self.is_declaration_start() {
            if let Some(decl) = self.try_range_decl() {
                self.bump(); // :
                let range = if self.at("{") {
                    self.parse_init_list_expr()?
                } else {
                    self.parse_expr()?
                };
                self.expect(")")?;
                let body = self.parse_stmt()?;
                return Ok(Stmt::RangeFor {
                    decl: Box::new(decl),
                    range,
                    body: Box::new(body),
                    span: self.span_from(start),
                });
            }
            Some(Box::new(match self.parse_simple_decl(Ctx::Block)? {
                Decl::Var(v) => Stmt::Decl(v),
                _ => {
                    let span = self.prev_span();
                    return Err(self.error("expected a variable declaration in for-init", span));
                }
            }))
        } else {
            let e = self.parse_expr()?;
            self.expect(";")?;
            Some(Box::new(Stmt::Expr(e)))
        };
        let cond = if self.at(";") {
            None
        } else {
            Some(Box::new(self.parse_condition()?))
        };
        self.expect(";")?;
        let step = if self.at(")") {
            None
        } else {
            Some(self.parse_expr()?)
        };
        self.expect(")")?;
        let body = self.parse_stmt()?;
        Ok(Stmt::For {
            init,
            cond,
            step,
            body: Box::new(body),
            span: self.span_from(start),
        })
    }

    /// `T x :` of a range-based for; leaves the cursor on the `:`.
    fn try_range_decl(&mut self) -> Option<Param> {
        let cp = self.checkpoint();
        let start = self.cur_span();
        let r = (|| {
            let (_, mut ty) = self.parse_decl_specifiers().ok()?;
            ty.ptr_ops = self.parse_ptr_ops();
            let name = self.expect_ident().ok()?;
            (self.at(":") && !self.at("::")).then_some((ty, name))
        })();
        match r {
            Some((ty, name)) => Some(Param {
                ty,
                name: Some(name),
                array_dims: Vec::new(),
                default: None,
                span: self.span_from(start),
            }),
            None => {
                self.restore(cp);
                None
            }
        }
    }

    fn parse_try(&mut self) -> PResult<Stmt> {
        let start = self.cur_span();
        self.bump(); // try
        let body = self.parse_block()?;
        let mut handlers = Vec::new();
        while self.eat_kw("catch") {
            self.expect("(")?;
            let param = if self.eat("...") {
                None
            } else {
                Some(self.nested(|p| p.parse_param())?)
            };
            self.expect(")")?;
            let body = self.parse_block()?;
            handlers.push(CatchClause { param, body });
        }
        if handlers.is_empty() {
            return Err(self.err_expected("'catch'"));
        }
        Ok(Stmt::Try {
            body,
            handlers,
            span: self.span_from(start),
        })
    }
}
