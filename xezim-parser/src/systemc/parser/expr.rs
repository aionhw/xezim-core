//! Expressions (C++17 §8), qualified names and template argument lists.

use super::decl::is_builtin_type_keyword;
use super::*;
use crate::systemc::preprocess::parse_int;

/// Binding power of the shift operators; `sensitive << a << b` parses each
/// operand just above it.
pub(super) const PREC_SHIFT: u8 = 9;

fn decode_escapes(body: &str, out: &mut String) {
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('a') => out.push('\x07'),
            Some('b') => out.push('\x08'),
            Some('f') => out.push('\x0c'),
            Some('v') => out.push('\x0b'),
            Some('x') => {
                let mut v = 0u32;
                while let Some(d) = chars.peek().and_then(|d| d.to_digit(16)) {
                    v = v.wrapping_mul(16).wrapping_add(d);
                    chars.next();
                }
                out.push(char::from_u32(v).unwrap_or('\u{fffd}'));
            }
            Some(d @ '0'..='7') => {
                let mut v = d.to_digit(8).unwrap_or(0);
                for _ in 0..2 {
                    match chars.peek().and_then(|d| d.to_digit(8)) {
                        Some(n) => {
                            v = v * 8 + n;
                            chars.next();
                        }
                        None => break,
                    }
                }
                out.push(char::from_u32(v).unwrap_or('\u{fffd}'));
            }
            Some(other) => out.push(other),
            None => out.push('\\'),
        }
    }
}

/// The value of one string literal token (prefix, quotes, raw delimiters
/// and user-defined suffix removed, escapes decoded).
fn string_value(text: &str) -> String {
    let Some(q) = text.find('"') else {
        return String::new();
    };
    let prefix = &text[..q];
    let rest = &text[q + 1..];
    let mut out = String::new();
    if prefix.ends_with('R') {
        if let Some(paren) = rest.find('(') {
            let delim = &rest[..paren];
            let close = format!("){}\"", delim);
            if let Some(end) = rest.rfind(&close) {
                out.push_str(&rest[paren + 1..end]);
            }
        }
        return out;
    }
    let end = rest.rfind('"').unwrap_or(rest.len());
    decode_escapes(&rest[..end], &mut out);
    out
}

impl Parser {
    // ---- operator precedence ---------------------------------------------

    fn binary_op(&self) -> Option<(BinaryOp, u8)> {
        let t = self.peek();
        if t.kind != ScTokenKind::Punct {
            return None;
        }
        if self.no_gt > 0 && t.text.starts_with('>') {
            return None;
        }
        use BinaryOp::*;
        Some(match t.text.as_str() {
            "||" => (LogOr, 1),
            "&&" => (LogAnd, 2),
            "|" => (BitOr, 3),
            "^" => (BitXor, 4),
            "&" => (BitAnd, 5),
            "==" => (Eq, 6),
            "!=" => (Ne, 6),
            "<=>" => (Spaceship, 7),
            "<" => (Lt, 8),
            ">" => (Gt, 8),
            "<=" => (Le, 8),
            ">=" => (Ge, 8),
            "<<" => (Shl, PREC_SHIFT),
            ">>" => (Shr, PREC_SHIFT),
            "+" => (Add, 10),
            "-" => (Sub, 10),
            "*" => (Mul, 11),
            "/" => (Div, 11),
            "%" => (Rem, 11),
            ".*" => (PtrMem, 12),
            "->*" => (ArrowPtrMem, 12),
            _ => return None,
        })
    }

    fn assign_op(&self) -> Option<AssignOp> {
        let t = self.peek();
        if t.kind != ScTokenKind::Punct {
            return None;
        }
        use AssignOp::*;
        Some(match t.text.as_str() {
            "=" => Assign,
            "*=" => Mul,
            "/=" => Div,
            "%=" => Rem,
            "+=" => Add,
            "-=" => Sub,
            "<<=" => Shl,
            ">>=" if self.no_gt == 0 => Shr,
            "&=" => And,
            "^=" => Xor,
            "|=" => Or,
            _ => return None,
        })
    }

    // ---- expression levels ----------------------------------------------

    /// expression: assignment-expressions joined by the comma operator.
    pub(super) fn parse_expr(&mut self) -> PResult<Expr> {
        let mut e = self.parse_assign()?;
        while self.at(",") {
            self.bump();
            let rhs = self.parse_assign()?;
            e = Expr {
                span: e.span.to(rhs.span),
                kind: ExprKind::Binary {
                    op: BinaryOp::Comma,
                    lhs: Box::new(e),
                    rhs: Box::new(rhs),
                },
            };
        }
        Ok(e)
    }

    pub(super) fn parse_assign(&mut self) -> PResult<Expr> {
        let start = self.cur_span();
        if self.eat_kw("throw") {
            let operand =
                if self.at(";") || self.at(")") || self.at(",") || self.at(":") || self.at("]") {
                    None
                } else {
                    Some(Box::new(self.parse_assign()?))
                };
            return Ok(Expr {
                kind: ExprKind::Throw(operand),
                span: self.span_from(start),
            });
        }
        let lhs = self.parse_conditional()?;
        if let Some(op) = self.assign_op() {
            self.bump();
            let rhs = if self.at("{") {
                self.parse_init_list_expr()?
            } else {
                self.parse_assign()?
            };
            return Ok(Expr {
                span: lhs.span.to(rhs.span),
                kind: ExprKind::Assign {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            });
        }
        Ok(lhs)
    }

    pub(super) fn parse_conditional(&mut self) -> PResult<Expr> {
        let cond = self.parse_binary(0)?;
        if !self.at("?") {
            return Ok(cond);
        }
        self.bump();
        let then_expr = self.nested(|p| p.parse_expr())?;
        self.expect(":")?;
        let else_expr = self.parse_assign()?;
        Ok(Expr {
            span: cond.span.to(else_expr.span),
            kind: ExprKind::Conditional {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            },
        })
    }

    /// Binary operators binding tighter than `min_prec` (left-associative).
    pub(super) fn parse_binary(&mut self, min_prec: u8) -> PResult<Expr> {
        let mut lhs = self.parse_unary()?;
        while let Some((op, prec)) = self.binary_op() {
            if prec <= min_prec {
                break;
            }
            self.bump();
            let rhs = self.parse_binary(prec)?;
            lhs = Expr {
                span: lhs.span.to(rhs.span),
                kind: ExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            };
        }
        Ok(lhs)
    }

    fn unary(&mut self, op: UnaryOp, start: ScSpan) -> PResult<Expr> {
        self.bump();
        let operand = self.parse_unary()?;
        Ok(Expr {
            span: start.to(operand.span),
            kind: ExprKind::Unary {
                op,
                operand: Box::new(operand),
            },
        })
    }

    fn parse_unary(&mut self) -> PResult<Expr> {
        let start = self.cur_span();
        let t = self.peek().clone();
        if t.kind == ScTokenKind::Punct {
            let op = match t.text.as_str() {
                "+" => Some(UnaryOp::Plus),
                "-" => Some(UnaryOp::Neg),
                "!" => Some(UnaryOp::Not),
                "~" => Some(UnaryOp::BitNot),
                "&" => Some(UnaryOp::AddrOf),
                "*" => Some(UnaryOp::Deref),
                "++" => Some(UnaryOp::PreInc),
                "--" => Some(UnaryOp::PreDec),
                _ => None,
            };
            if let Some(op) = op {
                return self.unary(op, start);
            }
            if t.text == "("
                && let Some(cast) = self.try_c_style_cast()?
            {
                return Ok(cast);
            }
            if t.text == "::" && (self.nth(1).is_keyword("new") || self.nth(1).is_keyword("delete"))
            {
                self.bump();
                return self.parse_unary();
            }
        }
        if t.kind == ScTokenKind::Keyword {
            match t.text.as_str() {
                "sizeof" => return self.parse_sizeof(),
                "alignof" => {
                    self.bump();
                    self.expect("(")?;
                    let ty = self.nested(|p| p.parse_type_id(false))?;
                    self.expect(")")?;
                    return Ok(Expr {
                        kind: ExprKind::AlignofType(Box::new(ty)),
                        span: self.span_from(start),
                    });
                }
                "new" => return self.parse_new(),
                "delete" => {
                    self.bump();
                    let array = self.at("[") && self.nth(1).is_punct("]");
                    if array {
                        self.bump();
                        self.bump();
                    }
                    let expr = self.parse_unary()?;
                    return Ok(Expr {
                        kind: ExprKind::Delete {
                            array,
                            expr: Box::new(expr),
                        },
                        span: self.span_from(start),
                    });
                }
                "noexcept" => {
                    self.bump();
                    self.expect("(")?;
                    let e = self.nested(|p| p.parse_expr())?;
                    self.expect(")")?;
                    return Ok(Expr {
                        kind: ExprKind::NoexceptExpr(Box::new(e)),
                        span: self.span_from(start),
                    });
                }
                _ => {}
            }
        }
        self.parse_postfix()
    }

    /// Whether `ty` is certainly a type rather than an expression that
    /// happened to parse as one.
    fn type_is_definite(&self, ty: &Type) -> bool {
        match &ty.base {
            TypeName::Named(q) => {
                !ty.ptr_ops.is_empty()
                    || ty.is_const
                    || self.names_type(q)
                    || q.last_args().is_some()
            }
            _ => true,
        }
    }

    fn parse_sizeof(&mut self) -> PResult<Expr> {
        let start = self.cur_span();
        self.bump(); // sizeof
        if self.eat("...") {
            self.expect("(")?;
            let id = self.expect_ident()?;
            self.expect(")")?;
            return Ok(Expr {
                kind: ExprKind::SizeofPack(id),
                span: self.span_from(start),
            });
        }
        if self.at("(") {
            let cp = self.checkpoint();
            self.bump();
            let saved = self.no_gt;
            self.no_gt = 0;
            let ty = self.parse_type_id(false);
            self.no_gt = saved;
            if let Ok(ty) = ty
                && self.at(")")
                && self.type_is_definite(&ty)
            {
                self.bump();
                return Ok(Expr {
                    kind: ExprKind::SizeofType(Box::new(ty)),
                    span: self.span_from(start),
                });
            }
            self.restore(cp);
        }
        let e = self.parse_unary()?;
        Ok(Expr {
            kind: ExprKind::SizeofExpr(Box::new(e)),
            span: self.span_from(start),
        })
    }

    fn parse_new(&mut self) -> PResult<Expr> {
        let start = self.cur_span();
        self.bump(); // new
        let placement = if self.at("(") {
            self.parse_call_args()?
        } else {
            Vec::new()
        };
        let (_, mut ty) = self.parse_decl_specifiers()?;
        ty.ptr_ops = self.parse_ptr_ops();
        let array_size = if self.at("[") {
            self.bump();
            let e = self.nested(|p| p.parse_expr())?;
            self.expect("]")?;
            Some(Box::new(e))
        } else {
            None
        };
        let args = if self.at("(") {
            Some(self.parse_call_args()?)
        } else if self.at("{") {
            Some(self.parse_brace_list()?)
        } else {
            None
        };
        Ok(Expr {
            kind: ExprKind::New {
                ty: Box::new(ty),
                placement,
                array_size,
                args,
            },
            span: self.span_from(start),
        })
    }

    /// `(T) operand` where `T` is certainly a type.
    fn try_c_style_cast(&mut self) -> PResult<Option<Expr>> {
        let start = self.cur_span();
        let cp = self.checkpoint();
        self.bump(); // (
        let t1 = self.peek().clone();
        let plausible = t1.kind == ScTokenKind::Ident
            || t1.is_punct("::")
            || is_builtin_type_keyword(&t1)
            || matches!(
                t1.text.as_str(),
                "const" | "volatile" | "typename" | "struct" | "class" | "enum" | "union" | "auto"
            ) && t1.kind == ScTokenKind::Keyword;
        if plausible {
            let saved = self.no_gt;
            self.no_gt = 0;
            let ty = self.parse_type_id(false);
            self.no_gt = saved;
            if let Ok(ty) = ty
                && self.at(")")
                && self.type_is_definite(&ty)
            {
                self.bump();
                let n = self.peek();
                let starts_operand = match n.kind {
                    ScTokenKind::Ident
                    | ScTokenKind::IntLit
                    | ScTokenKind::FloatLit
                    | ScTokenKind::CharLit
                    | ScTokenKind::StringLit => true,
                    ScTokenKind::Keyword => {
                        matches!(
                            n.text.as_str(),
                            "this"
                                | "true"
                                | "false"
                                | "nullptr"
                                | "sizeof"
                                | "new"
                                | "static_cast"
                                | "dynamic_cast"
                                | "reinterpret_cast"
                                | "const_cast"
                                | "typeid"
                        ) || is_builtin_type_keyword(n)
                    }
                    ScTokenKind::Punct => matches!(
                        n.text.as_str(),
                        "(" | "!" | "~" | "-" | "+" | "*" | "&" | "::" | "++" | "--"
                    ),
                    ScTokenKind::Eof => false,
                };
                if starts_operand {
                    let operand = self.parse_unary()?;
                    return Ok(Some(Expr {
                        span: start.to(operand.span),
                        kind: ExprKind::Cast {
                            kind: CastKind::CStyle,
                            ty: Box::new(ty),
                            expr: Box::new(operand),
                        },
                    }));
                }
            }
        }
        self.restore(cp);
        Ok(None)
    }

    fn parse_postfix(&mut self) -> PResult<Expr> {
        let mut e = self.parse_primary()?;
        loop {
            if self.at("(") {
                let args = self.parse_call_args()?;
                e = Expr {
                    span: self.span_from(e.span),
                    kind: ExprKind::Call {
                        callee: Box::new(e),
                        args,
                    },
                };
            } else if self.at("[") && !self.nth(1).is_punct("[") {
                self.bump();
                let index = self.nested(|p| {
                    if p.at("{") {
                        p.parse_init_list_expr()
                    } else {
                        p.parse_expr()
                    }
                })?;
                self.expect("]")?;
                e = Expr {
                    span: self.span_from(e.span),
                    kind: ExprKind::Index {
                        base: Box::new(e),
                        index: Box::new(index),
                    },
                };
            } else if self.at(".") || self.at("->") {
                let arrow = self.bump().text == "->";
                self.eat_kw("template");
                let name = self.parse_member_name()?;
                e = Expr {
                    span: self.span_from(e.span),
                    kind: ExprKind::Member {
                        base: Box::new(e),
                        arrow,
                        name,
                    },
                };
            } else if self.at("++") || self.at("--") {
                let op = if self.bump().text == "++" {
                    PostfixOp::Inc
                } else {
                    PostfixOp::Dec
                };
                e = Expr {
                    span: self.span_from(e.span),
                    kind: ExprKind::Postfix {
                        op,
                        operand: Box::new(e),
                    },
                };
            } else if self.at("{") && e.as_name().is_some_and(|q| self.names_type(q)) {
                // `T{args}` temporary of a named type.
                let args = self.parse_brace_list()?;
                let ExprKind::Name(q) = e.kind else {
                    unreachable!("checked as_name")
                };
                let ty = Type {
                    is_const: false,
                    is_volatile: false,
                    span: q.span,
                    base: TypeName::Named(q),
                    ptr_ops: Vec::new(),
                };
                e = Expr {
                    span: self.span_from(e.span),
                    kind: ExprKind::Construct {
                        ty: Box::new(ty),
                        args,
                        braced: true,
                    },
                };
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn parse_member_name(&mut self) -> PResult<NameSegment> {
        let ident = if self.at("~") && self.nth(1).kind == ScTokenKind::Ident {
            let tilde = self.bump().span;
            let id = self.bump();
            Ident {
                name: format!("~{}", id.text),
                span: tilde.to(id.span),
            }
        } else if self.at_kw("operator") {
            self.parse_operator_name()?
        } else {
            self.expect_ident()?
        };
        let template_args = if self.at("<") {
            self.try_template_args(&ident.name, false)?
        } else {
            None
        };
        Ok(NameSegment {
            ident,
            template_args,
        })
    }

    fn parse_primary(&mut self) -> PResult<Expr> {
        let start = self.cur_span();
        let t = self.peek().clone();
        let lit = |kind| Ok(Expr { kind, span: start });
        match t.kind {
            ScTokenKind::IntLit => {
                self.bump();
                let value = parse_int(&t.text);
                lit(ExprKind::IntLit {
                    text: t.text,
                    value,
                })
            }
            ScTokenKind::FloatLit => {
                self.bump();
                lit(ExprKind::FloatLit { text: t.text })
            }
            ScTokenKind::CharLit => {
                self.bump();
                lit(ExprKind::CharLit { text: t.text })
            }
            ScTokenKind::StringLit => {
                let mut value = String::new();
                while self.peek().kind == ScTokenKind::StringLit {
                    let s = self.bump();
                    value.push_str(&string_value(&s.text));
                }
                Ok(Expr {
                    kind: ExprKind::StringLit {
                        text: t.text,
                        value,
                    },
                    span: self.span_from(start),
                })
            }
            ScTokenKind::Ident => {
                let q = self.parse_qualified_name(false)?;
                Ok(Expr {
                    span: q.span,
                    kind: ExprKind::Name(q),
                })
            }
            ScTokenKind::Keyword => self.parse_keyword_primary(&t),
            ScTokenKind::Punct => match t.text.as_str() {
                "(" => {
                    self.bump();
                    let inner = self.nested(|p| p.parse_expr())?;
                    self.expect(")")?;
                    Ok(Expr {
                        kind: ExprKind::Paren(Box::new(inner)),
                        span: self.span_from(start),
                    })
                }
                "{" => self.parse_init_list_expr(),
                "[" => self.parse_lambda(),
                "::" | "~" => {
                    let q = self.parse_qualified_name(false)?;
                    Ok(Expr {
                        span: q.span,
                        kind: ExprKind::Name(q),
                    })
                }
                _ => Err(self.err_expected("expression")),
            },
            ScTokenKind::Eof => Err(self.err_expected("expression")),
        }
    }

    fn parse_keyword_primary(&mut self, t: &ScToken) -> PResult<Expr> {
        let start = t.span;
        let simple = |kind| Expr { kind, span: start };
        match t.text.as_str() {
            "true" | "false" => {
                self.bump();
                Ok(simple(ExprKind::BoolLit(t.text == "true")))
            }
            "nullptr" => {
                self.bump();
                Ok(simple(ExprKind::Nullptr))
            }
            "this" => {
                self.bump();
                Ok(simple(ExprKind::This))
            }
            "static_cast" | "dynamic_cast" | "reinterpret_cast" | "const_cast" => {
                self.bump();
                let kind = match t.text.as_str() {
                    "static_cast" => CastKind::Static,
                    "dynamic_cast" => CastKind::Dynamic,
                    "reinterpret_cast" => CastKind::Reinterpret,
                    _ => CastKind::Const,
                };
                self.expect("<")?;
                let saved = self.no_gt;
                self.no_gt = 1;
                let ty = self.parse_type_id(true);
                self.no_gt = saved;
                let ty = ty?;
                self.expect_template_close()?;
                self.expect("(")?;
                let e = self.nested(|p| p.parse_expr())?;
                self.expect(")")?;
                Ok(Expr {
                    kind: ExprKind::Cast {
                        kind,
                        ty: Box::new(ty),
                        expr: Box::new(e),
                    },
                    span: self.span_from(start),
                })
            }
            "typeid" => {
                self.bump();
                self.expect("(")?;
                let cp = self.checkpoint();
                let kind = match self.nested(|p| p.parse_type_id(false)) {
                    Ok(ty) if self.at(")") && self.type_is_definite(&ty) => {
                        ExprKind::TypeidType(Box::new(ty))
                    }
                    _ => {
                        self.restore(cp);
                        ExprKind::TypeidExpr(Box::new(self.nested(|p| p.parse_expr())?))
                    }
                };
                self.expect(")")?;
                Ok(Expr {
                    kind,
                    span: self.span_from(start),
                })
            }
            "typename" | "decltype" | "auto" => {
                if t.text == "typename" {
                    self.bump();
                }
                let (_, ty) = self.parse_decl_specifiers()?;
                self.finish_construct(ty, start)
            }
            "operator" => {
                let q = self.parse_qualified_name(false)?;
                Ok(Expr {
                    span: q.span,
                    kind: ExprKind::Name(q),
                })
            }
            _ if is_builtin_type_keyword(t) => {
                let (_, ty) = self.parse_decl_specifiers()?;
                self.finish_construct(ty, start)
            }
            _ => Err(self.err_expected("expression")),
        }
    }

    /// `ty(args)` or `ty{args}` after a type in expression position.
    fn finish_construct(&mut self, ty: Type, start: ScSpan) -> PResult<Expr> {
        let (args, braced) = if self.at("(") {
            (self.parse_call_args()?, false)
        } else if self.at("{") {
            (self.parse_brace_list()?, true)
        } else {
            return Err(self.err_expected("'(' or '{' after type in expression"));
        };
        Ok(Expr {
            kind: ExprKind::Construct {
                ty: Box::new(ty),
                args,
                braced,
            },
            span: self.span_from(start),
        })
    }

    /// `(args)` of a call or parenthesized initializer.
    pub(super) fn parse_call_args(&mut self) -> PResult<Vec<Expr>> {
        self.expect("(")?;
        let args = self.nested(|p| p.expr_list(")"))?;
        self.expect(")")?;
        Ok(args)
    }

    /// `{a, b}` as a list of elements.
    pub(super) fn parse_brace_list(&mut self) -> PResult<Vec<Expr>> {
        self.expect("{")?;
        let items = self.nested(|p| p.expr_list("}"))?;
        self.expect("}")?;
        Ok(items)
    }

    /// `{a, b}` as an expression.
    pub(super) fn parse_init_list_expr(&mut self) -> PResult<Expr> {
        let start = self.cur_span();
        let items = self.parse_brace_list()?;
        Ok(Expr {
            kind: ExprKind::InitList(items),
            span: self.span_from(start),
        })
    }

    /// Comma-separated initializer clauses up to (not past) `close`; a
    /// trailing comma is accepted.
    fn expr_list(&mut self, close: &str) -> PResult<Vec<Expr>> {
        let mut items = Vec::new();
        while !self.at(close) && !self.at_eof() {
            // C++20 designated initializer `.x = 1`: keep the value.
            if self.at(".") && self.nth(1).kind == ScTokenKind::Ident && self.nth(2).is_punct("=") {
                self.bump();
                self.bump();
                self.bump();
            }
            let mut e = if self.at("{") {
                self.parse_init_list_expr()?
            } else {
                self.parse_assign()?
            };
            if self.at("...") {
                self.bump();
                e = Expr {
                    span: self.span_from(e.span),
                    kind: ExprKind::PackExpansion(Box::new(e)),
                };
            }
            items.push(e);
            if !self.eat(",") {
                break;
            }
        }
        Ok(items)
    }

    fn parse_lambda(&mut self) -> PResult<Expr> {
        let start = self.cur_span();
        self.bump(); // [
        let mut captures = Vec::new();
        while !self.at("]") && !self.at_eof() {
            let cap = if self.at("=") {
                self.bump();
                Capture::DefaultCopy
            } else if self.at("&") && (self.nth(1).is_punct(",") || self.nth(1).is_punct("]")) {
                self.bump();
                Capture::DefaultRef
            } else if self.eat_kw("this") {
                Capture::This
            } else if self.at("*") && self.nth(1).is_keyword("this") {
                self.bump();
                self.bump();
                Capture::StarThis
            } else {
                let by_ref = self.eat("&");
                let name = self.expect_ident()?;
                self.eat("...");
                let init = if self.eat("=") {
                    Some(self.nested(|p| p.parse_assign())?)
                } else {
                    None
                };
                Capture::Var { name, by_ref, init }
            };
            captures.push(cap);
            if !self.eat(",") {
                break;
            }
        }
        self.expect("]")?;
        let params = if self.at("(") {
            self.parse_params()?.0
        } else {
            Vec::new()
        };
        let mut is_mutable = false;
        loop {
            self.skip_attributes();
            if self.eat_kw("mutable") {
                is_mutable = true;
            } else if self.eat_kw("constexpr") {
            } else if self.eat_kw("noexcept") {
                if self.at("(") {
                    self.skip_balanced()?;
                }
            } else {
                break;
            }
        }
        let return_type = if self.eat("->") {
            Some(self.parse_type_id(false)?)
        } else {
            None
        };
        let body = self.parse_block()?;
        Ok(Expr {
            kind: ExprKind::Lambda(Box::new(Lambda {
                captures,
                params,
                is_mutable,
                return_type,
                body,
            })),
            span: self.span_from(start),
        })
    }

    // ---- names -----------------------------------------------------------

    /// `[::] seg [:: seg]…` where each segment may carry template arguments.
    /// In a type context (`ty_ctx`) `name<` opens template arguments
    /// whenever they parse; in an expression only for a known template, or
    /// when they parse and are followed by `(` or `::`.
    pub(super) fn parse_qualified_name(&mut self, ty_ctx: bool) -> PResult<QualifiedName> {
        let start = self.cur_span();
        let global = self.eat("::");
        let mut segments = Vec::new();
        loop {
            self.eat_kw("template");
            let ident = if self.at_ident() {
                self.expect_ident()?
            } else if self.at("~") && self.nth(1).kind == ScTokenKind::Ident {
                let tilde = self.bump().span;
                let id = self.bump();
                Ident {
                    name: format!("~{}", id.text),
                    span: tilde.to(id.span),
                }
            } else if self.at_kw("operator") {
                self.parse_operator_name()?
            } else {
                return Err(self.err_expected("identifier"));
            };
            let template_args = if self.at("<") && !ident.name.starts_with("operator") {
                self.try_template_args(&ident.name, ty_ctx)?
            } else {
                None
            };
            segments.push(NameSegment {
                ident,
                template_args,
            });
            let continues = self.at("::")
                && (self.nth(1).kind == ScTokenKind::Ident
                    || self.nth(1).is_punct("~")
                    || self.nth(1).is_keyword("operator")
                    || self.nth(1).is_keyword("template"));
            if !continues {
                break;
            }
            self.bump();
        }
        Ok(QualifiedName {
            global,
            segments,
            span: self.span_from(start),
        })
    }

    /// Template arguments after `name` at a `<`, or `None` (cursor
    /// unchanged) when the `<` is a less-than.
    fn try_template_args(&mut self, name: &str, ty_ctx: bool) -> PResult<Option<Vec<TemplateArg>>> {
        if self.is_template_name(name) {
            return self.parse_template_args().map(Some);
        }
        let cp = self.checkpoint();
        match self.parse_template_args() {
            Ok(args) => {
                let accept = ty_ctx
                    || ((self.at("(") || self.at("::"))
                        && args.iter().all(|a| match a {
                            TemplateArg::Type(_) => true,
                            TemplateArg::Expr(e) => matches!(
                                e.kind,
                                ExprKind::IntLit { .. } | ExprKind::Name(_) | ExprKind::BoolLit(_)
                            ),
                        }));
                if accept {
                    Ok(Some(args))
                } else {
                    self.restore(cp);
                    Ok(None)
                }
            }
            Err(Fail) => {
                self.restore(cp);
                Ok(None)
            }
        }
    }

    pub(super) fn parse_template_args(&mut self) -> PResult<Vec<TemplateArg>> {
        self.expect("<")?;
        let saved = self.no_gt;
        self.no_gt = 1;
        let r = self.template_arg_list();
        self.no_gt = saved;
        let args = r?;
        self.expect_template_close()?;
        Ok(args)
    }

    fn template_arg_list(&mut self) -> PResult<Vec<TemplateArg>> {
        let mut args = Vec::new();
        if self.peek().text.starts_with('>') && self.peek().kind == ScTokenKind::Punct {
            return Ok(args);
        }
        loop {
            let mut arg = self.parse_template_arg()?;
            if self.eat("...")
                && let TemplateArg::Expr(e) = arg
            {
                arg = TemplateArg::Expr(Expr {
                    span: self.span_from(e.span),
                    kind: ExprKind::PackExpansion(Box::new(e)),
                });
            }
            args.push(arg);
            if !self.eat(",") {
                break;
            }
        }
        Ok(args)
    }

    fn parse_template_arg(&mut self) -> PResult<TemplateArg> {
        let t = self.peek().clone();
        let starts_type = is_builtin_type_keyword(&t)
            || (t.kind == ScTokenKind::Keyword
                && matches!(
                    t.text.as_str(),
                    "const"
                        | "volatile"
                        | "typename"
                        | "struct"
                        | "class"
                        | "enum"
                        | "union"
                        | "auto"
                        | "decltype"
                ));
        if starts_type || t.kind == ScTokenKind::Ident || t.is_punct("::") {
            let cp = self.checkpoint();
            if let Ok(ty) = self.parse_type_id(true) {
                let closes = self.at(",")
                    || self.at("...")
                    || (self.peek().kind == ScTokenKind::Punct
                        && self.peek().text.starts_with('>'));
                let definite = starts_type
                    || matches!(ty.base, TypeName::Function { .. })
                    || self.type_is_definite(&ty);
                if closes && definite {
                    return Ok(TemplateArg::Type(ty));
                }
            }
            self.restore(cp);
        }
        Ok(TemplateArg::Expr(self.parse_conditional()?))
    }
}

#[cfg(test)]
mod tests {
    use super::string_value;

    #[test]
    fn string_values() {
        assert_eq!(string_value(r#""a\tb\x41\101\"""#), "a\tbAA\"");
        assert_eq!(string_value(r#"u8"x""#), "x");
        assert_eq!(string_value(r#"R"d(a\n)"b)d""#), r#"a\n)"b"#);
    }
}
