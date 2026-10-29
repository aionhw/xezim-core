//! vhdl_lang's syntax tree → xezim's VHDL AST (`ast`).
//!
//! The conversion keeps the shapes the analysis expects from the earlier
//! parser: names stay unclassified (`f(x)`, `a(i)`, `a(3 downto 0)` are all
//! calls; sema decides), index, element and record constraints are lists of
//! associations, and a single parenthesized value is `Paren`. A construct
//! the conversion does not know becomes an error at its location ("not
//! supported yet"), never a silently dropped one.
//!
//! Positions: vhdl_lang gives each token a line and a UTF-16 column. The
//! source is handed to it as Latin-1 (one byte, one character), so a column
//! is a byte offset in its line; `Lines` turns positions into byte offsets.

use vhdl_lang::ast as v;
use vhdl_lang::ast::token_range::WithTokenSpan;
use vhdl_lang::{HasTokenSpan, Position, Token, TokenAccess, TokenId, TokenSpan};

use super::Diagnostic;
use crate::vhdl::ast::*;

/// Line start offsets with vhdl_lang's line breaks (`\r\n`, `\r`, `\n`).
pub struct Lines {
    starts: Vec<usize>,
}

impl Lines {
    pub fn new(text: &[u8]) -> Lines {
        let mut starts = vec![0];
        let mut i = 0;
        while i < text.len() {
            match text[i] {
                b'\r' if text.get(i + 1) == Some(&b'\n') => {
                    i += 2;
                    starts.push(i);
                }
                b'\r' | b'\n' => {
                    i += 1;
                    starts.push(i);
                }
                _ => i += 1,
            }
        }
        Lines { starts }
    }

    /// The byte offset of a position.
    pub fn offset(&self, p: Position) -> usize {
        self.starts
            .get(p.line as usize)
            .map_or(usize::MAX, |s| s + p.character as usize)
    }
}

/// Identifiers are case-insensitive; extended identifiers keep their text.
pub fn fold(s: &str) -> String {
    if s.starts_with('\\') {
        s.to_string()
    } else {
        s.to_ascii_lowercase()
    }
}

/// Latin-1 bytes as a string, one character per byte.
fn latin1(b: &[u8]) -> String {
    b.iter().map(|&c| c as char).collect()
}

/// The text of an operator symbol (`"+"`, `"and"`).
fn op_text(op: v::Operator) -> &'static str {
    use v::Operator::*;
    match op {
        And => "and",
        Or => "or",
        Nand => "nand",
        Nor => "nor",
        Xor => "xor",
        Xnor => "xnor",
        Abs => "abs",
        Not => "not",
        Minus => "-",
        Plus => "+",
        QueQue => "??",
        EQ => "=",
        NE => "/=",
        LT => "<",
        LTE => "<=",
        GT => ">",
        GTE => ">=",
        QueEQ => "?=",
        QueNE => "?/=",
        QueLT => "?<",
        QueLTE => "?<=",
        QueGT => "?>",
        QueGTE => "?>=",
        SLL => "sll",
        SRL => "srl",
        SLA => "sla",
        SRA => "sra",
        ROL => "rol",
        ROR => "ror",
        Concat => "&",
        Times => "*",
        Div => "/",
        Mod => "mod",
        Rem => "rem",
        Pow => "**",
    }
}

/// The name of an attribute designator, lower case.
fn attr_text(a: &v::AttributeDesignator) -> String {
    use v::AttributeDesignator::*;
    match a {
        Type(v::TypeAttribute::Subtype) => "subtype".into(),
        Type(v::TypeAttribute::Element) => "element".into(),
        Range(v::RangeAttribute::Range) => "range".into(),
        Range(v::RangeAttribute::ReverseRange) => "reverse_range".into(),
        Ident(s) => fold(&latin1(&s.item.name().bytes)),
        Ascending => "ascending".into(),
        Left => "left".into(),
        Right => "right".into(),
        High => "high".into(),
        Low => "low".into(),
        Length => "length".into(),
        Image => "image".into(),
        Value => "value".into(),
        Pos => "pos".into(),
        Val => "val".into(),
        Succ => "succ".into(),
        Pred => "pred".into(),
        LeftOf => "leftof".into(),
        RightOf => "rightof".into(),
        Signal(s) => match s {
            v::SignalAttribute::Delayed => "delayed",
            v::SignalAttribute::Stable => "stable",
            v::SignalAttribute::Quiet => "quiet",
            v::SignalAttribute::Transaction => "transaction",
            v::SignalAttribute::Event => "event",
            v::SignalAttribute::Active => "active",
            v::SignalAttribute::LastEvent => "last_event",
            v::SignalAttribute::LastActive => "last_active",
            v::SignalAttribute::LastValue => "last_value",
            v::SignalAttribute::Driving => "driving",
            v::SignalAttribute::DrivingValue => "driving_value",
        }
        .into(),
        SimpleName => "simple_name".into(),
        InstanceName => "instance_name".into(),
        PathName => "path_name".into(),
        Converse => "converse".into(),
    }
}

/// Attributes that take a parameter (`t'image(x)`, `a'length(2)`,
/// `s'delayed(5 ns)`); `x'other(e)` is a call of the attribute's value.
fn takes_param(attr: &str) -> bool {
    matches!(
        attr,
        "image"
            | "value"
            | "pos"
            | "val"
            | "succ"
            | "pred"
            | "leftof"
            | "rightof"
            | "left"
            | "right"
            | "high"
            | "low"
            | "length"
            | "range"
            | "reverse_range"
            | "ascending"
            | "delayed"
            | "stable"
            | "quiet"
    )
}

fn obj_class(c: v::ObjectClass) -> ObjClass {
    match c {
        v::ObjectClass::Signal => ObjClass::Signal,
        v::ObjectClass::Constant => ObjClass::Constant,
        v::ObjectClass::Variable | v::ObjectClass::SharedVariable => ObjClass::Variable,
    }
}

fn mode(m: v::Mode) -> Mode {
    match m {
        v::Mode::In => Mode::In,
        v::Mode::Out => Mode::Out,
        v::Mode::InOut => Mode::InOut,
        v::Mode::Buffer => Mode::Buffer,
        v::Mode::Linkage => Mode::Linkage,
    }
}

fn force_mode(m: &Option<v::ForceMode>) -> Option<ForceMode> {
    m.as_ref().map(|m| match m {
        v::ForceMode::In => ForceMode::In,
        v::ForceMode::Out => ForceMode::Out,
    })
}

/// The converter of one design unit (positions are per unit).
pub struct Converter<'a> {
    pub errors: Vec<Diagnostic>,
    tokens: &'a [Token],
    lines: &'a Lines,
    text: &'a [u8],
}

impl<'a> Converter<'a> {
    pub fn new(tokens: &'a [Token], lines: &'a Lines, text: &'a [u8]) -> Self {
        Converter {
            errors: Vec::new(),
            tokens,
            lines,
            text,
        }
    }

    // ---- positions ------------------------------------------------------------

    fn tok_span(&self, t: TokenId) -> Span {
        let p = self.tokens.get_pos(t);
        self.lines.offset(p.range.start)..self.lines.offset(p.range.end)
    }

    fn span(&self, s: TokenSpan) -> Span {
        self.span2(s.start_token, s.end_token)
    }

    fn span2(&self, a: TokenId, b: TokenId) -> Span {
        let (pa, pb) = (self.tokens.get_pos(a), self.tokens.get_pos(b));
        self.lines.offset(pa.range.start)..self.lines.offset(pb.range.end)
    }

    fn has_span(&self, x: &dyn HasTokenSpan) -> Span {
        self.span2(x.get_start_token(), x.get_end_token())
    }

    fn err(&mut self, s: Span, msg: impl Into<String>) {
        self.errors.push(Diagnostic {
            span: s,
            message: msg.into(),
        });
    }

    fn unsupported(&mut self, s: Span, what: &str) {
        self.err(s, format!("VHDL: {} is not supported yet", what));
    }

    /// The source text of a span, one character per byte.
    fn text_of(&self, s: &Span) -> String {
        latin1(self.text.get(s.clone()).unwrap_or_default())
    }

    // ---- identifiers -------------------------------------------------------------

    fn ident(&self, i: &v::Ident) -> Ident {
        Ident {
            name: fold(&latin1(&i.item.name().bytes)),
            span: self.tok_span(i.token),
        }
    }

    fn idents(&self, l: &[v::WithDecl<v::Ident>]) -> Vec<Ident> {
        l.iter().map(|i| self.ident(&i.tree)).collect()
    }

    // ---- design units ------------------------------------------------------------

    pub fn design_unit(&mut self, u: &v::AnyDesignUnit, span: Span) -> Option<DesignUnit> {
        use v::{AnyDesignUnit as U, AnyPrimaryUnit as P, AnySecondaryUnit as S};
        let (context, unit) = match u {
            U::Primary(P::Entity(e)) => (
                self.context_items(&e.context_clause),
                LibraryUnit::Entity(EntityDecl {
                    name: self.ident(&e.ident.tree),
                    generics: self.interface_list(e.generic_clause.as_ref()),
                    ports: self.interface_list(e.port_clause.as_ref()),
                    decls: self.decls(&e.decl),
                    stmts: self.conc_stmts(&e.statements),
                }),
            ),
            U::Primary(P::Configuration(c)) => {
                if let Some(d) = c.decl.first() {
                    let s = self.span(d.span);
                    self.unsupported(s, "a configuration declarative part");
                }
                (
                    self.context_items(&c.context_clause),
                    LibraryUnit::Configuration(ConfigDecl {
                        name: self.ident(&c.ident.tree),
                        entity: self.name(&c.entity_name)?,
                        block: self.block_config(&c.block_config),
                        span: span.clone(),
                    }),
                )
            }
            U::Primary(P::Package(p)) => (
                self.context_items(&p.context_clause),
                LibraryUnit::Package(PackageDecl {
                    name: self.ident(&p.ident.tree),
                    generics: self.interface_list(p.generic_clause.as_ref()),
                    generic_map: None,
                    decls: self.decls(&p.decl),
                    span: span.clone(),
                }),
            ),
            U::Primary(P::PackageInstance(p)) => (
                self.context_items(&p.context_clause),
                LibraryUnit::PackageInst(self.package_inst(p, span.clone())?),
            ),
            U::Primary(P::Context(c)) => (
                Vec::new(),
                LibraryUnit::Context(ContextDecl {
                    name: self.ident(&c.ident.tree),
                    items: self.context_items(&c.items),
                }),
            ),
            U::Secondary(S::Architecture(a)) => (
                self.context_items(&a.context_clause),
                LibraryUnit::Architecture(ArchBody {
                    name: self.ident(&a.ident.tree),
                    entity: self.ident(&a.entity_name.item),
                    decls: self.decls(&a.decl),
                    stmts: self.conc_stmts(&a.statements),
                }),
            ),
            U::Secondary(S::PackageBody(p)) => (
                self.context_items(&p.context_clause),
                LibraryUnit::PackageBody(PackageBody {
                    name: self.ident(&p.ident.tree),
                    decls: self.decls(&p.decl),
                    span: span.clone(),
                }),
            ),
        };
        Some(DesignUnit {
            context,
            unit,
            span,
        })
    }

    fn context_items(&mut self, items: &[v::ContextItem]) -> Vec<ContextItem> {
        let mut out = Vec::new();
        for c in items {
            match c {
                v::ContextItem::Library(l) => out.push(ContextItem::Library(
                    l.name_list.iter().map(|n| self.ident(&n.item)).collect(),
                )),
                v::ContextItem::Use(u) => out.push(ContextItem::Use(self.names(&u.name_list))),
                v::ContextItem::Context(r) => {
                    out.push(ContextItem::Context(self.names(&r.name_list)))
                }
            }
        }
        out
    }

    fn names(&mut self, l: &[WithTokenSpan<v::Name>]) -> Vec<Name> {
        l.iter().filter_map(|n| self.name(n)).collect()
    }

    fn package_inst(&mut self, p: &v::PackageInstantiation, span: Span) -> Option<PackageInst> {
        Some(PackageInst {
            name: self.ident(&p.ident.tree),
            package: self.name(&p.package_name)?,
            generic_map: self.map_aspect(p.generic_map.as_ref()),
            span,
        })
    }

    // ---- interfaces --------------------------------------------------------------

    fn interface_list(&mut self, l: Option<&v::InterfaceList>) -> Vec<InterfaceDecl> {
        let Some(l) = l else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for item in &l.items {
            match item {
                v::InterfaceDeclaration::Object(o) => {
                    let span = self.has_span(o);
                    let v::ModeIndication::Simple(m) = &o.mode else {
                        self.unsupported(span, "a mode view");
                        continue;
                    };
                    // The class as written (`signal x : bit`), or none: the
                    // analysis applies the default of the interface list.
                    let first = self
                        .text_of(&span)
                        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                        .next()
                        .unwrap_or_default()
                        .to_ascii_lowercase();
                    let class = matches!(first.as_str(), "constant" | "signal" | "variable")
                        .then(|| obj_class(m.class));
                    let Some(ty) = self.subtype_ind(&m.subtype_indication) else {
                        continue;
                    };
                    let default = m.expression.as_ref().and_then(|e| self.cond_expr(e));
                    out.push(InterfaceDecl::Object(InterfaceObject {
                        class,
                        names: self.idents(&o.idents),
                        mode: m.mode.as_ref().map(|m| mode(m.item)),
                        ty,
                        bus: m.bus,
                        default,
                        span,
                    }));
                }
                v::InterfaceDeclaration::File(f) => {
                    let span = self.has_span(f);
                    let Some(ty) = self.subtype_ind(&f.subtype_indication) else {
                        continue;
                    };
                    out.push(InterfaceDecl::Object(InterfaceObject {
                        class: Some(ObjClass::File),
                        names: self.idents(&f.idents),
                        mode: None,
                        ty,
                        bus: false,
                        default: None,
                        span,
                    }));
                }
                v::InterfaceDeclaration::Type(t) => {
                    out.push(InterfaceDecl::Type(self.ident(&t.tree), None))
                }
                v::InterfaceDeclaration::TypeClass(t) => {
                    if let Some(class) = self.type_class(&t.definition.item) {
                        out.push(InterfaceDecl::Type(self.ident(&t.ident.tree), Some(class)));
                    }
                }
                v::InterfaceDeclaration::Subprogram(s) => {
                    let Some(spec) = self.subprogram_spec(&s.specification) else {
                        continue;
                    };
                    let default = match &s.default {
                        None => None,
                        Some(v::SubprogramDefault::Box) => Some(SubprogramDefault::Box),
                        Some(v::SubprogramDefault::Name(n)) => {
                            self.name(n).map(SubprogramDefault::Name)
                        }
                    };
                    out.push(InterfaceDecl::Subprogram { spec, default });
                }
                v::InterfaceDeclaration::Package(p) => {
                    let span = self.has_span(p);
                    if let Some(package) = self.name(&p.package_name) {
                        out.push(InterfaceDecl::Package {
                            name: self.ident(&p.ident.tree),
                            package,
                            generic_map: None,
                            span,
                        });
                    }
                }
            }
        }
        out
    }

    /// The class of a generic type (VHDL-2019 §6.5.3).
    fn type_class(&mut self, d: &v::IncompleteTypeDefinition) -> Option<TypeClass> {
        use v::IncompleteTypeDefinition as I;
        Some(match d {
            I::Private => TypeClass::Private,
            I::Scalar => TypeClass::Scalar,
            I::Discrete => TypeClass::Discrete,
            I::Integer => TypeClass::Integer,
            I::Physical => TypeClass::Physical,
            I::Floating => TypeClass::Floating,
            I::Array(indexes, elem) => {
                let mut out = Vec::new();
                for i in indexes {
                    out.push(match i {
                        v::IncompleteArrayIndex::Unbounded(m) => ClassIndex::Unbounded(self.name(m)?),
                        v::IncompleteArrayIndex::Constraint(r) => {
                            ClassIndex::Range(self.discrete_range(r)?)
                        }
                        v::IncompleteArrayIndex::Anonymous(a) => {
                            ClassIndex::Anonymous(self.type_class(&a.item)?)
                        }
                    });
                }
                TypeClass::Array(out, Box::new(self.class_subtype(elem)?))
            }
            I::Access(s) => TypeClass::Access(Box::new(self.class_subtype(s)?)),
            I::File(s) => TypeClass::File(Box::new(self.class_subtype(s)?)),
        })
    }

    fn class_subtype(&mut self, s: &v::IncompleteSubtype) -> Option<ClassSubtype> {
        Some(match s {
            v::IncompleteSubtype::Subtype(s) => ClassSubtype::Subtype(Box::new(self.subtype_ind(s)?)),
            v::IncompleteSubtype::Anonymous(a) => ClassSubtype::Anonymous(self.type_class(&a.item)?),
        })
    }

    fn subprogram_spec(&mut self, s: &v::SubprogramSpecification) -> Option<SubprogramSpec> {
        let span = self.has_span(s);
        let (designator, header, params, kind) = match s {
            v::SubprogramSpecification::Procedure(p) => (
                &p.designator,
                p.header.as_ref(),
                p.parameter_list.as_ref(),
                SubprogramKind::Procedure,
            ),
            v::SubprogramSpecification::Function(f) => {
                if let Some(r) = &f.return_identifier {
                    let s = self.tok_span(r.tree.token);
                    self.unsupported(s, "a function return identifier");
                }
                (
                    &f.designator,
                    f.header.as_ref(),
                    f.parameter_list.as_ref(),
                    SubprogramKind::Function {
                        pure: f.pure,
                        ret: self.name(&f.return_type)?,
                    },
                )
            }
        };
        let d = &designator.tree;
        let designator = match &d.item {
            v::SubprogramDesignator::Identifier(sym) => Designator::Ident(Ident {
                name: fold(&latin1(&sym.name().bytes)),
                span: self.tok_span(d.token),
            }),
            v::SubprogramDesignator::OperatorSymbol(op) => {
                Designator::Op(op_text(*op).to_string(), self.tok_span(d.token))
            }
        };
        Some(SubprogramSpec {
            kind,
            designator,
            generics: self.interface_list(header.map(|h| &h.generic_list)),
            params: self.interface_list(params),
            span,
        })
    }

    // ---- subtype indications and types ---------------------------------------------

    pub fn subtype_ind(&mut self, s: &v::SubtypeIndication) -> Option<SubtypeInd> {
        let resolution = match &s.resolution {
            None => None,
            Some(r) => Some(self.resolution(r)?),
        };
        let start = match &s.resolution {
            Some(r) => r.get_start_token(),
            None => s.type_mark.span.start_token,
        };
        let end = match &s.constraint {
            Some(c) => c.span.end_token,
            None => s.type_mark.span.end_token,
        };
        let constraint = match &s.constraint {
            None => None,
            Some(c) => Some(self.constraint(c)?),
        };
        Some(SubtypeInd {
            resolution,
            mark: self.name(&s.type_mark)?,
            constraint,
            span: self.span2(start, end),
        })
    }

    fn resolution(&mut self, r: &v::ResolutionIndication) -> Option<Resolution> {
        match r {
            v::ResolutionIndication::FunctionName(n) => Some(Resolution::Function(self.name(n)?)),
            v::ResolutionIndication::Element(e) => match &e.item {
                v::ElementResolution::Array(inner) => {
                    Some(Resolution::Element(Box::new(self.resolution(inner)?)))
                }
                v::ElementResolution::Record(_) => {
                    let s = self.span(e.span);
                    self.unsupported(s, "record element resolution");
                    None
                }
            },
        }
    }

    /// A constraint: a range, or the association lists the earlier parser
    /// produced for index, element and record constraints
    /// (`t(7 downto 0)(1 to 2)`, `rec(a(3 downto 0))`).
    fn constraint(&mut self, c: &WithTokenSpan<v::SubtypeConstraint>) -> Option<Constraint> {
        match &c.item {
            v::SubtypeConstraint::Range(r) => Some(Constraint::Range(self.range(r)?)),
            _ => Some(Constraint::Paren(self.constraint_groups(c)?)),
        }
    }

    fn constraint_groups(
        &mut self,
        c: &WithTokenSpan<v::SubtypeConstraint>,
    ) -> Option<Vec<Vec<Assoc>>> {
        let span = self.span(c.span);
        match &c.item {
            v::SubtypeConstraint::Range(r) => {
                // A range as an element constraint: one association.
                let r = self.range(r)?;
                Some(vec![vec![Assoc {
                    formal: None,
                    actual: Actual::Expr(range_expr(r, span.clone())),
                    span,
                }]])
            }
            v::SubtypeConstraint::Array(ranges, elem) => {
                let mut group = Vec::new();
                if ranges.is_empty() {
                    group.push(Assoc {
                        formal: None,
                        actual: Actual::Open(span.clone()),
                        span: span.clone(),
                    });
                }
                for dr in ranges {
                    let s = self.span(dr.span);
                    let e = self.discrete_range_expr(&dr.item, s.clone())?;
                    group.push(Assoc {
                        formal: None,
                        actual: Actual::Expr(e),
                        span: s,
                    });
                }
                let mut groups = vec![group];
                if let Some(e) = elem {
                    groups.extend(self.constraint_groups(e)?);
                }
                Some(groups)
            }
            v::SubtypeConstraint::Record(els) => {
                let mut group = Vec::new();
                for el in els {
                    let id = self.ident(&el.ident);
                    let mut n = Name {
                        span: id.span.clone(),
                        kind: NameKind::Simple(id),
                    };
                    let cs = self.span(el.constraint.span);
                    for g in self.constraint_groups(&el.constraint)? {
                        n = Name {
                            span: n.span.start..cs.end,
                            kind: NameKind::Call(Box::new(n), g),
                        };
                    }
                    let s = n.span.clone();
                    group.push(Assoc {
                        formal: None,
                        actual: Actual::Expr(Expr {
                            span: s.clone(),
                            kind: ExprKind::Name(n),
                        }),
                        span: s,
                    });
                }
                Some(vec![group])
            }
        }
    }

    fn range(&mut self, r: &v::Range) -> Option<RangeExpr> {
        match r {
            v::Range::Range(rc) => {
                let left = self.expr(&rc.left_expr)?;
                let right = self.expr(&rc.right_expr)?;
                let span = left.span.start..right.span.end;
                Some(RangeExpr::Explicit {
                    left: Box::new(left),
                    dir: match rc.direction {
                        v::Direction::Ascending => Dir::To,
                        v::Direction::Descending => Dir::Downto,
                    },
                    right: Box::new(right),
                    span,
                })
            }
            v::Range::Attribute(a) => Some(RangeExpr::Attr(self.attribute_name(a)?)),
        }
    }

    /// A discrete range where the earlier parser saw an expression (a slice
    /// or an index constraint).
    fn discrete_range_expr(&mut self, d: &v::DiscreteRange, span: Span) -> Option<Expr> {
        Some(match d {
            v::DiscreteRange::Range(v::Range::Attribute(a)) => Expr {
                kind: ExprKind::Name(self.attribute_name(a)?),
                span,
            },
            v::DiscreteRange::Range(r) => range_expr(self.range(r)?, span),
            v::DiscreteRange::Discrete(mark, None) => Expr {
                kind: ExprKind::Name(self.name(mark)?),
                span,
            },
            v::DiscreteRange::Discrete(_, Some(r)) => range_expr(self.range(r)?, span),
        })
    }

    fn discrete_range(&mut self, d: &v::DiscreteRange) -> Option<DiscreteRange> {
        Some(match d {
            v::DiscreteRange::Range(r) => DiscreteRange::Range(self.range(r)?),
            v::DiscreteRange::Discrete(mark, r) => {
                let constraint = match r {
                    Some(r) => Some(Constraint::Range(self.range(r)?)),
                    None => None,
                };
                let span = self.span(mark.span);
                let span = match &constraint {
                    Some(Constraint::Range(RangeExpr::Explicit { span: rs, .. })) => {
                        span.start..rs.end
                    }
                    _ => span,
                };
                DiscreteRange::Subtype(SubtypeInd {
                    resolution: None,
                    mark: self.name(mark)?,
                    constraint,
                    span,
                })
            }
        })
    }

    /// `range implementation_defined` (STD.STANDARD), carried by the parser
    /// as `implementation_defined'range`.
    fn is_implementation_defined(r: &v::Range) -> bool {
        matches!(r, v::Range::Attribute(a)
            if matches!(&a.name.item, v::Name::Designator(d)
                if matches!(&d.item, v::Designator::Identifier(s)
                    if s.name().bytes.eq_ignore_ascii_case(b"implementation_defined"))))
    }

    fn type_def(&mut self, d: &v::TypeDefinition, span: Span) -> Option<TypeDef> {
        Some(match d {
            v::TypeDefinition::Enumeration(lits) => TypeDef::Enum(
                lits.iter()
                    .map(|l| match &l.tree.item {
                        v::EnumerationLiteral::Identifier(s) => EnumLit::Ident(Ident {
                            name: fold(&latin1(&s.name().bytes)),
                            span: self.tok_span(l.tree.token),
                        }),
                        v::EnumerationLiteral::Character(c) => {
                            EnumLit::Char(*c, self.tok_span(l.tree.token))
                        }
                    })
                    .collect(),
            ),
            v::TypeDefinition::Numeric(r) => {
                if Self::is_implementation_defined(r) {
                    TypeDef::ImplementationDefined
                } else {
                    TypeDef::Range(self.range(r)?)
                }
            }
            v::TypeDefinition::Physical(p) => {
                let range = if Self::is_implementation_defined(&p.range) {
                    RangeExpr::Attr(Name {
                        kind: NameKind::Simple(Ident {
                            name: "implementation_defined".into(),
                            span: span.clone(),
                        }),
                        span: span.clone(),
                    })
                } else {
                    self.range(&p.range)?
                };
                let mut secondary = Vec::new();
                for (name, lit) in &p.secondary_units {
                    let s = self.span(lit.span);
                    secondary.push((self.ident(&name.tree), self.physical_literal(&lit.item, s)));
                }
                TypeDef::Physical {
                    range,
                    primary: self.ident(&p.primary_unit.tree),
                    secondary,
                }
            }
            v::TypeDefinition::Array(indexes, _, elem) => {
                let unbounded = indexes
                    .iter()
                    .all(|i| matches!(i, v::ArrayIndex::IndexSubtypeDefintion(_)));
                let index = if unbounded {
                    let mut marks = Vec::new();
                    for i in indexes {
                        if let v::ArrayIndex::IndexSubtypeDefintion(m) = i {
                            marks.push(self.name(m)?);
                        }
                    }
                    ArrayIndex::Unbounded(marks)
                } else {
                    let mut ranges = Vec::new();
                    for i in indexes {
                        match i {
                            v::ArrayIndex::Discrete(dr) => ranges.push(self.discrete_range(&dr.item)?),
                            v::ArrayIndex::IndexSubtypeDefintion(m) => {
                                let s = self.span(m.span);
                                self.unsupported(s, "a mix of constrained and unbounded indexes");
                                return None;
                            }
                        }
                    }
                    ArrayIndex::Constrained(ranges)
                };
                TypeDef::Array {
                    index,
                    elem: self.subtype_ind(elem)?,
                }
            }
            v::TypeDefinition::Record(els) => {
                let mut fields = Vec::new();
                for e in els {
                    fields.push((self.idents(&e.idents), self.subtype_ind(&e.subtype)?));
                }
                TypeDef::Record(fields)
            }
            v::TypeDefinition::Access(s) => TypeDef::Access(self.subtype_ind(s)?),
            v::TypeDefinition::File(n) => TypeDef::File(self.name(n)?),
            v::TypeDefinition::Protected(p) => {
                let mut decls = Vec::new();
                for item in &p.items {
                    match item {
                        v::ProtectedTypeDeclarativeItem::Subprogram(s) => {
                            if let Some(spec) = self.subprogram_spec(&s.specification) {
                                decls.push(Decl::SubprogramDecl(spec));
                            }
                        }
                        v::ProtectedTypeDeclarativeItem::Other(d) => {
                            if let v::Declaration::SubprogramBody(_) = &d.item {
                                let s = self.span(d.span);
                                self.err(
                                    s,
                                    "VHDL: a subprogram body is not allowed in a protected type declaration",
                                );
                                continue;
                            }
                            decls.extend(self.decl(d));
                        }
                        // A private variable (VHDL-2019): the only variable
                        // declaration a protected type declaration has.
                        v::ProtectedTypeDeclarativeItem::Private(d) => decls.extend(self.decl(d)),
                    }
                }
                TypeDef::Protected {
                    generics: self.interface_list(p.generic_clause.as_ref()),
                    generic_map: p
                        .generic_map
                        .as_ref()
                        .map(|m| self.assoc_list(&m.list.items)),
                    decls,
                }
            }
            v::TypeDefinition::ProtectedBody(b) => TypeDef::ProtectedBody(self.decls(&b.decl)),
            v::TypeDefinition::Incomplete(_) | v::TypeDefinition::Subtype(_) => {
                self.err(span, "VHDL: internal: unexpected type definition");
                return None;
            }
        })
    }

    // ---- declarations ------------------------------------------------------------

    pub fn decls(&mut self, l: &[WithTokenSpan<v::Declaration>]) -> Vec<Decl> {
        let mut out = Vec::new();
        for d in l {
            if let Some(d) = self.decl(d) {
                out.push(d);
            }
        }
        out
    }

    fn object_decl(&mut self, o: &v::ObjectDeclaration, span: Span) -> Option<ObjectDecl> {
        let value = match &o.expression {
            Some(e) => Some(self.cond_expr(e)?),
            None => None,
        };
        Some(ObjectDecl {
            names: self.idents(&o.idents),
            ty: self.subtype_ind(&o.subtype_indication)?,
            value,
            span,
        })
    }

    fn decl(&mut self, d: &WithTokenSpan<v::Declaration>) -> Option<Decl> {
        let span = self.span(d.span);
        Some(match &d.item {
            v::Declaration::Object(o) => {
                let obj = self.object_decl(o, span)?;
                match o.class {
                    v::ObjectClass::Constant => Decl::Constant(obj),
                    v::ObjectClass::Signal => Decl::Signal {
                        obj,
                        kind: o.signal_kind.map(|k| match k {
                            v::SignalKind::Register => SignalKind::Register,
                            v::SignalKind::Bus => SignalKind::Bus,
                        }),
                    },
                    v::ObjectClass::Variable => Decl::Variable { obj, shared: false },
                    v::ObjectClass::SharedVariable => Decl::Variable { obj, shared: true },
                }
            }
            v::Declaration::File(f) => {
                let open = match &f.file_name {
                    Some((_, name)) => Some(FileOpen {
                        kind: match &f.open_info {
                            Some((_, k)) => Some(self.expr(k)?),
                            None => None,
                        },
                        name: self.expr(name)?,
                    }),
                    None => None,
                };
                Decl::File {
                    names: self.idents(&f.idents),
                    ty: self.subtype_ind(&f.subtype_indication)?,
                    open,
                    span,
                }
            }
            v::Declaration::Type(t) => match &t.def {
                v::TypeDefinition::Incomplete(_) => Decl::Type(TypeDecl {
                    name: self.ident(&t.ident.tree),
                    def: None,
                    span,
                }),
                v::TypeDefinition::Subtype(s) => Decl::Subtype {
                    name: self.ident(&t.ident.tree),
                    ind: self.subtype_ind(s)?,
                    span,
                },
                def => Decl::Type(TypeDecl {
                    name: self.ident(&t.ident.tree),
                    def: Some(self.type_def(def, span.clone())?),
                    span,
                }),
            },
            v::Declaration::Component(c) => Decl::Component(ComponentDecl {
                name: self.ident(&c.ident.tree),
                generics: self.interface_list(c.generic_list.as_ref()),
                ports: self.interface_list(c.port_list.as_ref()),
                span,
            }),
            v::Declaration::Attribute(v::Attribute::Declaration(a)) => Decl::Attribute {
                name: self.ident(&a.ident.tree),
                mark: self.name(&a.type_mark)?,
                span,
            },
            v::Declaration::Attribute(v::Attribute::Specification(a)) => {
                let (entities, all_or_others) = match &a.entity_name {
                    v::EntityName::Name(tag) => {
                        let mut v = Vec::new();
                        if let v::Designator::Identifier(sym) = &tag.designator.item.item {
                            v.push(Ident {
                                name: fold(&latin1(&sym.name().bytes)),
                                span: self.tok_span(tag.designator.token),
                            });
                        }
                        (v, false)
                    }
                    v::EntityName::All | v::EntityName::Others => (Vec::new(), true),
                };
                Decl::AttributeSpec(AttributeSpec {
                    attr: self.ident(&a.ident.item),
                    entities,
                    all_or_others,
                    class: format!("{:?}", a.entity_class).to_ascii_lowercase(),
                    value: self.cond_expr(&a.expr)?,
                    span,
                })
            }
            v::Declaration::Alias(a) => {
                let d = &a.designator.tree;
                let name = match &d.item {
                    v::Designator::Identifier(sym) => Designator::Ident(Ident {
                        name: fold(&latin1(&sym.name().bytes)),
                        span: self.tok_span(d.token),
                    }),
                    v::Designator::OperatorSymbol(op) => {
                        Designator::Op(op_text(*op).to_string(), self.tok_span(d.token))
                    }
                    v::Designator::Character(c) => {
                        Designator::Op((*c as char).to_string(), self.tok_span(d.token))
                    }
                    v::Designator::Anonymous(_) => {
                        self.err(span, "VHDL: internal: anonymous alias");
                        return None;
                    }
                };
                let ty = match &a.subtype_indication {
                    Some(s) => Some(self.subtype_ind(s)?),
                    None => None,
                };
                let signature = match &a.signature {
                    Some(s) => Some(self.signature(&s.item)?),
                    None => None,
                };
                Decl::Alias {
                    name,
                    ty,
                    target: self.name(&a.name)?,
                    signature,
                    span,
                }
            }
            v::Declaration::SubprogramDeclaration(s) => {
                Decl::SubprogramDecl(self.subprogram_spec(&s.specification)?)
            }
            v::Declaration::SubprogramBody(b) => Decl::SubprogramBody(SubprogramBody {
                spec: self.subprogram_spec(&b.specification)?,
                decls: self.decls(&b.declarations),
                stmts: self.seq_stmts(&b.statements),
                span,
            }),
            v::Declaration::SubprogramInstantiation(i) => {
                if let Some(s) = &i.signature {
                    let ss = self.span(s.span);
                    self.unsupported(ss, "signatures in subprogram instantiations");
                }
                let spec_kind = match i.kind {
                    v::SubprogramKind::Function => SubprogramKind::Function {
                        pure: true,
                        ret: Name {
                            kind: NameKind::Simple(Ident {
                                name: String::new(),
                                span: span.clone(),
                            }),
                            span: span.clone(),
                        },
                    },
                    v::SubprogramKind::Procedure => SubprogramKind::Procedure,
                };
                Decl::SubprogramInst {
                    spec_kind,
                    name: self.ident(&i.ident.tree),
                    uninst: self.name(&i.subprogram_name)?,
                    generic_map: self.map_aspect(i.generic_map.as_ref()),
                    span,
                }
            }
            v::Declaration::Use(u) => Decl::Use(self.names(&u.name_list)),
            v::Declaration::Package(p) => Decl::PackageInst(Box::new(self.package_inst(p, span)?)),
            v::Declaration::Configuration(c) => Decl::ConfigSpec(ConfigSpec {
                spec: self.component_spec(&c.spec)?,
                binding: self.binding(&c.bind_ind)?,
                span,
            }),
            v::Declaration::Disconnection(d) => {
                let signals = match &d.signals {
                    v::GuardedSignalList::All => SignalList::All,
                    v::GuardedSignalList::Others => SignalList::Others,
                    v::GuardedSignalList::Names(ns) => {
                        let mut out = Vec::new();
                        for n in ns {
                            match self.name(n)?.kind {
                                NameKind::Simple(i) => out.push(i),
                                _ => {
                                    let s = self.span(n.span);
                                    self.err(s, "VHDL: a guarded signal name was expected");
                                    return None;
                                }
                            }
                        }
                        SignalList::Names(out)
                    }
                };
                Decl::Disconnect(DisconnectSpec {
                    signals,
                    mark: self.name(&d.type_mark)?,
                    after: self.expr(&d.after)?,
                    span,
                })
            }
            v::Declaration::View(_) => {
                self.unsupported(span, "a mode view declaration");
                return None;
            }
        })
    }

    fn signature(&mut self, s: &v::Signature) -> Option<Signature> {
        let (params, ret) = match s {
            v::Signature::Function(p, r) => (p, Some(r)),
            v::Signature::Procedure(p) => (p, None),
        };
        Some(Signature {
            params: self.names(params),
            ret: match ret {
                Some(r) => Some(self.name(r)?),
                None => None,
            },
        })
    }

    // ---- configurations --------------------------------------------------------------

    fn block_config(&mut self, b: &v::BlockConfiguration) -> Option<BlockConfig> {
        let span = self.has_span(b);
        if !b.use_clauses.is_empty() {
            self.unsupported(span.clone(), "this configuration item");
        }
        let mut items = Vec::new();
        for i in &b.items {
            match i {
                v::ConfigurationItem::Block(b) => items.extend(self.block_config(b).map(ConfigItem::Block)),
                v::ConfigurationItem::Component(c) => items.extend(
                    self.component_config(c)
                        .map(|c| ConfigItem::Component(Box::new(c))),
                ),
            }
        }
        Some(BlockConfig {
            spec: self.name(&b.block_spec)?,
            items,
            span,
        })
    }

    fn component_config(&mut self, c: &v::ComponentConfiguration) -> Option<ComponentConfig> {
        let span = self.has_span(c);
        let binding = match &c.bind_ind {
            Some(b) => Some(self.binding(b)?),
            None => None,
        };
        Some(ComponentConfig {
            spec: self.component_spec(&c.spec)?,
            binding,
            block: c.block_config.as_ref().and_then(|b| self.block_config(b)),
            span,
        })
    }

    fn component_spec(&mut self, c: &v::ComponentSpecification) -> Option<ComponentSpec> {
        let insts = match &c.instantiation_list {
            v::InstantiationList::All => InstList::All,
            v::InstantiationList::Others => InstList::Others,
            v::InstantiationList::Labels(l) => {
                InstList::Labels(l.iter().map(|i| self.ident(i)).collect())
            }
        };
        Some(ComponentSpec {
            insts,
            comp: self.name(&c.component_name)?,
        })
    }

    fn binding(&mut self, b: &v::BindingIndication) -> Option<BindingInd> {
        let span = self.has_span(b);
        let aspect = match &b.entity_aspect {
            None => None,
            Some(v::EntityAspect::Entity(n, arch)) => Some(EntityAspect::Entity(
                self.name(n)?,
                arch.as_ref().map(|a| self.ident(a)),
            )),
            Some(v::EntityAspect::Configuration(n)) => {
                Some(EntityAspect::Configuration(self.name(n)?))
            }
            Some(v::EntityAspect::Open) => Some(EntityAspect::Open),
        };
        Some(BindingInd {
            aspect,
            generic_map: self.map_aspect(b.generic_map.as_ref()),
            port_map: self.map_aspect(b.port_map.as_ref()),
            span,
        })
    }

    fn map_aspect(&mut self, m: Option<&v::MapAspect>) -> Vec<Assoc> {
        match m {
            Some(m) => self.assoc_list(&m.list.items),
            None => Vec::new(),
        }
    }

    fn assoc_list(&mut self, l: &[v::AssociationElement]) -> Vec<Assoc> {
        let mut out = Vec::new();
        for a in l {
            let formal = a.formal.as_ref().and_then(|f| self.name(f));
            let aspan = self.span(a.actual.span);
            let actual = match &a.actual.item {
                v::ActualPart::Open => Actual::Open(aspan.clone()),
                v::ActualPart::Expression(e) => {
                    let Some(e) = self.cond_expr_at(e, aspan.clone()) else {
                        continue;
                    };
                    Actual::Expr(e)
                }
            };
            let start = a.formal.as_ref().map_or(aspan.start, |f| self.span(f.span).start);
            out.push(Assoc {
                formal,
                actual,
                span: start..aspan.end,
            });
        }
        out
    }

    // ---- names -------------------------------------------------------------------

    pub fn name(&mut self, n: &WithTokenSpan<v::Name>) -> Option<Name> {
        let span = self.span(n.span);
        self.name_at(&n.item, span)
    }

    fn name_at(&mut self, n: &v::Name, span: Span) -> Option<Name> {
        let kind = match n {
            v::Name::Designator(d) => match &d.item {
                v::Designator::Identifier(s) => NameKind::Simple(Ident {
                    name: fold(&latin1(&s.name().bytes)),
                    span: span.clone(),
                }),
                v::Designator::OperatorSymbol(op) => NameKind::Op(op_text(*op).to_string()),
                v::Designator::Character(c) => NameKind::Char(*c),
                v::Designator::Anonymous(_) => {
                    self.err(span, "VHDL: internal: anonymous name");
                    return None;
                }
            },
            v::Name::Selected(prefix, suffix) => {
                let p = self.name(prefix)?;
                let ss = self.tok_span(suffix.token);
                let s = match &suffix.item.item {
                    v::Designator::Identifier(sym) => Suffix::Ident(Ident {
                        name: fold(&latin1(&sym.name().bytes)),
                        span: ss,
                    }),
                    v::Designator::Character(c) => Suffix::Char(*c, ss),
                    v::Designator::OperatorSymbol(op) => Suffix::Op(op_text(*op).to_string(), ss),
                    v::Designator::Anonymous(_) => {
                        self.err(ss, "VHDL: internal: anonymous name");
                        return None;
                    }
                };
                NameKind::Selected(Box::new(p), s)
            }
            v::Name::SelectedAll(prefix) => {
                let p = self.name(prefix)?;
                let all = span.end.saturating_sub(3)..span.end;
                NameKind::Selected(Box::new(p), Suffix::All(all))
            }
            v::Name::Slice(prefix, dr) => {
                let p = self.name(prefix)?;
                let rs = p.span.end..span.end;
                let e = self.discrete_range_expr(dr, rs.clone())?;
                NameKind::Call(
                    Box::new(p),
                    vec![Assoc {
                        formal: None,
                        actual: Actual::Expr(e),
                        span: rs,
                    }],
                )
            }
            v::Name::Attribute(a) => return self.attribute_name(a).map(|mut x| {
                x.span = span;
                x
            }),
            v::Name::CallOrIndexed(c) => {
                let p = self.name(&c.name)?;
                NameKind::Call(Box::new(p), self.assoc_list(&c.parameters.items))
            }
            v::Name::External(x) => {
                let class = match x.class {
                    v::ExternalObjectClass::Constant => ObjClass::Constant,
                    v::ExternalObjectClass::Signal => ObjClass::Signal,
                    v::ExternalObjectClass::Variable => ObjClass::Variable,
                };
                let ps = self.span(x.path.span);
                let path: String = self
                    .text_of(&ps)
                    .split_whitespace()
                    .collect::<String>()
                    .to_ascii_lowercase();
                NameKind::External {
                    class,
                    path,
                    ty: Box::new(self.subtype_ind(&x.subtype)?),
                }
            }
        };
        Some(Name { kind, span })
    }

    /// `p'attr` and `p'attr(e)`: the parameter of an attribute that takes
    /// one, else a call of the attribute's value.
    fn attribute_name(&mut self, a: &v::AttributeName) -> Option<Name> {
        let prefix = self.name(&a.name)?;
        if let Some(s) = &a.signature {
            let ss = self.span(s.span);
            self.unsupported(ss, "signatures in names");
        }
        let aspan = self.tok_span(a.attr.token);
        let attr = Ident {
            name: attr_text(&a.attr.item),
            span: aspan.clone(),
        };
        let start = prefix.span.start;
        match &a.expr {
            None => Some(Name {
                span: start..aspan.end,
                kind: NameKind::Attribute(Box::new(prefix), attr, None),
            }),
            Some(e) => {
                let ex = self.expr(e)?;
                let end = ex.span.end + 1;
                if takes_param(&attr.name) {
                    Some(Name {
                        span: start..end,
                        kind: NameKind::Attribute(Box::new(prefix), attr, Some(Box::new(ex))),
                    })
                } else {
                    let base = Name {
                        span: start..aspan.end,
                        kind: NameKind::Attribute(Box::new(prefix), attr, None),
                    };
                    let es = ex.span.clone();
                    Some(Name {
                        span: start..end,
                        kind: NameKind::Call(
                            Box::new(base),
                            vec![Assoc {
                                formal: None,
                                actual: Actual::Expr(ex),
                                span: es,
                            }],
                        ),
                    })
                }
            }
        }
    }

    // ---- expressions ---------------------------------------------------------------

    /// A conditional expression (VHDL-2019) where a plain expression is
    /// expected.
    fn cond_expr(&mut self, e: &WithTokenSpan<v::ConditionalExpression>) -> Option<Expr> {
        let span = self.span(e.span);
        self.cond_expr_at(&e.item, span)
    }

    fn cond_expr_at(&mut self, e: &v::ConditionalExpression, span: Span) -> Option<Expr> {
        match e {
            v::ConditionalExpression::Simple(x) => self.expr_at(x, span),
            // VHDL-2019 §9.1: `a when c1 else b when c2 else d`.
            v::ConditionalExpression::Conditional(c) => {
                let Some((last, _)) = &c.else_item else {
                    self.err(span, "VHDL: a conditional expression needs a final else");
                    return None;
                };
                let mut arms = Vec::new();
                for x in &c.conditionals {
                    arms.push((self.expr(&x.item)?, self.expr(&x.condition)?));
                }
                Some(Expr {
                    kind: ExprKind::Cond(arms, Box::new(self.expr(last)?)),
                    span,
                })
            }
        }
    }

    pub fn expr(&mut self, e: &WithTokenSpan<v::Expression>) -> Option<Expr> {
        let span = self.span(e.span);
        self.expr_at(&e.item, span)
    }

    fn expr_at(&mut self, e: &v::Expression, span: Span) -> Option<Expr> {
        let kind = match e {
            v::Expression::Binary(op, l, r) => {
                use v::Operator::*;
                let bop = match op.item.item {
                    Plus => BinOp::Add,
                    Minus => BinOp::Sub,
                    EQ => BinOp::Eq,
                    NE => BinOp::Ne,
                    LT => BinOp::Lt,
                    LTE => BinOp::Le,
                    GT => BinOp::Gt,
                    GTE => BinOp::Ge,
                    QueEQ => BinOp::MatchEq,
                    QueNE => BinOp::MatchNe,
                    QueLT => BinOp::MatchLt,
                    QueLTE => BinOp::MatchLe,
                    QueGT => BinOp::MatchGt,
                    QueGTE => BinOp::MatchGe,
                    Times => BinOp::Mul,
                    Pow => BinOp::Pow,
                    Div => BinOp::Div,
                    Concat => BinOp::Concat,
                    And => BinOp::And,
                    Or => BinOp::Or,
                    Nand => BinOp::Nand,
                    Nor => BinOp::Nor,
                    Xor => BinOp::Xor,
                    Xnor => BinOp::Xnor,
                    SLL => BinOp::Sll,
                    SRL => BinOp::Srl,
                    SLA => BinOp::Sla,
                    SRA => BinOp::Sra,
                    ROL => BinOp::Rol,
                    ROR => BinOp::Ror,
                    Mod => BinOp::Mod,
                    Rem => BinOp::Rem,
                    Abs | Not | QueQue => {
                        self.err(span, "VHDL: internal: unexpected binary operator");
                        return None;
                    }
                };
                ExprKind::Binary(bop, Box::new(self.expr(l)?), Box::new(self.expr(r)?))
            }
            v::Expression::Unary(op, x) => {
                use v::Operator::*;
                let uop = match op.item.item {
                    Plus => UnOp::Plus,
                    Minus => UnOp::Minus,
                    QueQue => UnOp::Cond,
                    Abs => UnOp::Abs,
                    Not => UnOp::Not,
                    And => UnOp::And,
                    Or => UnOp::Or,
                    Nand => UnOp::Nand,
                    Nor => UnOp::Nor,
                    Xor => UnOp::Xor,
                    Xnor => UnOp::Xnor,
                    _ => {
                        self.err(span, "VHDL: internal: unexpected unary operator");
                        return None;
                    }
                };
                ExprKind::Unary(uop, Box::new(self.expr(x)?))
            }
            v::Expression::Aggregate(items) => {
                let assocs = self.elem_assocs(items)?;
                match assocs.as_slice() {
                    [ElemAssoc { choices, value }] if choices.is_empty() => {
                        ExprKind::Paren(Box::new(value.clone()))
                    }
                    _ => ExprKind::Aggregate(assocs),
                }
            }
            v::Expression::Qualified(q) => {
                let mark = self.name(&q.type_mark)?;
                let inner = self.expr(&q.expr)?;
                let inner = match inner.kind {
                    ExprKind::Paren(_) | ExprKind::Aggregate(_) => inner,
                    _ => Expr {
                        span: inner.span.clone(),
                        kind: ExprKind::Paren(Box::new(inner)),
                    },
                };
                ExprKind::Qualified(mark, Box::new(inner))
            }
            v::Expression::Name(n) => {
                let nm = self.name_at(n, span.clone())?;
                match nm.kind {
                    // A bare operator symbol in an expression is a string
                    // literal.
                    NameKind::Op(s) => ExprKind::Lit(Literal::Str(s.bytes().collect())),
                    k => ExprKind::Name(Name {
                        kind: k,
                        span: nm.span,
                    }),
                }
            }
            v::Expression::Literal(l) => match l {
                v::Literal::Physical(p) => return Some(self.physical_literal(p, span)),
                l => ExprKind::Lit(self.literal(l, &span)?),
            },
            v::Expression::New(a) => match &a.item {
                v::Allocator::Qualified(q) => {
                    let qs = self.span(a.span);
                    let mark = self.name(&q.type_mark)?;
                    let inner = self.expr(&q.expr)?;
                    let inner = match inner.kind {
                        ExprKind::Paren(_) | ExprKind::Aggregate(_) => inner,
                        _ => Expr {
                            span: inner.span.clone(),
                            kind: ExprKind::Paren(Box::new(inner)),
                        },
                    };
                    ExprKind::New(Box::new(Expr {
                        span: qs,
                        kind: ExprKind::Qualified(mark, Box::new(inner)),
                    }))
                }
                v::Allocator::Subtype(s) => ExprKind::NewSubtype(Box::new(self.subtype_ind(s)?)),
            },
            v::Expression::Parenthesized(c) => {
                let cs = self.span(c.span);
                let inner = self.cond_expr_at(&c.item, cs)?;
                ExprKind::Paren(Box::new(inner))
            }
        };
        Some(Expr { kind, span })
    }

    fn literal(&mut self, l: &v::Literal, span: &Span) -> Option<Literal> {
        Some(match l {
            v::Literal::String(s) => Literal::Str(s.bytes.clone()),
            v::Literal::Character(c) => Literal::Char(*c),
            v::Literal::AbstractLiteral(a) => abstract_literal(a),
            v::Literal::BitString(b) => {
                let base = match b.base {
                    v::BaseSpecifier::B => "b",
                    v::BaseSpecifier::O => "o",
                    v::BaseSpecifier::X => "x",
                    v::BaseSpecifier::UB => "ub",
                    v::BaseSpecifier::UO => "uo",
                    v::BaseSpecifier::UX => "ux",
                    v::BaseSpecifier::SB => "sb",
                    v::BaseSpecifier::SO => "so",
                    v::BaseSpecifier::SX => "sx",
                    v::BaseSpecifier::D => "d",
                };
                let text = format!(
                    "{}{}\"{}\"",
                    b.length.map(|n| n.to_string()).unwrap_or_default(),
                    base,
                    latin1(&b.value.bytes)
                );
                match expand_bit_string(&text) {
                    Ok(v) => Literal::BitStr(v),
                    Err(m) => {
                        self.err(span.clone(), format!("VHDL: {}", m));
                        return None;
                    }
                }
            }
            v::Literal::Null => Literal::Null,
            v::Literal::Physical(_) => {
                self.err(span.clone(), "VHDL: internal: unexpected literal");
                return None;
            }
        })
    }

    fn physical_literal(&mut self, p: &v::PhysicalLiteral, span: Span) -> Expr {
        let unit = self.ident(&p.unit.item);
        Expr {
            kind: ExprKind::Lit(Literal::Physical(
                Box::new(abstract_literal(&p.value)),
                Name {
                    span: unit.span.clone(),
                    kind: NameKind::Simple(unit),
                },
            )),
            span,
        }
    }

    fn elem_assocs(&mut self, items: &[WithTokenSpan<v::ElementAssociation>]) -> Option<Vec<ElemAssoc>> {
        let mut out = Vec::new();
        for a in items {
            match &a.item {
                v::ElementAssociation::Positional(e) => out.push(ElemAssoc {
                    choices: Vec::new(),
                    value: self.expr(e)?,
                }),
                v::ElementAssociation::Named(cs, e) => out.push(ElemAssoc {
                    choices: self.choices(cs)?,
                    value: self.expr(e)?,
                }),
            }
        }
        Some(out)
    }

    fn choices(&mut self, cs: &[WithTokenSpan<v::Choice>]) -> Option<Vec<Choice>> {
        let mut out = Vec::new();
        for c in cs {
            let s = self.span(c.span);
            out.push(match &c.item {
                v::Choice::Others => Choice::Others(s),
                v::Choice::Expression(e) => Choice::Expr(self.expr_at(e, s)?),
                v::Choice::DiscreteRange(d) => Choice::Range(self.discrete_range(d)?),
            });
        }
        Some(out)
    }

    // ---- concurrent statements --------------------------------------------------------

    pub fn conc_stmts(&mut self, l: &[v::LabeledConcurrentStatement]) -> Vec<ConcStmt> {
        let mut out = Vec::new();
        for s in l {
            if let Some(s) = self.conc_stmt(s) {
                out.push(s);
            }
        }
        out
    }

    fn label(&self, l: &v::WithDecl<Option<v::Ident>>) -> Option<Ident> {
        l.tree.as_ref().map(|i| self.ident(i))
    }

    fn conc_stmt(&mut self, s: &v::LabeledConcurrentStatement) -> Option<ConcStmt> {
        let label = self.label(&s.label);
        let span = match &s.label.tree {
            Some(l) => self.span2(l.token, s.statement.span.end_token),
            None => self.span(s.statement.span),
        };
        let kind = match &s.statement.item {
            v::ConcurrentStatement::Process(p) => ConcKind::Process {
                postponed: p.postponed,
                sens: p.sensitivity_list.as_ref().map(|l| match &l.item {
                    v::SensitivityList::All => Sensitivity::All,
                    v::SensitivityList::Names(ns) => Sensitivity::List(self.names(ns)),
                }),
                decls: self.decls(&p.decl),
                stmts: self.seq_stmts(&p.statements),
            },
            v::ConcurrentStatement::Assignment(a) => ConcKind::SignalAssign {
                postponed: a.postponed,
                guarded: a.guarded,
                target: self.target(&a.assignment.target)?,
                delay: self.delay(a.assignment.delay_mechanism.as_ref()),
                rhs: self.rhs_waveform(&a.assignment.rhs)?,
            },
            v::ConcurrentStatement::Assert(a) => {
                let (cond, report, severity) = self.assertion(&a.statement)?;
                ConcKind::Assert {
                    postponed: a.postponed,
                    cond,
                    report,
                    severity,
                }
            }
            v::ConcurrentStatement::ProcedureCall(c) => ConcKind::ProcCall {
                postponed: c.postponed,
                call: self.call(&c.call)?,
            },
            v::ConcurrentStatement::Instance(i) => {
                let unit = match &i.unit {
                    v::InstantiatedUnit::Entity(n, arch) => {
                        InstUnit::Entity(self.name(n)?, arch.as_ref().map(|a| self.ident(&a.item)))
                    }
                    v::InstantiatedUnit::Component(n) => InstUnit::Component(self.name(n)?),
                    v::InstantiatedUnit::Configuration(n) => {
                        InstUnit::Configuration(self.name(n)?)
                    }
                };
                ConcKind::Instance {
                    unit,
                    generic_map: self.map_aspect(i.generic_map.as_ref()),
                    port_map: self.map_aspect(i.port_map.as_ref()),
                }
            }
            v::ConcurrentStatement::Block(b) => {
                let guard = match &b.guard_condition {
                    Some(g) => Some(self.expr(g)?),
                    None => None,
                };
                ConcKind::Block {
                    guard,
                    generics: self.interface_list(b.header.generic_clause.as_ref()),
                    generic_map: self.map_aspect(b.header.generic_map.as_ref()),
                    ports: self.interface_list(b.header.port_clause.as_ref()),
                    port_map: self.map_aspect(b.header.port_map.as_ref()),
                    decls: self.decls(&b.decl),
                    stmts: self.conc_stmts(&b.statements),
                }
            }
            v::ConcurrentStatement::ForGenerate(g) => {
                let (decls, stmts) = self.generate_body(&g.body);
                ConcKind::ForGenerate {
                    param: self.ident(&g.index_name.tree),
                    range: self.discrete_range(&g.discrete_range)?,
                    decls,
                    stmts,
                }
            }
            v::ConcurrentStatement::IfGenerate(g) => {
                let mut branches = Vec::new();
                for c in &g.conds.conditionals {
                    let cond = self.expr(&c.condition);
                    let (decls, stmts) = self.generate_body(&c.item);
                    branches.push(GenerateBranch {
                        alt_label: c.item.alternative_label.as_ref().map(|l| self.ident(&l.tree)),
                        cond,
                        choices: Vec::new(),
                        decls,
                        stmts,
                    });
                }
                if let Some((body, _)) = &g.conds.else_item {
                    let (decls, stmts) = self.generate_body(body);
                    branches.push(GenerateBranch {
                        alt_label: body.alternative_label.as_ref().map(|l| self.ident(&l.tree)),
                        cond: None,
                        choices: Vec::new(),
                        decls,
                        stmts,
                    });
                }
                ConcKind::IfGenerate(branches)
            }
            v::ConcurrentStatement::CaseGenerate(g) => {
                let mut branches = Vec::new();
                for alt in &g.sels.alternatives {
                    let choices = self.choices(&alt.choices)?;
                    let (decls, stmts) = self.generate_body(&alt.item);
                    branches.push(GenerateBranch {
                        alt_label: alt.item.alternative_label.as_ref().map(|l| self.ident(&l.tree)),
                        cond: None,
                        choices,
                        decls,
                        stmts,
                    });
                }
                ConcKind::CaseGenerate {
                    expr: self.expr(&g.sels.expression)?,
                    branches,
                }
            }
        };
        Some(ConcStmt { label, kind, span })
    }

    fn generate_body(&mut self, b: &v::GenerateBody) -> (Vec<Decl>, Vec<ConcStmt>) {
        let decls = match &b.decl {
            Some((d, _)) => self.decls(d),
            None => Vec::new(),
        };
        (decls, self.conc_stmts(&b.statements))
    }

    /// A procedure call: the name, with its parameters when it has some.
    fn call(&mut self, c: &WithTokenSpan<v::CallOrIndexed>) -> Option<Name> {
        let span = self.span(c.span);
        if c.item.parameters.items.is_empty() {
            let mut n = self.name(&c.item.name)?;
            n.span = span;
            return Some(n);
        }
        let p = self.name(&c.item.name)?;
        Some(Name {
            kind: NameKind::Call(Box::new(p), self.assoc_list(&c.item.parameters.items)),
            span,
        })
    }

    fn target(&mut self, t: &WithTokenSpan<v::Target>) -> Option<Target> {
        let span = self.span(t.span);
        Some(match &t.item {
            v::Target::Name(n) => Target::Name(self.name_at(n, span)?),
            v::Target::Aggregate(a) => Target::Aggregate(self.elem_assocs(a)?, span),
        })
    }

    fn delay(&mut self, d: Option<&WithTokenSpan<v::DelayMechanism>>) -> Option<DelayMech> {
        match &d?.item {
            v::DelayMechanism::Transport => Some(DelayMech::Transport),
            v::DelayMechanism::Inertial { reject } => Some(DelayMech::Inertial(
                reject.as_ref().and_then(|r| self.expr(r)),
            )),
        }
    }

    fn waveform(&mut self, w: &v::Waveform) -> Option<Waveform> {
        Some(match w {
            v::Waveform::Unaffected(t) => Waveform::Unaffected(self.tok_span(*t)),
            v::Waveform::Elements(els) => {
                let mut out = Vec::new();
                for e in els {
                    let value = self.expr(&e.value)?;
                    let value = match value.kind {
                        ExprKind::Lit(Literal::Null) => None,
                        _ => Some(value),
                    };
                    let after = match &e.after {
                        Some(a) => Some(self.expr(a)?),
                        None => None,
                    };
                    out.push(WaveElem {
                        value,
                        after,
                        span: self.has_span(e),
                    });
                }
                Waveform::Elems(out)
            }
        })
    }

    fn rhs_waveform(&mut self, r: &v::AssignmentRightHand<v::Waveform>) -> Option<AssignRhs<Waveform>> {
        Some(match r {
            v::AssignmentRightHand::Simple(w) => AssignRhs::Simple(self.waveform(w)?),
            v::AssignmentRightHand::Conditional(c) => {
                let mut out = Vec::new();
                for x in &c.conditionals {
                    out.push((self.waveform(&x.item)?, self.expr(&x.condition)));
                }
                if let Some((w, _)) = &c.else_item {
                    out.push((self.waveform(w)?, None));
                }
                AssignRhs::Cond(out)
            }
            v::AssignmentRightHand::Selected(s) => {
                let mut items = Vec::new();
                for alt in &s.alternatives {
                    items.push((self.waveform(&alt.item)?, self.choices(&alt.choices)?));
                }
                AssignRhs::Select {
                    expr: self.expr(&s.expression)?,
                    matching: s.is_matching,
                    items,
                }
            }
        })
    }

    fn rhs_expr(
        &mut self,
        r: &v::AssignmentRightHand<WithTokenSpan<v::Expression>>,
    ) -> Option<AssignRhs<Expr>> {
        Some(match r {
            v::AssignmentRightHand::Simple(e) => AssignRhs::Simple(self.expr(e)?),
            v::AssignmentRightHand::Conditional(c) => {
                let mut out = Vec::new();
                for x in &c.conditionals {
                    out.push((self.expr(&x.item)?, self.expr(&x.condition)));
                }
                if let Some((e, _)) = &c.else_item {
                    out.push((self.expr(e)?, None));
                }
                AssignRhs::Cond(out)
            }
            v::AssignmentRightHand::Selected(s) => {
                let mut items = Vec::new();
                for alt in &s.alternatives {
                    items.push((self.expr(&alt.item)?, self.choices(&alt.choices)?));
                }
                AssignRhs::Select {
                    expr: self.expr(&s.expression)?,
                    matching: s.is_matching,
                    items,
                }
            }
        })
    }

    fn assertion(&mut self, a: &v::AssertStatement) -> Option<(Expr, Option<Expr>, Option<Expr>)> {
        let report = match &a.report {
            Some(r) => Some(self.expr(r)?),
            None => None,
        };
        let severity = match &a.severity {
            Some(s) => Some(self.expr(s)?),
            None => None,
        };
        Some((self.expr(&a.condition)?, report, severity))
    }

    // ---- sequential statements -----------------------------------------------------

    pub fn seq_stmts(&mut self, l: &[v::LabeledSequentialStatement]) -> Vec<SeqStmt> {
        let mut out = Vec::new();
        for s in l {
            if let Some(s) = self.seq_stmt(s) {
                out.push(s);
            }
        }
        out
    }

    fn seq_stmt(&mut self, s: &v::LabeledSequentialStatement) -> Option<SeqStmt> {
        let label = self.label(&s.label);
        let span = match &s.label.tree {
            Some(l) => self.span2(l.token, s.statement.span.end_token),
            None => self.span(s.statement.span),
        };
        let kind = match &s.statement.item {
            v::SequentialStatement::Wait(w) => SeqKind::Wait {
                on: w
                    .sensitivity_clause
                    .as_ref()
                    .map(|l| self.names(l))
                    .unwrap_or_default(),
                until: match &w.condition_clause {
                    Some(c) => Some(self.expr(c)?),
                    None => None,
                },
                timeout: match &w.timeout_clause {
                    Some(t) => Some(self.expr(t)?),
                    None => None,
                },
            },
            v::SequentialStatement::Assert(a) => {
                let (cond, report, severity) = self.assertion(a)?;
                SeqKind::Assert {
                    cond,
                    report,
                    severity,
                }
            }
            v::SequentialStatement::Report(r) => SeqKind::Report {
                msg: self.expr(&r.report)?,
                severity: match &r.severity {
                    Some(x) => Some(self.expr(x)?),
                    None => None,
                },
            },
            v::SequentialStatement::VariableAssignment(a) => SeqKind::VarAssign {
                target: self.target(&a.target)?,
                rhs: self.rhs_expr(&a.rhs)?,
            },
            v::SequentialStatement::SignalAssignment(a) => SeqKind::SignalAssign {
                target: self.target(&a.target)?,
                delay: self.delay(a.delay_mechanism.as_ref()),
                rhs: self.rhs_waveform(&a.rhs)?,
            },
            v::SequentialStatement::SignalForceAssignment(a) => SeqKind::Force {
                target: self.target(&a.target)?,
                mode: force_mode(&a.force_mode),
                rhs: self.rhs_expr(&a.rhs)?,
            },
            v::SequentialStatement::SignalReleaseAssignment(a) => SeqKind::Release {
                target: self.target(&a.target)?,
                mode: force_mode(&a.force_mode),
            },
            v::SequentialStatement::ProcedureCall(c) => SeqKind::ProcCall(self.call(c)?),
            v::SequentialStatement::If(i) => {
                let mut branches = Vec::new();
                for c in &i.conds.conditionals {
                    branches.push((self.expr(&c.condition)?, self.seq_stmts(&c.item)));
                }
                SeqKind::If {
                    branches,
                    else_branch: i.conds.else_item.as_ref().map(|(b, _)| self.seq_stmts(b)),
                }
            }
            v::SequentialStatement::Case(c) => {
                let mut alts = Vec::new();
                for alt in &c.alternatives {
                    alts.push((self.choices(&alt.choices)?, self.seq_stmts(&alt.item)));
                }
                SeqKind::Case {
                    matching: c.is_matching,
                    expr: self.expr(&c.expression)?,
                    alts,
                }
            }
            v::SequentialStatement::Loop(l) => SeqKind::Loop {
                scheme: match &l.iteration_scheme {
                    None => LoopScheme::Plain,
                    Some(v::IterationScheme::While(c)) => LoopScheme::While(self.expr(c)?),
                    Some(v::IterationScheme::For(i, r)) => {
                        LoopScheme::For(self.ident(&i.tree), self.discrete_range(r)?)
                    }
                },
                body: self.seq_stmts(&l.statements),
            },
            v::SequentialStatement::Next(n) => SeqKind::Next {
                label: n.loop_label.as_ref().map(|l| self.ident(&l.item)),
                cond: match &n.condition {
                    Some(c) => Some(self.expr(c)?),
                    None => None,
                },
            },
            v::SequentialStatement::Exit(n) => SeqKind::Exit {
                label: n.loop_label.as_ref().map(|l| self.ident(&l.item)),
                cond: match &n.condition {
                    Some(c) => Some(self.expr(c)?),
                    None => None,
                },
            },
            v::SequentialStatement::Return(r) => self.return_stmt(r, &span)?,
            v::SequentialStatement::Null => SeqKind::Null,
            v::SequentialStatement::Block(b) => SeqKind::Block {
                decls: self.decls(&b.decl),
                stmts: self.seq_stmts(&b.statements),
            },
        };
        Some(SeqStmt { label, kind, span })
    }
}

impl Converter<'_> {
    /// A return statement. VHDL-2019's `return when c;` and
    /// `return a when c1 else b when c2 [else unaffected];` (§10.13) are
    /// `if` statements around plain returns; an `unaffected` arm returns
    /// nothing and the execution continues.
    fn return_stmt(&mut self, r: &v::ReturnStatement, span: &Span) -> Option<SeqKind> {
        let ret = |value: Option<Expr>| {
            vec![SeqStmt {
                label: None,
                kind: SeqKind::Return(value),
                span: span.clone(),
            }]
        };
        if let Some(c) = &r.condition {
            return Some(SeqKind::If {
                branches: vec![(self.expr(c)?, ret(None))],
                else_branch: None,
            });
        }
        if let Some(cs) = &r.conditionals {
            let mut branches = Vec::new();
            for x in &cs.conditionals {
                let value = match &x.item {
                    Some(e) => Some(self.expr(e)?),
                    None => None,
                };
                let body = match value {
                    Some(v) => ret(Some(v)),
                    None => Vec::new(),
                };
                branches.push((self.expr(&x.condition)?, body));
            }
            let else_branch = match &cs.else_item {
                Some((Some(e), _)) => Some(ret(Some(self.expr(e)?))),
                _ => None,
            };
            return Some(SeqKind::If {
                branches,
                else_branch,
            });
        }
        Some(SeqKind::Return(match &r.expression {
            Some(e) => Some(self.expr(e)?),
            None => None,
        }))
    }
}

/// A range as an expression (a slice, an index constraint).
fn range_expr(r: RangeExpr, span: Span) -> Expr {
    match r {
        RangeExpr::Attr(n) => Expr {
            kind: ExprKind::Name(n),
            span,
        },
        r => Expr {
            kind: ExprKind::Range(Box::new(r)),
            span,
        },
    }
}

fn abstract_literal(a: &v::AbstractLiteral) -> Literal {
    match a {
        v::AbstractLiteral::Integer(i) => Literal::Int(*i as i128),
        v::AbstractLiteral::Real(r) => Literal::Real(*r),
    }
}

/// Expand a bit string literal (§15.8) to its string of characters, e.g.
/// `x"A"` → `"1010"`, `8x"F"` → `"00001111"`, `b"1_0"` → `"10"`.
pub fn expand_bit_string(s: &str) -> Result<Vec<u8>, String> {
    let q = s.find('"').ok_or("invalid bit string literal")?;
    let (prefix, rest) = s.split_at(q);
    let body = &rest[1..rest.len() - 1];
    let prefix = prefix.to_ascii_lowercase();
    let size_end = prefix
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(prefix.len());
    let size: Option<usize> = if size_end > 0 {
        Some(
            prefix[..size_end]
                .parse()
                .map_err(|_| "invalid bit string length")?,
        )
    } else {
        None
    };
    let base = &prefix[size_end..];
    let (signed, base) = match base.strip_prefix('s') {
        Some(b) => (Some(true), b),
        None => match base.strip_prefix('u') {
            Some(b) => (Some(false), b),
            None => (None, base),
        },
    };
    let body: Vec<u8> = body.bytes().filter(|&b| b != b'_').collect();
    let mut bits = Vec::new();
    match base {
        "b" => bits = body,
        "o" | "x" => {
            let width = if base == "o" { 3 } else { 4 };
            for c in body {
                match (c as char).to_digit(if base == "o" { 8 } else { 16 }) {
                    Some(v) => {
                        for i in (0..width).rev() {
                            bits.push(if (v >> i) & 1 == 1 { b'1' } else { b'0' });
                        }
                    }
                    None => bits.extend(std::iter::repeat_n(c, width)),
                }
            }
        }
        "d" => {
            let s = String::from_utf8_lossy(&body).to_string();
            let mut v: u128 = s.parse().map_err(|_| "invalid decimal bit string")?;
            let mut out = Vec::new();
            while v > 0 {
                out.push(if v & 1 == 1 { b'1' } else { b'0' });
                v >>= 1;
            }
            out.reverse();
            bits = out;
        }
        _ => return Err("invalid bit string base".into()),
    }
    if let Some(n) = size {
        if n < bits.len() {
            let drop = bits.len() - n;
            bits = bits[drop..].to_vec();
        } else if n > bits.len() {
            let fill = if signed == Some(true) {
                *bits.first().unwrap_or(&b'0')
            } else {
                b'0'
            };
            let mut v = vec![fill; n - bits.len()];
            v.extend(bits);
            bits = v;
        }
    }
    Ok(bits)
}
