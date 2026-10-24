//! Concrete syntax tree (vhdl_syntax) → xezim's VHDL AST (`ast`).
//!
//! The conversion walks the untyped tree by node and token kind. A node it
//! does not know becomes an error at its location ("not supported yet"),
//! never a silently dropped construct.

use vhdl_syntax::syntax::node::{SyntaxNode, SyntaxToken};
use vhdl_syntax::syntax::{NodeKind as K, SyntaxElement};
use vhdl_syntax::tokens::TokenKind as T;

use super::Diagnostic;
use crate::vhdl::ast::*;

type N = SyntaxNode;
type Tk = SyntaxToken;

pub struct Converter {
    pub errors: Vec<Diagnostic>,
}

// ---- tree helpers -------------------------------------------------------------

fn nodes(n: &N) -> Vec<N> {
    n.children().collect()
}

fn elems(n: &N) -> Vec<SyntaxElement> {
    n.children_with_tokens().collect()
}

fn toks(n: &N) -> Vec<Tk> {
    n.children_with_tokens()
        .filter_map(|c| match c {
            SyntaxElement::Token(t) => Some(t),
            SyntaxElement::Node(_) => None,
        })
        .collect()
}

/// The first child node that is not a statement label.
fn first_node(n: &N) -> Option<N> {
    n.children().find(|c| c.kind() != K::StmtLabel)
}

fn child(n: &N, k: K) -> Option<N> {
    n.children().find(|c| c.kind() == k)
}

fn childs(n: &N, k: K) -> Vec<N> {
    n.children().filter(|c| c.kind() == k).collect()
}

fn text(t: &Tk) -> String {
    t.text().to_string()
}

/// The keyword a token is, lower case.
fn kw(t: &Tk) -> Option<String> {
    match t.kind() {
        T::Keyword(_) => Some(text(t).to_ascii_lowercase()),
        _ => None,
    }
}

fn has_kw(n: &N, k: &str) -> bool {
    toks(n).iter().any(|t| kw(t).as_deref() == Some(k))
}

fn tok(n: &N, k: T) -> Option<Tk> {
    toks(n).into_iter().find(|t| t.kind() == k)
}

/// The source span without leading/trailing trivia.
pub fn span(n: &N) -> Span {
    match (n.first_token(), n.last_token()) {
        (Some(f), Some(l)) => f.text_range().start..l.text_range().end,
        _ => n.range(),
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

fn ident(t: &Tk) -> Ident {
    Ident {
        name: fold(&text(t)),
        span: t.text_range(),
    }
}

fn first_ident(n: &N) -> Option<Ident> {
    tok(n, T::Identifier).map(|t| ident(&t))
}

fn idents(n: &N) -> Vec<Ident> {
    toks(n)
        .iter()
        .filter(|t| t.kind() == T::Identifier)
        .map(ident)
        .collect()
}

/// Latin-1 bytes of a token's text.
fn bytes(t: &Tk) -> Vec<u8> {
    t.text()
        .to_string()
        .chars()
        .map(|c| c as u32 as u8)
        .collect()
}

/// `"ab""c"` → `ab"c`.
fn string_value(raw: &[u8]) -> Vec<u8> {
    let q = raw[0];
    let inner = &raw[1..raw.len().saturating_sub(1)];
    let mut out = Vec::with_capacity(inner.len());
    let mut i = 0;
    while i < inner.len() {
        out.push(inner[i]);
        if inner[i] == q && inner.get(i + 1) == Some(&q) {
            i += 1;
        }
        i += 1;
    }
    out
}

impl Converter {
    pub fn new() -> Self {
        Converter { errors: Vec::new() }
    }

    fn err(&mut self, s: Span, msg: impl Into<String>) {
        self.errors.push(Diagnostic {
            span: s,
            message: msg.into(),
        });
    }

    fn unsupported(&mut self, n: &N, what: &str) {
        self.err(span(n), format!("VHDL: {} is not supported yet", what));
    }

    fn unexpected(&mut self, n: &N) {
        self.err(
            span(n),
            format!("VHDL: internal: unexpected syntax ({:?})", n.kind()),
        );
    }

    // ---- design units -------------------------------------------------------

    pub fn design_file(&mut self, root: &N) -> DesignFile {
        let mut units = Vec::new();
        for du in childs(root, K::DesignUnit) {
            if let Some(u) = self.design_unit(&du) {
                units.push(u);
            }
        }
        DesignFile { units }
    }

    fn design_unit(&mut self, du: &N) -> Option<DesignUnit> {
        let context = child(du, K::ContextClause)
            .map(|c| self.context_items(&c))
            .unwrap_or_default();
        let lu = nodes(du)
            .into_iter()
            .find(|c| c.kind() != K::ContextClause)?;
        let unit = self.library_unit(&lu)?;
        Some(DesignUnit {
            context,
            unit,
            span: span(du),
        })
    }

    fn context_items(&mut self, n: &N) -> Vec<ContextItem> {
        let mut out = Vec::new();
        for c in nodes(n) {
            match c.kind() {
                K::LibraryClause => {
                    let names = child(&c, K::LogicalNameList)
                        .map(|l| idents(&l))
                        .unwrap_or_default();
                    out.push(ContextItem::Library(names));
                }
                K::UseClauseContextItem | K::UseClauseDeclaration => {
                    if let Some(u) = child(&c, K::UseClause) {
                        out.push(ContextItem::Use(self.name_list(&u)));
                    }
                }
                K::UseClause => out.push(ContextItem::Use(self.name_list(&c))),
                K::ContextReference => out.push(ContextItem::Context(self.name_list(&c))),
                _ => self.unexpected(&c),
            }
        }
        out
    }

    fn name_list(&mut self, n: &N) -> Vec<Name> {
        let list = child(n, K::NameList).unwrap_or_else(|| n.clone());
        childs(&list, K::Name)
            .iter()
            .filter_map(|x| self.name(x))
            .collect()
    }

    fn library_unit(&mut self, n: &N) -> Option<LibraryUnit> {
        Some(match n.kind() {
            K::EntityDeclaration => LibraryUnit::Entity(self.entity(n)?),
            K::ArchitectureBody => LibraryUnit::Architecture(self.architecture(n)?),
            K::PrimaryUnitPackageDeclaration => {
                let p = child(n, K::PackageDeclaration)?;
                LibraryUnit::Package(self.package(&p)?)
            }
            K::PackageDeclaration => LibraryUnit::Package(self.package(n)?),
            K::SecondaryUnitPackageBody => {
                let p = child(n, K::PackageBody)?;
                LibraryUnit::PackageBody(self.package_body(&p)?)
            }
            K::PackageBody => LibraryUnit::PackageBody(self.package_body(n)?),
            K::PackageInstantiationDeclarationPrimaryUnit => {
                let p = child(n, K::PackageInstantiationDeclaration)?;
                LibraryUnit::PackageInst(self.package_inst(&p)?)
            }
            K::ConfigurationDeclaration => {
                let pre = child(n, K::ConfigurationDeclarationPreamble)?;
                LibraryUnit::Configuration(ConfigDecl {
                    name: first_ident(&pre)?,
                    entity: self.name(&child(&pre, K::Name)?)?,
                    span: span(n),
                })
            }
            K::ContextDeclaration => {
                let pre = child(n, K::ContextDeclarationPreamble)?;
                let items = child(n, K::ContextClause)
                    .map(|c| self.context_items(&c))
                    .unwrap_or_default();
                LibraryUnit::Context(ContextDecl {
                    name: first_ident(&pre)?,
                    items,
                })
            }
            _ => {
                self.unsupported(n, "this design unit");
                return None;
            }
        })
    }

    fn entity(&mut self, n: &N) -> Option<EntityDecl> {
        let pre = child(n, K::EntityDeclarationPreamble)?;
        let header = child(n, K::EntityHeader);
        let generics = header
            .as_ref()
            .and_then(|h| child(h, K::GenericClause))
            .map(|g| self.interface_clause(&g))
            .unwrap_or_default();
        let ports = header
            .as_ref()
            .and_then(|h| child(h, K::PortClause))
            .map(|g| self.interface_clause(&g))
            .unwrap_or_default();
        let decls = child(n, K::EntityDeclarativePart)
            .map(|d| self.decls(&d))
            .unwrap_or_default();
        let stmts = child(n, K::EntityStatements)
            .or_else(|| child(n, K::EntityStatementPart))
            .map(|s| self.conc_stmts(&s))
            .unwrap_or_default();
        Some(EntityDecl {
            name: first_ident(&pre)?,
            generics,
            ports,
            decls,
            stmts,
        })
    }

    fn architecture(&mut self, n: &N) -> Option<ArchBody> {
        let pre = child(n, K::ArchitecturePreamble)?;
        let entity = child(&pre, K::Name)
            .and_then(|x| self.name(&x))
            .and_then(|x| match x.kind {
                NameKind::Simple(i) => Some(i),
                _ => None,
            })?;
        Some(ArchBody {
            name: first_ident(&pre)?,
            entity,
            decls: child(n, K::ArchitectureDeclarativePart)
                .map(|d| self.decls(&d))
                .unwrap_or_default(),
            stmts: child(n, K::ArchitectureStatementPart)
                .map(|s| self.conc_stmts(&s))
                .unwrap_or_default(),
        })
    }

    fn package(&mut self, n: &N) -> Option<PackageDecl> {
        let pre = child(n, K::PackagePreamble)?;
        let header = child(n, K::PackageHeader);
        let generics = header
            .as_ref()
            .and_then(|h| child(h, K::GenericClause))
            .map(|g| self.interface_clause(&g))
            .unwrap_or_default();
        let generic_map = header
            .as_ref()
            .and_then(|h| child(h, K::GenericMapAspect))
            .map(|g| self.map_aspect(&g));
        Some(PackageDecl {
            name: first_ident(&pre)?,
            generics,
            generic_map,
            decls: child(n, K::PackageDeclarativePart)
                .map(|d| self.decls(&d))
                .unwrap_or_default(),
            span: span(n),
        })
    }

    fn package_body(&mut self, n: &N) -> Option<PackageBody> {
        let pre = child(n, K::PackageBodyPreamble)?;
        Some(PackageBody {
            name: first_ident(&pre)?,
            decls: child(n, K::PackageBodyDeclarativePart)
                .map(|d| self.decls(&d))
                .unwrap_or_default(),
            span: span(n),
        })
    }

    fn package_inst(&mut self, n: &N) -> Option<PackageInst> {
        let pre = child(n, K::PackageInstantiationPreamble)?;
        Some(PackageInst {
            name: first_ident(&pre)?,
            package: self.name(&child(&pre, K::Name)?)?,
            generic_map: child(n, K::GenericMapAspect)
                .map(|g| self.map_aspect(&g))
                .unwrap_or_default(),
            span: span(n),
        })
    }

    // ---- interfaces ---------------------------------------------------------

    fn interface_clause(&mut self, n: &N) -> Vec<InterfaceDecl> {
        child(n, K::InterfaceList)
            .or_else(|| {
                child(n, K::ParenthesizedInterfaceList).and_then(|p| child(&p, K::InterfaceList))
            })
            .map(|l| self.interface_list(&l))
            .unwrap_or_default()
    }

    fn interface_list(&mut self, n: &N) -> Vec<InterfaceDecl> {
        let mut out = Vec::new();
        for c in nodes(n) {
            match c.kind() {
                K::InterfaceObjectDeclaration | K::InterfaceFileDeclaration => {
                    if let Some(o) = self.interface_object(&c) {
                        out.push(InterfaceDecl::Object(o));
                    }
                }
                K::InterfaceIncompleteTypeDeclaration => {
                    if let Some(i) = first_ident(&c) {
                        out.push(InterfaceDecl::Type(i));
                    }
                }
                K::InterfaceSubprogramDeclaration => {
                    let spec = nodes(&c).into_iter().find(|x| {
                        matches!(
                            x.kind(),
                            K::InterfaceFunctionSpecification | K::InterfaceProcedureSpecification
                        )
                    });
                    if let Some(spec) = spec.and_then(|s| self.subprogram_spec(&s)) {
                        let default = child(&c, K::InterfaceSubprogramDefaultBox)
                            .map(|_| SubprogramDefault::Box)
                            .or_else(|| {
                                child(&c, K::InterfaceSubprogramDefaultName)
                                    .and_then(|d| child(&d, K::Name))
                                    .and_then(|d| self.name(&d))
                                    .map(SubprogramDefault::Name)
                            });
                        out.push(InterfaceDecl::Subprogram { spec, default });
                    }
                }
                K::InterfacePackageDeclaration => {
                    let pre = child(&c, K::InterfacePackageDeclarationPreamble);
                    let name = pre.as_ref().and_then(first_ident);
                    let package = pre
                        .as_ref()
                        .and_then(|p| child(p, K::Name))
                        .and_then(|p| self.name(&p));
                    if let (Some(name), Some(package)) = (name, package) {
                        out.push(InterfaceDecl::Package {
                            name,
                            package,
                            generic_map: None,
                            span: span(&c),
                        });
                    }
                }
                _ => self.unexpected(&c),
            }
        }
        out
    }

    fn interface_object(&mut self, n: &N) -> Option<InterfaceObject> {
        let mut class = None;
        let mut mode = None;
        let mut bus = false;
        for t in toks(n) {
            match kw(&t).as_deref() {
                Some("constant") => class = Some(ObjClass::Constant),
                Some("signal") => class = Some(ObjClass::Signal),
                Some("variable") => class = Some(ObjClass::Variable),
                Some("file") => class = Some(ObjClass::File),
                Some("in") => mode = Some(Mode::In),
                Some("out") => mode = Some(Mode::Out),
                Some("inout") => mode = Some(Mode::InOut),
                Some("buffer") => mode = Some(Mode::Buffer),
                Some("linkage") => mode = Some(Mode::Linkage),
                Some("bus") => bus = true,
                _ => {}
            }
        }
        Some(InterfaceObject {
            class,
            names: child(n, K::IdentifierList).map(|l| idents(&l))?,
            mode,
            ty: self.subtype_ind(&child(n, K::SubtypeIndication)?)?,
            bus,
            default: self.initial_value(n),
            span: span(n),
        })
    }

    fn initial_value(&mut self, n: &N) -> Option<Expr> {
        let iv = child(n, K::InitialValue)?;
        let e = nodes(&iv).into_iter().next()?;
        self.expr(&e)
    }

    // ---- subtype indications and types ----------------------------------------

    pub fn subtype_ind(&mut self, n: &N) -> Option<SubtypeInd> {
        let mut resolution = None;
        let mut mark = None;
        let mut constraint = None;
        for c in nodes(n) {
            match c.kind() {
                K::NameResolutionIndication => {
                    resolution = child(&c, K::Name)
                        .and_then(|x| self.name(&x))
                        .map(Resolution::Function);
                }
                K::ParenthesizedElementResolution => {
                    resolution = self.element_resolution(&c);
                }
                K::Name => {
                    let full = self.name(&c)?;
                    // Index/record constraints are parsed as call suffixes of
                    // the type mark.
                    let (m, groups) = split_paren_constraints(full);
                    if !groups.is_empty() {
                        constraint = Some(Constraint::Paren(groups));
                    }
                    if let Some(rc) = child(&c, K::RangeConstraint) {
                        constraint = self.range_constraint(&rc).map(Constraint::Range);
                    }
                    mark = Some(m);
                }
                K::RangeConstraint => {
                    constraint = self.range_constraint(&c).map(Constraint::Range);
                }
                _ => self.unexpected(&c),
            }
        }
        Some(SubtypeInd {
            resolution,
            mark: mark?,
            constraint,
            span: span(n),
        })
    }

    fn element_resolution(&mut self, n: &N) -> Option<Resolution> {
        let inner = nodes(n).into_iter().next()?;
        let r = match inner.kind() {
            K::ElementResolutionResolutionIndication => {
                let nr = child(&inner, K::NameResolutionIndication)?;
                Resolution::Function(self.name(&child(&nr, K::Name)?)?)
            }
            _ => {
                self.unsupported(&inner, "record element resolution");
                return None;
            }
        };
        Some(Resolution::Element(Box::new(r)))
    }

    fn range_constraint(&mut self, n: &N) -> Option<RangeExpr> {
        let e = nodes(n).into_iter().next()?;
        self.range_of(&e)
    }

    /// A range written as an expression: `a to b`, `a downto b`, or a
    /// range attribute name.
    fn range_of(&mut self, n: &N) -> Option<RangeExpr> {
        let e = self.expr(n)?;
        match e.kind {
            ExprKind::Range(r) => Some(*r),
            ExprKind::Name(nm) => Some(RangeExpr::Attr(nm)),
            _ => {
                self.err(e.span, "VHDL: a range was expected");
                None
            }
        }
    }

    fn type_def(&mut self, n: &N) -> Option<TypeDef> {
        Some(match n.kind() {
            K::EnumerationTypeDefinition => {
                let list = child(n, K::EnumerationList)?;
                let lits = toks(&list)
                    .iter()
                    .filter_map(|t| match t.kind() {
                        T::Identifier => Some(EnumLit::Ident(ident(t))),
                        T::CharacterLiteral => Some(EnumLit::Char(bytes(t)[1], t.text_range())),
                        _ => None,
                    })
                    .collect();
                TypeDef::Enum(lits)
            }
            K::NumericTypeDefinition => {
                let rc = child(n, K::RangeConstraint)?;
                if let Some(e) = nodes(&rc).into_iter().next()
                    && e.kind() == K::NameExpression
                    && self
                        .expr(&e)
                        .is_some_and(|x| matches!(&x.kind, ExprKind::Name(Name { kind: NameKind::Simple(i), .. }) if i.name == "implementation_defined"))
                {
                    return Some(TypeDef::ImplementationDefined);
                }
                TypeDef::Range(self.range_constraint(&rc)?)
            }
            K::PhysicalTypeDefinition => {
                let rc = child(n, K::RangeConstraint)?;
                let range = if nodes(&rc)
                    .first()
                    .and_then(|e| self.expr(e))
                    .is_some_and(|x| matches!(&x.kind, ExprKind::Name(Name { kind: NameKind::Simple(i), .. }) if i.name == "implementation_defined"))
                {
                    RangeExpr::Attr(Name {
                        kind: NameKind::Simple(Ident {
                            name: "implementation_defined".into(),
                            span: span(&rc),
                        }),
                        span: span(&rc),
                    })
                } else {
                    self.range_constraint(&rc)?
                };
                let units = child(n, K::UnitDeclarations)?;
                let primary =
                    child(&units, K::PrimaryUnitDeclaration).and_then(|p| first_ident(&p))?;
                let mut secondary = Vec::new();
                for s in childs(&units, K::SecondaryUnitDeclaration) {
                    let name = first_ident(&s)?;
                    let lit = child(&s, K::PhysicalLiteral)?;
                    let value = self.physical_literal(&lit)?;
                    secondary.push((name, value));
                }
                TypeDef::Physical {
                    range,
                    primary,
                    secondary,
                }
            }
            K::ConstrainedArrayDefinition => {
                let ic = child(n, K::IndexConstraint)?;
                let list = child(&ic, K::ExpressionList)?;
                let mut ranges = Vec::new();
                for e in nodes(&list) {
                    ranges.push(self.discrete_range(&e)?);
                }
                TypeDef::Array {
                    index: ArrayIndex::Constrained(ranges),
                    elem: self.subtype_ind(&child(n, K::SubtypeIndication)?)?,
                }
            }
            K::UnboundedArrayDefinition => {
                let list = child(n, K::IndexSubtypeDefinitionList)?;
                let mut marks = Vec::new();
                for d in childs(&list, K::IndexSubtypeDefinition) {
                    marks.push(self.name(&child(&d, K::Name)?)?);
                }
                TypeDef::Array {
                    index: ArrayIndex::Unbounded(marks),
                    elem: self.subtype_ind(&child(n, K::SubtypeIndication)?)?,
                }
            }
            K::RecordTypeDefinition => {
                let els = child(n, K::RecordElementDeclarations)?;
                let mut fields = Vec::new();
                for e in childs(&els, K::ElementDeclaration) {
                    let names = child(&e, K::IdentifierList).map(|l| idents(&l))?;
                    let ty = self.subtype_ind(&child(&e, K::SubtypeIndication)?)?;
                    fields.push((names, ty));
                }
                TypeDef::Record(fields)
            }
            K::AccessTypeDefinition => {
                TypeDef::Access(self.subtype_ind(&child(n, K::SubtypeIndication)?)?)
            }
            K::FileTypeDefinition => TypeDef::File(self.name(&child(n, K::Name)?)?),
            K::ProtectedTypeDeclaration => TypeDef::Protected(
                child(n, K::ProtectedTypeDeclarativePart)
                    .map(|d| self.decls(&d))
                    .unwrap_or_default(),
            ),
            K::ProtectedTypeBody => TypeDef::ProtectedBody(
                child(n, K::ProtectedTypeBodyDeclarativePart)
                    .map(|d| self.decls(&d))
                    .unwrap_or_default(),
            ),
            _ => {
                self.unsupported(n, "this type definition");
                return None;
            }
        })
    }

    fn discrete_range(&mut self, n: &N) -> Option<DiscreteRange> {
        let e = self.expr(n)?;
        Some(match e.kind {
            ExprKind::Range(r) => DiscreteRange::Range(*r),
            // A name: a subtype mark or a range attribute; sema decides.
            ExprKind::Name(nm) => match &nm.kind {
                NameKind::Attribute(..) => DiscreteRange::Range(RangeExpr::Attr(nm)),
                _ => DiscreteRange::Subtype(SubtypeInd {
                    resolution: None,
                    span: nm.span.clone(),
                    mark: nm,
                    constraint: None,
                }),
            },
            _ => {
                self.err(e.span, "VHDL: a discrete range was expected");
                return None;
            }
        })
    }

    // ---- declarations -------------------------------------------------------

    pub fn decls(&mut self, n: &N) -> Vec<Decl> {
        let mut out = Vec::new();
        for c in nodes(n) {
            if let Some(d) = self.decl(&c) {
                out.push(d);
            }
        }
        out
    }

    fn object_decl(&mut self, n: &N) -> Option<ObjectDecl> {
        Some(ObjectDecl {
            names: child(n, K::IdentifierList).map(|l| idents(&l))?,
            ty: self.subtype_ind(&child(n, K::SubtypeIndication)?)?,
            value: self.initial_value(n),
            span: span(n),
        })
    }

    fn decl(&mut self, n: &N) -> Option<Decl> {
        Some(match n.kind() {
            K::FullTypeDeclaration => {
                let name = first_ident(n)?;
                let defn = nodes(n).into_iter().next()?;
                Decl::Type(TypeDecl {
                    name,
                    def: Some(self.type_def(&defn)?),
                    span: span(n),
                })
            }
            K::IncompleteTypeDeclaration => Decl::Type(TypeDecl {
                name: first_ident(n)?,
                def: None,
                span: span(n),
            }),
            K::SubtypeDeclaration => Decl::Subtype {
                name: first_ident(n)?,
                ind: self.subtype_ind(&child(n, K::SubtypeIndication)?)?,
                span: span(n),
            },
            K::ConstantDeclaration => Decl::Constant(self.object_decl(n)?),
            K::SignalDeclaration => {
                let kind = if has_kw(n, "register") {
                    Some(SignalKind::Register)
                } else if has_kw(n, "bus") {
                    Some(SignalKind::Bus)
                } else {
                    None
                };
                Decl::Signal {
                    obj: self.object_decl(n)?,
                    kind,
                }
            }
            K::VariableDeclaration => Decl::Variable {
                shared: has_kw(n, "shared"),
                obj: self.object_decl(n)?,
            },
            K::FileDeclaration => {
                let open = match child(n, K::FileOpenInformation) {
                    Some(fo) => {
                        let kind = child(&fo, K::FileOpenKind)
                            .and_then(|k| nodes(&k).into_iter().last())
                            .and_then(|e| self.expr(&e));
                        let name_e = nodes(&fo)
                            .into_iter()
                            .filter(|x| x.kind() != K::FileOpenKind)
                            .last()?;
                        Some(FileOpen {
                            kind,
                            name: self.expr(&name_e)?,
                        })
                    }
                    None => None,
                };
                Decl::File {
                    names: child(n, K::IdentifierList).map(|l| idents(&l))?,
                    ty: self.subtype_ind(&child(n, K::SubtypeIndication)?)?,
                    open,
                    span: span(n),
                }
            }
            K::AliasDeclaration => {
                let name = match toks(n).into_iter().find(|t| {
                    matches!(
                        t.kind(),
                        T::Identifier | T::CharacterLiteral | T::StringLiteral
                    )
                })? {
                    t if t.kind() == T::Identifier => Designator::Ident(ident(&t)),
                    t => Designator::Op(
                        String::from_utf8_lossy(&string_value(&bytes(&t))).to_ascii_lowercase(),
                        t.text_range(),
                    ),
                };
                let ty = match child(n, K::AliasSubtype) {
                    Some(a) => Some(self.subtype_ind(&child(&a, K::SubtypeIndication)?)?),
                    None => None,
                };
                Decl::Alias {
                    name,
                    ty,
                    target: self.name(&child(n, K::Name)?)?,
                    span: span(n),
                }
            }
            K::ComponentDeclaration => {
                let pre = child(n, K::ComponentDeclarationPreamble)?;
                Decl::Component(ComponentDecl {
                    name: first_ident(&pre)?,
                    generics: child(n, K::GenericClause)
                        .map(|g| self.interface_clause(&g))
                        .unwrap_or_default(),
                    ports: child(n, K::PortClause)
                        .map(|g| self.interface_clause(&g))
                        .unwrap_or_default(),
                    span: span(n),
                })
            }
            K::AttributeDeclaration => Decl::Attribute {
                name: first_ident(n)?,
                mark: self.name(&child(n, K::Name)?)?,
                span: span(n),
            },
            K::AttributeSpecification => {
                let es = child(n, K::EntitySpecification)?;
                let mut entities = Vec::new();
                let mut all_or_others = false;
                if let Some(l) = child(&es, K::EntityDesignatorList) {
                    for d in childs(&l, K::EntityDesignator) {
                        if let Some(i) = first_ident(&d) {
                            entities.push(i);
                        }
                    }
                } else {
                    all_or_others = true;
                }
                let class = toks(&es)
                    .iter()
                    .filter_map(kw)
                    .next_back()
                    .unwrap_or_default();
                let value_n = nodes(n)
                    .into_iter()
                    .filter(|x| x.kind() != K::EntitySpecification)
                    .last()?;
                Decl::AttributeSpec(AttributeSpec {
                    attr: first_ident(n)?,
                    entities,
                    all_or_others,
                    class,
                    value: self.expr(&value_n)?,
                    span: span(n),
                })
            }
            K::SubprogramDeclaration => {
                let spec = nodes(n).into_iter().next()?;
                Decl::SubprogramDecl(self.subprogram_spec(&spec)?)
            }
            K::SubprogramBody => {
                let pre = child(n, K::SubprogramBodyPreamble)?;
                let spec_n = nodes(&pre).into_iter().find(|x| {
                    matches!(
                        x.kind(),
                        K::FunctionSpecification | K::ProcedureSpecification
                    )
                })?;
                Decl::SubprogramBody(SubprogramBody {
                    spec: self.subprogram_spec(&spec_n)?,
                    decls: child(n, K::SubprogramDeclarativePart)
                        .map(|d| self.decls(&d))
                        .unwrap_or_default(),
                    stmts: child(n, K::SubprogramStatementPart)
                        .map(|s| self.seq_stmts(&s))
                        .unwrap_or_default(),
                    span: span(n),
                })
            }
            K::SubprogramInstantiationDeclaration => {
                let pre = child(n, K::SubprogramInstantiationDeclarationPreamble)?;
                let spec_kind = if has_kw(&pre, "function") {
                    SubprogramKind::Function {
                        pure: true,
                        ret: Name {
                            kind: NameKind::Simple(Ident {
                                name: String::new(),
                                span: span(&pre),
                            }),
                            span: span(&pre),
                        },
                    }
                } else {
                    SubprogramKind::Procedure
                };
                Decl::SubprogramInst {
                    spec_kind,
                    name: first_ident(&pre)?,
                    uninst: self.name(&child(&pre, K::Name)?)?,
                    generic_map: child(n, K::GenericMapAspect)
                        .map(|g| self.map_aspect(&g))
                        .unwrap_or_default(),
                    span: span(n),
                }
            }
            K::UseClauseDeclaration => {
                let u = child(n, K::UseClause)?;
                Decl::Use(self.name_list(&u))
            }
            K::UseClause => Decl::Use(self.name_list(n)),
            K::PackageDeclarationItem => {
                let p = child(n, K::PackageDeclaration)?;
                Decl::Package(Box::new(self.package(&p)?))
            }
            K::PackageDeclaration => Decl::Package(Box::new(self.package(n)?)),
            K::PackageBodyDeclaration => {
                let p = child(n, K::PackageBody)?;
                Decl::PackageBody(Box::new(self.package_body(&p)?))
            }
            K::PackageBody => Decl::PackageBody(Box::new(self.package_body(n)?)),
            K::PackageInstantiationDeclarationItem => {
                let p = child(n, K::PackageInstantiationDeclaration)?;
                Decl::PackageInst(Box::new(self.package_inst(&p)?))
            }
            K::PackageInstantiationDeclaration => {
                Decl::PackageInst(Box::new(self.package_inst(n)?))
            }
            K::DisconnectionSpecification => {
                Decl::Unsupported("disconnection specifications".into(), span(n))
            }
            K::GroupDeclaration | K::GroupTemplateDeclaration => {
                Decl::Unsupported("groups".into(), span(n))
            }
            K::SimpleConfigurationSpecification | K::CompoundConfigurationSpecification => {
                Decl::Unsupported("configuration specifications".into(), span(n))
            }
            _ => {
                self.unsupported(n, "this declaration");
                return None;
            }
        })
    }

    fn subprogram_spec(&mut self, n: &N) -> Option<SubprogramSpec> {
        let designator = match toks(n)
            .into_iter()
            .find(|t| matches!(t.kind(), T::Identifier | T::StringLiteral))?
        {
            t if t.kind() == T::Identifier => Designator::Ident(ident(&t)),
            t => Designator::Op(
                String::from_utf8_lossy(&string_value(&bytes(&t))).to_ascii_lowercase(),
                t.text_range(),
            ),
        };
        let generics = child(n, K::SubprogramHeader)
            .and_then(|h| child(&h, K::SubprogramHeaderGenericClause))
            .map(|g| self.interface_clause(&g))
            .unwrap_or_default();
        let params = child(n, K::ParameterList)
            .and_then(|p| child(&p, K::ParenthesizedInterfaceList))
            .and_then(|p| child(&p, K::InterfaceList))
            .map(|l| self.interface_list(&l))
            .unwrap_or_default();
        let kind = if matches!(
            n.kind(),
            K::FunctionSpecification | K::InterfaceFunctionSpecification
        ) {
            let ret_n = child(n, K::Name)
                .or_else(|| child(n, K::ReturnType).and_then(|r| child(&r, K::Name)))?;
            SubprogramKind::Function {
                pure: !has_kw(n, "impure"),
                ret: self.name(&ret_n)?,
            }
        } else {
            SubprogramKind::Procedure
        };
        Some(SubprogramSpec {
            kind,
            designator,
            generics,
            params,
            span: span(n),
        })
    }

    // ---- associations -------------------------------------------------------

    fn map_aspect(&mut self, n: &N) -> Vec<Assoc> {
        child(n, K::AssociationList)
            .map(|l| self.assoc_list(&l))
            .unwrap_or_default()
    }

    fn assoc_list(&mut self, n: &N) -> Vec<Assoc> {
        let mut out = Vec::new();
        for a in childs(n, K::AssociationElement) {
            let formal = child(&a, K::Formal)
                .and_then(|f| child(&f, K::Name))
                .and_then(|f| self.name(&f));
            let Some(ap) = child(&a, K::ActualPart) else {
                continue;
            };
            let Some(inner) = nodes(&ap).into_iter().next() else {
                continue;
            };
            let actual = match inner.kind() {
                K::ActualPartOpen => Actual::Open(span(&inner)),
                K::ActualPartExpression => {
                    let Some(e) = nodes(&inner).into_iter().next().and_then(|e| self.expr(&e))
                    else {
                        continue;
                    };
                    Actual::Expr(e)
                }
                K::ActualPartSubtypeIndication => {
                    let Some(si) =
                        child(&inner, K::SubtypeIndication).and_then(|s| self.subtype_ind(&s))
                    else {
                        continue;
                    };
                    // A subtype indication actual (for a generic type): carried
                    // as a name expression of its mark; constraints are rare.
                    Actual::Expr(Expr {
                        span: si.span.clone(),
                        kind: ExprKind::Name(si.mark),
                    })
                }
                _ => {
                    self.unexpected(&inner);
                    continue;
                }
            };
            out.push(Assoc {
                formal,
                actual,
                span: span(&a),
            });
        }
        out
    }

    // ---- names --------------------------------------------------------------

    pub fn name(&mut self, n: &N) -> Option<Name> {
        let mut cur: Option<Name> = None;
        let parts = nodes(n);
        let mut i = 0;
        while i < parts.len() {
            let p = &parts[i];
            let start = cur.as_ref().map(|c| c.span.start).unwrap_or(span(p).start);
            let sp = start..span(p).end;
            match p.kind() {
                K::NameDesignatorPrefix => {
                    let t = toks(p).into_iter().next()?;
                    let kind = match t.kind() {
                        T::Identifier => NameKind::Simple(ident(&t)),
                        T::CharacterLiteral => NameKind::Char(bytes(&t)[1]),
                        T::StringLiteral => NameKind::Op(
                            String::from_utf8_lossy(&string_value(&bytes(&t))).to_ascii_lowercase(),
                        ),
                        _ => {
                            self.unexpected(p);
                            return None;
                        }
                    };
                    cur = Some(Name {
                        kind,
                        span: span(p),
                    });
                }
                K::SelectedName => {
                    let t = toks(p).into_iter().find(|t| t.kind() != T::Dot)?;
                    let suffix = match t.kind() {
                        T::Identifier => Suffix::Ident(ident(&t)),
                        T::CharacterLiteral => Suffix::Char(bytes(&t)[1], t.text_range()),
                        T::StringLiteral => Suffix::Op(
                            String::from_utf8_lossy(&string_value(&bytes(&t))).to_ascii_lowercase(),
                            t.text_range(),
                        ),
                        T::Keyword(_) if kw(&t).as_deref() == Some("all") => {
                            Suffix::All(t.text_range())
                        }
                        _ => {
                            self.unexpected(p);
                            return None;
                        }
                    };
                    cur = Some(Name {
                        kind: NameKind::Selected(Box::new(cur?), suffix),
                        span: sp,
                    });
                }
                K::ParenthesizedName => {
                    let assocs = child(p, K::AssociationList)
                        .map(|l| self.assoc_list(&l))
                        .unwrap_or_default();
                    cur = Some(Name {
                        kind: NameKind::Call(Box::new(cur?), assocs),
                        span: sp,
                    });
                }
                K::AttributeName => {
                    let t = toks(p).into_iter().find(|t| t.kind() != T::Tick)?;
                    let attr = Ident {
                        name: fold(&text(&t)),
                        span: t.text_range(),
                    };
                    // `t'image(x)`: a following parenthesized part is the
                    // attribute's parameter for the attributes that take one.
                    let mut param = None;
                    let mut end = span(p).end;
                    if takes_param(&attr.name)
                        && let Some(next) = parts.get(i + 1)
                        && next.kind() == K::ParenthesizedName
                    {
                        let assocs = child(next, K::AssociationList)
                            .map(|l| self.assoc_list(&l))
                            .unwrap_or_default();
                        if let [
                            Assoc {
                                formal: None,
                                actual: Actual::Expr(e),
                                ..
                            },
                        ] = assocs.as_slice()
                        {
                            param = Some(Box::new(e.clone()));
                            end = span(next).end;
                            i += 1;
                        }
                    }
                    cur = Some(Name {
                        kind: NameKind::Attribute(Box::new(cur?), attr, param),
                        span: start..end,
                    });
                }
                K::ExternalConstantName | K::ExternalSignalName | K::ExternalVariableName => {
                    let class = match p.kind() {
                        K::ExternalConstantName => ObjClass::Constant,
                        K::ExternalSignalName => ObjClass::Signal,
                        _ => ObjClass::Variable,
                    };
                    let path_n = nodes(p)
                        .into_iter()
                        .find(|x| x.kind() != K::SubtypeIndication)?;
                    let mut out = Vec::new();
                    path_n.write_to(&mut out).ok();
                    let path: String = out
                        .iter()
                        .map(|&b| b as char)
                        .collect::<String>()
                        .split_whitespace()
                        .collect();
                    let ty = self.subtype_ind(&child(p, K::SubtypeIndication)?)?;
                    cur = Some(Name {
                        kind: NameKind::External {
                            class,
                            path: path.to_ascii_lowercase(),
                            ty: Box::new(ty),
                        },
                        span: span(p),
                    });
                }
                // `integer range 0 to 9` in a subtype indication: the range
                // constraint is read by `subtype_ind`.
                K::RangeConstraint => {}
                K::Signature => {
                    // Signatures (`f[integer return bit]`) select an overload;
                    // not modelled yet.
                    self.unsupported(p, "signatures in names");
                }
                _ => {
                    self.unexpected(p);
                    return None;
                }
            }
            i += 1;
        }
        cur
    }

    // ---- expressions ----------------------------------------------------------

    pub fn expr(&mut self, n: &N) -> Option<Expr> {
        let sp = span(n);
        let kind = match n.kind() {
            K::BinaryExpression => {
                let els = elems(n);
                let mut operands = Vec::new();
                let mut op = None;
                for e in els {
                    match e {
                        SyntaxElement::Node(x) => operands.push(x),
                        SyntaxElement::Token(t) => op = Some(t),
                    }
                }
                let [l, r] = operands.as_slice() else {
                    self.unexpected(n);
                    return None;
                };
                let op = op?;
                let opk = kw(&op);
                if let Some(d) = opk.as_deref().and_then(|k| match k {
                    "to" => Some(Dir::To),
                    "downto" => Some(Dir::Downto),
                    _ => None,
                }) {
                    let left = self.expr(l)?;
                    let right = self.expr(r)?;
                    return Some(Expr {
                        kind: ExprKind::Range(Box::new(RangeExpr::Explicit {
                            left: Box::new(left),
                            dir: d,
                            right: Box::new(right),
                            span: sp.clone(),
                        })),
                        span: sp,
                    });
                }
                let bop = match (op.kind(), opk.as_deref()) {
                    (T::Plus, _) => BinOp::Add,
                    (T::Minus, _) => BinOp::Sub,
                    (T::EQ, _) => BinOp::Eq,
                    (T::NE, _) => BinOp::Ne,
                    (T::LT, _) => BinOp::Lt,
                    (T::LTE, _) => BinOp::Le,
                    (T::GT, _) => BinOp::Gt,
                    (T::GTE, _) => BinOp::Ge,
                    (T::QueEQ, _) => BinOp::MatchEq,
                    (T::QueNE, _) => BinOp::MatchNe,
                    (T::QueLT, _) => BinOp::MatchLt,
                    (T::QueLTE, _) => BinOp::MatchLe,
                    (T::QueGT, _) => BinOp::MatchGt,
                    (T::QueGTE, _) => BinOp::MatchGe,
                    (T::Times, _) => BinOp::Mul,
                    (T::Pow, _) => BinOp::Pow,
                    (T::Div, _) => BinOp::Div,
                    (T::Concat, _) => BinOp::Concat,
                    (_, Some("and")) => BinOp::And,
                    (_, Some("or")) => BinOp::Or,
                    (_, Some("nand")) => BinOp::Nand,
                    (_, Some("nor")) => BinOp::Nor,
                    (_, Some("xor")) => BinOp::Xor,
                    (_, Some("xnor")) => BinOp::Xnor,
                    (_, Some("sll")) => BinOp::Sll,
                    (_, Some("srl")) => BinOp::Srl,
                    (_, Some("sla")) => BinOp::Sla,
                    (_, Some("sra")) => BinOp::Sra,
                    (_, Some("rol")) => BinOp::Rol,
                    (_, Some("ror")) => BinOp::Ror,
                    (_, Some("mod")) => BinOp::Mod,
                    (_, Some("rem")) => BinOp::Rem,
                    _ => {
                        self.unexpected(n);
                        return None;
                    }
                };
                ExprKind::Binary(bop, Box::new(self.expr(l)?), Box::new(self.expr(r)?))
            }
            K::UnaryExpression => {
                let op = toks(n).into_iter().next()?;
                let operand = nodes(n).into_iter().next()?;
                let uop = match (op.kind(), kw(&op).as_deref()) {
                    (T::Plus, _) => UnOp::Plus,
                    (T::Minus, _) => UnOp::Minus,
                    (T::QueQue, _) => UnOp::Cond,
                    (_, Some("abs")) => UnOp::Abs,
                    (_, Some("not")) => UnOp::Not,
                    (_, Some("and")) => UnOp::And,
                    (_, Some("or")) => UnOp::Or,
                    (_, Some("nand")) => UnOp::Nand,
                    (_, Some("nor")) => UnOp::Nor,
                    (_, Some("xor")) => UnOp::Xor,
                    (_, Some("xnor")) => UnOp::Xnor,
                    _ => {
                        self.unexpected(n);
                        return None;
                    }
                };
                ExprKind::Unary(uop, Box::new(self.expr(&operand)?))
            }
            K::NameExpression => ExprKind::Name(self.name(&child(n, K::Name)?)?),
            K::Name => ExprKind::Name(self.name(n)?),
            K::LiteralExpression => {
                let t = toks(n).into_iter().next()?;
                ExprKind::Lit(self.literal(&t)?)
            }
            K::PhysicalLiteralExpression => {
                let pl = child(n, K::PhysicalLiteral)?;
                return self.physical_literal(&pl);
            }
            K::ParenthesizedExpressionOrAggregate => {
                let list = child(n, K::ElementAssociationList)?;
                let assocs = self.elem_assocs(&list)?;
                match assocs.as_slice() {
                    [ElemAssoc { choices, value }] if choices.is_empty() => {
                        ExprKind::Paren(Box::new(value.clone()))
                    }
                    _ => ExprKind::Aggregate(assocs),
                }
            }
            K::QualifiedExpression => {
                let mark = self.name(&child(n, K::Name)?)?;
                let inner = child(n, K::ParenthesizedExpressionOrAggregate)?;
                let e = self.expr(&inner)?;
                ExprKind::Qualified(mark, Box::new(e))
            }
            K::Allocator => {
                let inner = nodes(n).into_iter().next()?;
                match inner.kind() {
                    K::QualifiedExpression => ExprKind::New(Box::new(self.expr(&inner)?)),
                    K::SubtypeIndication => {
                        ExprKind::NewSubtype(Box::new(self.subtype_ind(&inner)?))
                    }
                    _ => {
                        let e = self.expr(&inner)?;
                        match e.kind {
                            ExprKind::Name(nm) => {
                                let (mark, groups) = split_paren_constraints(nm);
                                ExprKind::NewSubtype(Box::new(SubtypeInd {
                                    resolution: None,
                                    span: e.span.clone(),
                                    mark,
                                    constraint: (!groups.is_empty())
                                        .then_some(Constraint::Paren(groups)),
                                }))
                            }
                            _ => {
                                self.unexpected(&inner);
                                return None;
                            }
                        }
                    }
                }
            }
            _ => {
                self.unsupported(n, "this expression");
                return None;
            }
        };
        Some(Expr { kind, span: sp })
    }

    fn elem_assocs(&mut self, n: &N) -> Option<Vec<ElemAssoc>> {
        let mut out = Vec::new();
        for a in childs(n, K::ElementAssociation) {
            let mut choices = Vec::new();
            if let Some(ec) = child(&a, K::ElementChoices)
                && let Some(cs) = child(&ec, K::Choices)
            {
                choices = self.choices(&cs)?;
            }
            let value_n = nodes(&a)
                .into_iter()
                .find(|x| x.kind() != K::ElementChoices)?;
            out.push(ElemAssoc {
                choices,
                value: self.expr(&value_n)?,
            });
        }
        Some(out)
    }

    fn choices(&mut self, n: &N) -> Option<Vec<Choice>> {
        let mut out = Vec::new();
        for c in nodes(n) {
            match c.kind() {
                K::OthersChoice => out.push(Choice::Others(span(&c))),
                K::ExpressionChoice => {
                    let e = self.expr(&nodes(&c).into_iter().next()?)?;
                    out.push(match e.kind {
                        ExprKind::Range(r) => Choice::Range(DiscreteRange::Range(*r)),
                        _ => Choice::Expr(e),
                    });
                }
                _ => {
                    // A discrete range or subtype indication choice.
                    if let Some(d) = self.discrete_range(&c) {
                        out.push(Choice::Range(d));
                    }
                }
            }
        }
        Some(out)
    }

    fn literal(&mut self, t: &Tk) -> Option<Literal> {
        let raw = bytes(t);
        Some(match t.kind() {
            T::AbstractLiteral => match parse_abstract(&text(t)) {
                Some(l) => l,
                None => {
                    self.err(t.text_range(), "VHDL: invalid numeric literal");
                    return None;
                }
            },
            T::CharacterLiteral => Literal::Char(raw[1]),
            T::StringLiteral => Literal::Str(string_value(&raw)),
            T::BitStringLiteral => match expand_bit_string(&text(t)) {
                Ok(v) => Literal::BitStr(v),
                Err(m) => {
                    self.err(t.text_range(), format!("VHDL: {}", m));
                    return None;
                }
            },
            T::Keyword(_) if kw(t).as_deref() == Some("null") => Literal::Null,
            _ => {
                self.err(t.text_range(), "VHDL: internal: unexpected literal");
                return None;
            }
        })
    }

    fn physical_literal(&mut self, n: &N) -> Option<Expr> {
        let sp = span(n);
        let value = match tok(n, T::AbstractLiteral) {
            Some(t) => self.literal(&t)?,
            None => Literal::Int(1),
        };
        let unit = self.name(&child(n, K::Name)?)?;
        Some(Expr {
            kind: ExprKind::Lit(Literal::Physical(Box::new(value), unit)),
            span: sp,
        })
    }

    // ---- concurrent statements ------------------------------------------------

    pub fn conc_stmts(&mut self, n: &N) -> Vec<ConcStmt> {
        let mut out = Vec::new();
        for c in nodes(n) {
            if let Some(s) = self.conc_stmt(&c) {
                out.push(s);
            }
        }
        out
    }

    fn label(&mut self, n: &N) -> Option<Ident> {
        child(n, K::StmtLabel).and_then(|l| first_ident(&l))
    }

    fn waveform(&mut self, n: &N) -> Option<Waveform> {
        if n.kind() == K::UnaffectedWaveform {
            return Some(Waveform::Unaffected(span(n)));
        }
        let mut elems = Vec::new();
        for we in childs(n, K::WaveformElement) {
            let mut value = None;
            let mut after = None;
            for c in nodes(&we) {
                if c.kind() == K::AfterClause {
                    after = nodes(&c).into_iter().next().and_then(|e| self.expr(&e));
                } else {
                    let e = self.expr(&c)?;
                    value = match e.kind {
                        ExprKind::Lit(Literal::Null) => None,
                        _ => Some(e),
                    };
                }
            }
            elems.push(WaveElem {
                value,
                after,
                span: span(&we),
            });
        }
        Some(Waveform::Elems(elems))
    }

    fn delay(&mut self, n: &N) -> Option<DelayMech> {
        if let Some(_t) = child(n, K::TransportDelayMechanism) {
            return Some(DelayMech::Transport);
        }
        let im = child(n, K::InertialDelayMechanism)?;
        let reject = child(&im, K::RejectClause)
            .and_then(|r| nodes(&r).into_iter().next())
            .and_then(|e| self.expr(&e));
        Some(DelayMech::Inertial(reject))
    }

    fn target(&mut self, n: &N) -> Option<Target> {
        if let Some(t) = child(n, K::NameTarget) {
            return Some(Target::Name(self.name(&child(&t, K::Name)?)?));
        }
        if let Some(t) = child(n, K::AggregateTarget) {
            let agg = nodes(&t).into_iter().next()?;
            let list = child(&agg, K::ElementAssociationList)?;
            return Some(Target::Aggregate(self.elem_assocs(&list)?, span(&t)));
        }
        None
    }

    /// `a when c else b when d else e` (waveforms).
    fn cond_waveforms(&mut self, n: &N) -> Option<Vec<(Waveform, Option<Expr>)>> {
        let mut out = Vec::new();
        for c in nodes(n) {
            match c.kind() {
                K::WhenWaveform | K::ElseWhenWaveform => {
                    let parts = nodes(&c);
                    let w = parts.first()?;
                    let cond = parts.get(1).and_then(|e| self.expr(e));
                    out.push((self.waveform(w)?, cond));
                }
                K::ElseWaveform => {
                    let w = nodes(&c).into_iter().next()?;
                    out.push((self.waveform(&w)?, None));
                }
                _ => self.unexpected(&c),
            }
        }
        Some(out)
    }

    fn selected_waveforms(&mut self, n: &N) -> Option<Vec<(Waveform, Vec<Choice>)>> {
        let mut out = Vec::new();
        for item in childs(n, K::SelectedWaveformItem) {
            let parts = nodes(&item);
            let w = self.waveform(parts.first()?)?;
            let cs = child(&item, K::Choices).and_then(|c| self.choices(&c))?;
            out.push((w, cs));
        }
        Some(out)
    }

    fn conc_stmt(&mut self, n: &N) -> Option<ConcStmt> {
        let label = self.label(n);
        let postponed = has_kw(n, "postponed");
        let kind = match n.kind() {
            K::ProcessStatement => {
                let pre = child(n, K::ProcessPreamble)?;
                let sens = child(&pre, K::ParenthesizedProcessSensitivityList).map(|p| {
                    if child(&p, K::AllSensitivityList).is_some() {
                        Sensitivity::All
                    } else {
                        Sensitivity::List(
                            child(&p, K::SensitivityList)
                                .map(|l| {
                                    childs(&l, K::Name)
                                        .iter()
                                        .filter_map(|x| self.name(x))
                                        .collect()
                                })
                                .unwrap_or_default(),
                        )
                    }
                });
                ConcKind::Process {
                    postponed: has_kw(&pre, "postponed") || postponed,
                    sens,
                    decls: child(n, K::ProcessDeclarativePart)
                        .map(|d| self.decls(&d))
                        .unwrap_or_default(),
                    stmts: child(n, K::ProcessStatementPart)
                        .map(|s| self.seq_stmts(&s))
                        .unwrap_or_default(),
                }
            }
            K::ConcurrentSimpleSignalAssignment => ConcKind::SignalAssign {
                postponed,
                guarded: has_kw(n, "guarded"),
                target: self.target(n)?,
                delay: self.delay(n),
                rhs: AssignRhs::Simple(self.waveform(&child(n, K::WaveformElements)?)?),
            },
            K::ConcurrentConditionalSignalAssignment => ConcKind::SignalAssign {
                postponed,
                guarded: has_kw(n, "guarded"),
                target: self.target(n)?,
                delay: self.delay(n),
                rhs: AssignRhs::Cond(self.cond_waveforms(&child(n, K::ConditionalWaveforms)?)?),
            },
            K::ConcurrentSelectedSignalAssignment => {
                let pre = child(n, K::SelectedAssignmentPreamble)?;
                let e = first_node(&pre)?;
                ConcKind::SignalAssign {
                    postponed,
                    guarded: has_kw(n, "guarded"),
                    target: self.target(n)?,
                    delay: self.delay(n),
                    rhs: AssignRhs::Select {
                        expr: self.expr(&e)?,
                        matching: tok(&pre, T::Que).is_some(),
                        items: self.selected_waveforms(&child(n, K::SelectedWaveforms)?)?,
                    },
                }
            }
            K::ConcurrentAssertionStatement => {
                let a = child(n, K::Assertion)?;
                let (cond, report, severity) = self.assertion(&a)?;
                ConcKind::Assert {
                    postponed,
                    cond,
                    report,
                    severity,
                }
            }
            K::ConcurrentProcedureCallOrComponentInstantiationStatement => {
                // `label: name;` / `name(args);` — a procedure call or a
                // component instantiation without maps; sema decides.
                ConcKind::ProcCall {
                    postponed,
                    call: self.name(&child(n, K::Name)?)?,
                }
            }
            K::ComponentInstantiationStatement => {
                let unit = if let Some(ie) = child(n, K::InstantiatedEntity) {
                    let full = self.name(&child(&ie, K::Name)?)?;
                    match full.kind {
                        NameKind::Call(prefix, args) => {
                            let arch = match args.as_slice() {
                                [
                                    Assoc {
                                        actual:
                                            Actual::Expr(Expr {
                                                kind:
                                                    ExprKind::Name(Name {
                                                        kind: NameKind::Simple(i),
                                                        ..
                                                    }),
                                                ..
                                            }),
                                        ..
                                    },
                                ] => Some(i.clone()),
                                _ => None,
                            };
                            InstUnit::Entity(*prefix, arch)
                        }
                        _ => InstUnit::Entity(full, None),
                    }
                } else if let Some(ic) = child(n, K::InstantiatedComponent) {
                    InstUnit::Component(self.name(&child(&ic, K::Name)?)?)
                } else if let Some(ic) = child(n, K::InstantiatedConfiguration) {
                    InstUnit::Configuration(self.name(&child(&ic, K::Name)?)?)
                } else {
                    self.unexpected(n);
                    return None;
                };
                ConcKind::Instance {
                    unit,
                    generic_map: child(n, K::GenericMapAspect)
                        .map(|g| self.map_aspect(&g))
                        .unwrap_or_default(),
                    port_map: child(n, K::PortMapAspect)
                        .map(|g| self.map_aspect(&g))
                        .unwrap_or_default(),
                }
            }
            K::BlockStatement => {
                let pre = child(n, K::BlockPreamble)?;
                let guard = child(&pre, K::ParenthesizedCondition)
                    .and_then(|c| nodes(&c).into_iter().next())
                    .and_then(|e| self.expr(&e));
                let header = child(n, K::BlockHeader);
                let (mut generics, mut generic_map, mut ports, mut port_map) =
                    (Vec::new(), Vec::new(), Vec::new(), Vec::new());
                if let Some(h) = &header {
                    if let Some(g) = child(h, K::GenericClause) {
                        generics = self.interface_clause(&g);
                    }
                    if let Some(g) = child(h, K::GenericMapAspect) {
                        generic_map = self.map_aspect(&g);
                    }
                    if let Some(g) = child(h, K::PortClause) {
                        ports = self.interface_clause(&g);
                    }
                    if let Some(g) = child(h, K::PortMapAspect) {
                        port_map = self.map_aspect(&g);
                    }
                }
                ConcKind::Block {
                    guard,
                    generics,
                    generic_map,
                    ports,
                    port_map,
                    decls: child(n, K::BlockDeclarativePart)
                        .map(|d| self.decls(&d))
                        .unwrap_or_default(),
                    stmts: child(n, K::BlockStatementPart)
                        .map(|s| self.conc_stmts(&s))
                        .unwrap_or_default(),
                }
            }
            K::ForGenerateStatement => {
                let pre = child(n, K::ForGeneratePreamble)?;
                let ps = child(&pre, K::ParameterSpecification)?;
                let range_n = nodes(&ps).into_iter().next()?;
                let (decls, stmts) = self.generate_body(&child(n, K::GenerateStatementBody)?);
                ConcKind::ForGenerate {
                    param: first_ident(&ps)?,
                    range: self.discrete_range(&range_n)?,
                    decls,
                    stmts,
                }
            }
            K::IfGenerateStatement => {
                let mut branches = Vec::new();
                for b in nodes(n) {
                    match b.kind() {
                        K::IfGenerateIf | K::IfGenerateElsif | K::IfGenerateElse => {
                            let alt_label = self.label(&b);
                            let cond = nodes(&b)
                                .into_iter()
                                .find(|x| {
                                    !matches!(x.kind(), K::StmtLabel | K::GenerateStatementBody)
                                })
                                .and_then(|e| self.expr(&e));
                            let (decls, stmts) =
                                self.generate_body(&child(&b, K::GenerateStatementBody)?);
                            branches.push(GenerateBranch {
                                alt_label,
                                cond,
                                choices: Vec::new(),
                                decls,
                                stmts,
                            });
                        }
                        K::StmtLabel | K::GenerateEpilogue => {}
                        _ => self.unexpected(&b),
                    }
                }
                ConcKind::IfGenerate(branches)
            }
            K::CaseGenerateStatement => {
                let pre = child(n, K::CaseGeneratePreamble)?;
                let e = first_node(&pre)?;
                let mut branches = Vec::new();
                for b in childs(n, K::CaseGenerateAlternative) {
                    let choices = child(&b, K::Choices).and_then(|c| self.choices(&c))?;
                    let (decls, stmts) = self.generate_body(&child(&b, K::GenerateStatementBody)?);
                    branches.push(GenerateBranch {
                        alt_label: self.label(&b),
                        cond: None,
                        choices,
                        decls,
                        stmts,
                    });
                }
                ConcKind::CaseGenerate {
                    expr: self.expr(&e)?,
                    branches,
                }
            }
            _ => {
                self.unsupported(n, "this concurrent statement");
                return None;
            }
        };
        Some(ConcStmt {
            label,
            kind,
            span: span(n),
        })
    }

    fn generate_body(&mut self, n: &N) -> (Vec<Decl>, Vec<ConcStmt>) {
        let decls = child(n, K::GenerateBodyDeclarations)
            .and_then(|d| child(&d, K::BlockDeclarativePart))
            .map(|d| self.decls(&d))
            .unwrap_or_default();
        let mut stmts = Vec::new();
        for c in nodes(n) {
            match c.kind() {
                K::GenerateBodyDeclarations
                | K::DeclarationStatementSeparator
                | K::GenerateBodyEpilogue => {}
                _ => {
                    if let Some(s) = self.conc_stmt(&c) {
                        stmts.push(s);
                    }
                }
            }
        }
        (decls, stmts)
    }

    fn assertion(&mut self, a: &N) -> Option<(Expr, Option<Expr>, Option<Expr>)> {
        let cond_n = nodes(a)
            .into_iter()
            .find(|x| !matches!(x.kind(), K::ReportClause | K::SeverityClause))?;
        let report = child(a, K::ReportClause)
            .and_then(|r| nodes(&r).into_iter().next())
            .and_then(|e| self.expr(&e));
        let severity = child(a, K::SeverityClause)
            .and_then(|r| nodes(&r).into_iter().next())
            .and_then(|e| self.expr(&e));
        Some((self.expr(&cond_n)?, report, severity))
    }

    // ---- sequential statements ----------------------------------------------

    pub fn seq_stmts(&mut self, n: &N) -> Vec<SeqStmt> {
        let mut out = Vec::new();
        for c in nodes(n) {
            if let Some(s) = self.seq_stmt(&c) {
                out.push(s);
            }
        }
        out
    }

    fn seq_body(&mut self, n: &N) -> Vec<SeqStmt> {
        child(n, K::SequenceOfStatements)
            .map(|s| self.seq_stmts(&s))
            .unwrap_or_default()
    }

    fn seq_stmt(&mut self, n: &N) -> Option<SeqStmt> {
        let mut label = self.label(n);
        let kind = match n.kind() {
            K::WaitStatement => SeqKind::Wait {
                on: child(n, K::SensitivityClause)
                    .and_then(|c| child(&c, K::SensitivityList))
                    .map(|l| {
                        childs(&l, K::Name)
                            .iter()
                            .filter_map(|x| self.name(x))
                            .collect()
                    })
                    .unwrap_or_default(),
                until: child(n, K::ConditionClause)
                    .and_then(|c| nodes(&c).into_iter().next())
                    .and_then(|e| self.expr(&e)),
                timeout: child(n, K::TimeoutClause)
                    .and_then(|c| nodes(&c).into_iter().next())
                    .and_then(|e| self.expr(&e)),
            },
            K::AssertionStatement => {
                let a = child(n, K::Assertion)?;
                let (cond, report, severity) = self.assertion(&a)?;
                SeqKind::Assert {
                    cond,
                    report,
                    severity,
                }
            }
            K::ReportStatement => {
                let msg_n = nodes(n)
                    .into_iter()
                    .find(|x| x.kind() != K::SeverityClause && x.kind() != K::StmtLabel)?;
                SeqKind::Report {
                    msg: self.expr(&msg_n)?,
                    severity: child(n, K::SeverityClause)
                        .and_then(|r| nodes(&r).into_iter().next())
                        .and_then(|e| self.expr(&e)),
                }
            }
            K::SimpleWaveformAssignment => SeqKind::SignalAssign {
                target: self.target(n)?,
                delay: self.delay(n),
                rhs: AssignRhs::Simple(self.waveform(&child(n, K::WaveformElements)?)?),
            },
            K::ConditionalWaveformAssignment => SeqKind::SignalAssign {
                target: self.target(n)?,
                delay: self.delay(n),
                rhs: AssignRhs::Cond(self.cond_waveforms(&child(n, K::ConditionalWaveforms)?)?),
            },
            K::SelectedWaveformAssignment => {
                let pre = child(n, K::SelectedAssignmentPreamble)?;
                let e = first_node(&pre)?;
                SeqKind::SignalAssign {
                    target: self.target(n)?,
                    delay: self.delay(n),
                    rhs: AssignRhs::Select {
                        expr: self.expr(&e)?,
                        matching: tok(&pre, T::Que).is_some(),
                        items: self.selected_waveforms(&child(n, K::SelectedWaveforms)?)?,
                    },
                }
            }
            K::SimpleVariableAssignment => {
                let e = nodes(n).into_iter().find(|x| {
                    !matches!(x.kind(), K::NameTarget | K::AggregateTarget | K::StmtLabel)
                })?;
                SeqKind::VarAssign {
                    target: self.target(n)?,
                    rhs: AssignRhs::Simple(self.expr(&e)?),
                }
            }
            K::ConditionalVariableAssignment => {
                let ce = child(n, K::ConditionalExpressions)?;
                SeqKind::VarAssign {
                    target: self.target(n)?,
                    rhs: AssignRhs::Cond(self.cond_exprs(&ce)?),
                }
            }
            K::SelectedVariableAssignment => {
                let pre = child(n, K::SelectedAssignmentPreamble)?;
                let e = first_node(&pre)?;
                let se = child(n, K::SelectedExpressions)?;
                SeqKind::VarAssign {
                    target: self.target(n)?,
                    rhs: AssignRhs::Select {
                        expr: self.expr(&e)?,
                        matching: tok(&pre, T::Que).is_some(),
                        items: self.selected_exprs(&se)?,
                    },
                }
            }
            K::SimpleForceAssignment => {
                let e = nodes(n).into_iter().find(|x| {
                    !matches!(x.kind(), K::NameTarget | K::AggregateTarget | K::StmtLabel)
                })?;
                SeqKind::Force {
                    target: self.target(n)?,
                    mode: force_mode(n),
                    rhs: AssignRhs::Simple(self.expr(&e)?),
                }
            }
            K::ConditionalForceAssignment => {
                let ce = child(n, K::ConditionalExpressions)?;
                SeqKind::Force {
                    target: self.target(n)?,
                    mode: force_mode(n),
                    rhs: AssignRhs::Cond(self.cond_exprs(&ce)?),
                }
            }
            K::SelectedForceAssignment => {
                let pre = child(n, K::SelectedAssignmentPreamble)?;
                let e = first_node(&pre)?;
                let se = child(n, K::SelectedExpressions)?;
                SeqKind::Force {
                    target: self.target(n)?,
                    mode: force_mode(n),
                    rhs: AssignRhs::Select {
                        expr: self.expr(&e)?,
                        matching: tok(&pre, T::Que).is_some(),
                        items: self.selected_exprs(&se)?,
                    },
                }
            }
            K::SimpleReleaseAssignment => SeqKind::Release {
                target: self.target(n)?,
                mode: force_mode(n),
            },
            K::ProcedureCallStatement => SeqKind::ProcCall(self.name(&child(n, K::Name)?)?),
            K::IfStatement => {
                let pre = child(n, K::IfStatementPreamble)?;
                if label.is_none() {
                    label = self.label(&pre);
                }
                let cond = first_node(&pre)?;
                let mut branches = vec![(self.expr(&cond)?, self.seq_body(n))];
                for ei in childs(n, K::IfStatementElsif) {
                    let c = nodes(&ei).into_iter().next()?;
                    let body = self.seq_body(&ei);
                    branches.push((self.expr(&c)?, body));
                }
                let else_branch = child(n, K::IfStatementElse).map(|e| self.seq_body(&e));
                SeqKind::If {
                    branches,
                    else_branch,
                }
            }
            K::CaseStatement => {
                let pre = child(n, K::CaseStatementPreamble)?;
                if label.is_none() {
                    label = self.label(&pre);
                }
                let e = first_node(&pre)?;
                let mut alts = Vec::new();
                for alt in childs(n, K::CaseStatementAlternative) {
                    let ap = child(&alt, K::CaseStatementAlternativePreamble)?;
                    let cs = child(&ap, K::Choices).and_then(|c| self.choices(&c))?;
                    alts.push((cs, self.seq_body(&alt)));
                }
                SeqKind::Case {
                    matching: tok(&pre, T::Que).is_some(),
                    expr: self.expr(&e)?,
                    alts,
                }
            }
            K::LoopStatement => {
                let pre = child(n, K::LoopStatementPreamble)?;
                if label.is_none() {
                    label = self.label(&pre);
                }
                let scheme = if let Some(w) = child(&pre, K::WhileScheme) {
                    LoopScheme::While(self.expr(&nodes(&w).into_iter().next()?)?)
                } else if let Some(f) = child(&pre, K::ForScheme) {
                    let ps = child(&f, K::ParameterSpecification)?;
                    let r = nodes(&ps).into_iter().next()?;
                    LoopScheme::For(first_ident(&ps)?, self.discrete_range(&r)?)
                } else {
                    LoopScheme::Plain
                };
                SeqKind::Loop {
                    scheme,
                    body: self.seq_body(n),
                }
            }
            K::NextStatement | K::ExitStatement => {
                let target_label = first_ident(n);
                let cond = child(n, K::WhenClause)
                    .and_then(|w| nodes(&w).into_iter().next())
                    .and_then(|e| self.expr(&e));
                if n.kind() == K::NextStatement {
                    SeqKind::Next {
                        label: target_label,
                        cond,
                    }
                } else {
                    SeqKind::Exit {
                        label: target_label,
                        cond,
                    }
                }
            }
            K::ReturnStatement => SeqKind::Return(
                nodes(n)
                    .into_iter()
                    .find(|x| x.kind() != K::StmtLabel)
                    .and_then(|e| self.expr(&e)),
            ),
            K::NullStatement => SeqKind::Null,
            _ => {
                self.unsupported(n, "this sequential statement");
                return None;
            }
        };
        Some(SeqStmt {
            label,
            kind,
            span: span(n),
        })
    }

    fn cond_exprs(&mut self, n: &N) -> Option<Vec<(Expr, Option<Expr>)>> {
        let mut out = Vec::new();
        for c in nodes(n) {
            match c.kind() {
                K::WhenExpression | K::ElseWhenExpression => {
                    let parts = nodes(&c);
                    let v = self.expr(parts.first()?)?;
                    let cond = parts.get(1).and_then(|e| self.expr(e));
                    out.push((v, cond));
                }
                K::ElseExpression => {
                    let v = nodes(&c).into_iter().next()?;
                    out.push((self.expr(&v)?, None));
                }
                _ => self.unexpected(&c),
            }
        }
        Some(out)
    }

    fn selected_exprs(&mut self, n: &N) -> Option<Vec<(Expr, Vec<Choice>)>> {
        let mut out = Vec::new();
        for item in childs(n, K::SelectedExpressionItem) {
            let v = nodes(&item).into_iter().next()?;
            let cs = child(&item, K::Choices).and_then(|c| self.choices(&c))?;
            out.push((self.expr(&v)?, cs));
        }
        Some(out)
    }
}

fn force_mode(n: &N) -> Option<ForceMode> {
    if has_kw(n, "in") {
        Some(ForceMode::In)
    } else if has_kw(n, "out") {
        Some(ForceMode::Out)
    } else {
        None
    }
}

/// Attributes that take a parameter (`t'image(x)`, `a'length(2)`,
/// `s'delayed(5 ns)`).
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

/// Split trailing call suffixes off a type mark: `bit_vector(7 downto 0)` →
/// (`bit_vector`, [[7 downto 0]]).
fn split_paren_constraints(mut n: Name) -> (Name, Vec<Vec<Assoc>>) {
    let mut groups = Vec::new();
    while let NameKind::Call(prefix, args) = n.kind {
        groups.push(args);
        n = *prefix;
    }
    groups.reverse();
    (n, groups)
}

/// Parse an abstract literal (§15.5): decimal or based, integer or real,
/// with `_` separators and an optional exponent.
pub fn parse_abstract(s: &str) -> Option<Literal> {
    let s: String = s.chars().filter(|&c| c != '_').collect();
    let lower = s.to_ascii_lowercase();
    if let Some(h) = lower.find(['#', ':']) {
        let delim = lower.as_bytes()[h] as char;
        let base: u32 = lower[..h].parse().ok()?;
        if !(2..=16).contains(&base) {
            return None;
        }
        let rest = &lower[h + 1..];
        let end = rest.find(delim)?;
        let digits = &rest[..end];
        let exp = match rest[end + 1..].strip_prefix('e') {
            Some(e) => e.trim_start_matches('+').parse::<i32>().ok()?,
            None => 0,
        };
        if let Some(dot) = digits.find('.') {
            let mut v = 0f64;
            for c in digits[..dot].chars() {
                v = v * base as f64 + c.to_digit(base)? as f64;
            }
            let mut scale = 1f64 / base as f64;
            for c in digits[dot + 1..].chars() {
                v += c.to_digit(base)? as f64 * scale;
                scale /= base as f64;
            }
            return Some(Literal::Real(v * (base as f64).powi(exp)));
        }
        let mut v: i128 = 0;
        for c in digits.chars() {
            v = v
                .checked_mul(base as i128)?
                .checked_add(c.to_digit(base)? as i128)?;
        }
        return Some(Literal::Int(
            v.checked_mul((base as i128).checked_pow(exp.max(0) as u32)?)?,
        ));
    }
    if lower.contains('.') {
        return lower.parse::<f64>().ok().map(Literal::Real);
    }
    match lower.split_once('e') {
        Some((m, e)) => {
            let m: i128 = m.parse().ok()?;
            let e: u32 = e.trim_start_matches('+').parse().ok()?;
            Some(Literal::Int(m.checked_mul(10i128.checked_pow(e)?)?))
        }
        None => lower.parse::<i128>().ok().map(Literal::Int),
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
