//! Abstract Syntax Tree definitions for SystemVerilog IEEE 1800-2017/2023.



pub mod types;
pub mod expr;
pub mod stmt;
pub mod decl;
pub mod module;

/// A span of source text identified by byte offsets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self { Self { start, end } }
    pub fn dummy() -> Self { Self { start: 0, end: 0 } }
}

/// Trait for AST nodes that have a source span.
pub trait Spanned {
    fn span(&self) -> Span;
}

/// An identifier with its source location.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Identifier {
    pub name: String,
    pub span: Span,
}

/// An attribute instance: (* attr_spec { , attr_spec } *)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AttributeInstance {
    pub attrs: Vec<(Identifier, Option<expr::Expression>)>,
    pub span: Span,
}

/// Top-level source text: a sequence of descriptions.
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceText {
    pub descriptions: Vec<Description>,
    pub span: Span,
}

/// A top-level description item.
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Description {
    Module(module::ModuleDeclaration),
    Interface(module::InterfaceDeclaration),
    Program(module::ProgramDeclaration),
    Package(module::PackageDeclaration),
    Class(decl::ClassDeclaration),
    TypedefDecl(decl::TypedefDeclaration),
    ImportDecl(decl::ImportDeclaration),
    TimeunitsDecl(decl::TimeunitsDeclaration),
    PackageItem(decl::PackageItem),
    DPIImport(decl::DPIImport),
    DPIExport(decl::DPIExport),
    /// Compilation-unit-scope `bind` directive (IEEE 1800-2023 §23.11).
    /// Resolved during elaboration: the wrapped instantiation is appended
    /// to the named target module's items.
    Bind(decl::BindDirective),
    /// IEEE 1800-2017 §29 User-Defined Primitive declaration.
    Udp(decl::UdpDecl),
    /// §18.5.1 compilation-unit-scope out-of-class constraint definition
    /// `constraint ClassName::name { ... }`. Records that the class's
    /// `extern constraint name;` has an external body.
    /// §18.5.1 `constraint Class::name { ... }` — the BODY is carried so the
    /// class's extern-constraint prototype can be filled in at elaboration
    /// (it used to be brace-skipped and discarded, so the constraints simply
    /// did not exist at solve time).
    OutOfClassConstraint { class_name: String, constraint_name: String, items: Vec<crate::ast::decl::ConstraintItem> },
    /// Verilog-AMS §3.6.1 `nature … endnature`. Top-level only (a nature is not
    /// a module item). Parse-only at this stage: recorded so an analog stage
    /// can resolve `access` functions and tolerances without re-parsing.
    Nature(decl::NatureDeclaration),
    /// Verilog-AMS §3.6.2 `discipline … enddiscipline`. Top-level only.
    Discipline(decl::DisciplineDeclaration),
}
