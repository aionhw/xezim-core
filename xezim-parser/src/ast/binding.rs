//! Ids of the scope tree (`xezim_core::scope_tree`), for AST nodes to refer to.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeclId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DeclKind {
    Function,
    Task,
    Data,
    Net,
    Param,
    Genvar,
    Typedef,
    Class,
    Instance,
    Module,
    Let,
    Property,
    Sequence,
    Covergroup,
    Clocking,
    Checker,
    Modport,
    DpiImport,
    EnumMember,
    Label,
    Nettype,
}
