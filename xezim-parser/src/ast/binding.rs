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
    TypeParam,
    Genvar,
    Typedef,
    Class,
    Instance,
    Gate,
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
    /// §6.10, §31.9: a net declared by its use.
    ImplicitNet,
}

/// §23.9, §26.3, §23.8.1: what the head of a name resolves to in its definition,
/// in 4 bytes. The tree's `decls[d]` gives a declaration's scope and kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Bound(u32);

impl Bound {
    /// Not analysed: a position the binder does not walk, or a synthesized name.
    pub const UNSET: Bound = Bound(0);
    /// No lexical target: hidden by a procedural or class-level name, found
    /// through an import or `$unit`, rooted or scoped.
    pub const NO_TARGET: Bound = Bound(1);
    /// Nothing declares it lexically: resolved through the hierarchy (§23.8.1).
    pub const UPWARD: Bound = Bound(2);

    pub fn decl(d: DeclId) -> Bound {
        Bound(d.0 + 3)
    }

    /// The declaration in this definition's tree.
    pub fn as_decl(self) -> Option<DeclId> {
        self.0.checked_sub(3).map(DeclId)
    }

    pub fn is_unset(self) -> bool {
        self == Self::UNSET
    }

    pub fn is_upward(self) -> bool {
        self == Self::UPWARD
    }
}
