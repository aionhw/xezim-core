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
    /// §27.4: a generate loop's genvar, a localparam of each iteration.
    pub const GENVAR: Bound = Bound(3);

    /// The tag of a §6.10 implicit net that a generate block declares.
    const BLOCK_IMPLICIT_NET: u32 = 1 << 31;
    /// A typedef key assigned by package and compilation-unit scoping.
    const EXTERNAL_TYPE: u32 = 1 << 30;
    /// §6.18: the local type declaration follows this use.
    const LATE_TYPE_DECLARATION: u32 = 1 << 29;

    pub fn external_type(index: u32) -> Bound {
        Bound(index | Self::EXTERNAL_TYPE)
    }

    pub fn external_type_index(self) -> Option<usize> {
        (self.0 & Self::EXTERNAL_TYPE != 0).then_some((self.0 ^ Self::EXTERNAL_TYPE) as usize)
    }

    pub fn with_late_type_declaration(self) -> Bound {
        Bound(self.0 | Self::LATE_TYPE_DECLARATION)
    }

    pub fn has_late_type_declaration(self) -> bool {
        self.0 & Self::LATE_TYPE_DECLARATION != 0
    }

    pub fn decl(d: DeclId) -> Bound {
        Bound(d.0 + 4)
    }

    /// §6.10, §27: a declaration that is an implicit net of a generate
    /// block, which the block's rename keys like its declared nets.
    pub fn block_implicit_net(d: DeclId) -> Bound {
        Bound((d.0 + 4) | Self::BLOCK_IMPLICIT_NET)
    }

    /// The declaration in this definition's tree.
    pub fn as_decl(self) -> Option<DeclId> {
        if self.external_type_index().is_some() {
            return None;
        }
        (self.0 & !(Self::BLOCK_IMPLICIT_NET | Self::LATE_TYPE_DECLARATION))
            .checked_sub(4)
            .map(DeclId)
    }

    pub fn is_block_implicit_net(self) -> bool {
        self.0 & Self::BLOCK_IMPLICIT_NET != 0
    }

    pub fn is_unset(self) -> bool {
        self == Self::UNSET
    }

    pub fn is_upward(self) -> bool {
        self == Self::UPWARD
    }
}
