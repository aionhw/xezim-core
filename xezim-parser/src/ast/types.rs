//! SystemVerilog data types (IEEE 1800-2017 §6, §7)

use super::{Identifier, Span, expr};

/// Data type AST node.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DataType {
    IntegerVector {
        kind: IntegerVectorType,
        signing: Option<Signing>,
        dimensions: Vec<PackedDimension>,
        span: Span,
    },
    IntegerAtom {
        kind: IntegerAtomType,
        signing: Option<Signing>,
        span: Span,
    },
    Real {
        kind: RealType,
        span: Span,
    },
    Simple {
        kind: SimpleType,
        span: Span,
    },
    Struct(StructUnionType),
    Enum(EnumType),
    Void(Span),
    TypeReference {
        name: TypeName,
        dimensions: Vec<PackedDimension>,
        type_args: Vec<expr::Expression>,
        span: Span,
    },
    Interface {
        name: Identifier,
        modport: Option<Identifier>,
        type_args: Vec<expr::Expression>,
        span: Span,
    },
    Implicit {
        signing: Option<Signing>,
        dimensions: Vec<PackedDimension>,
        span: Span,
    },
}

/// One `::`-chained scope link of a [`TypeName`] — `pkg` in `pkg::T`, the
/// class `cls` (with its `#(...)` specialization args) in `cls#(N)::t`
/// (IEEE 1800-2017 §8.23, §8.25.1).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeScope {
    pub name: Identifier,
    /// `#(...)` specialization args when this link names a parameterized
    /// class (`cls#(N)::t`). Empty for package/plain-class links.
    #[cfg_attr(feature = "serde", serde(default))]
    pub type_args: Vec<expr::Expression>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeName {
    /// `::`-chained scope prefix, outermost first: `pkg::cls::t` keeps
    /// [`pkg`, `cls`]. Empty for an unqualified name. A chain longer than
    /// one link is legal wherever a type may be named (§8.23 class scope,
    /// §6.20.3 typedef, §13.5 ports) — the parser used to collapse it to a
    /// single link and mis-parse the rest.
    #[cfg_attr(feature = "serde", serde(default))]
    pub scopes: Vec<TypeScope>,
    pub name: Identifier,
    pub span: Span,
}

impl TypeName {
    /// Whether any `::` scope prefix is present.
    pub fn has_scope(&self) -> bool {
        !self.scopes.is_empty()
    }

    /// The scope prefix when exactly one `::` link precedes the name —
    /// `pkg::T` and an out-of-block method name `C::f`. `None` for
    /// unqualified names and for longer chains.
    pub fn single_scope(&self) -> Option<&Identifier> {
        if self.scopes.len() == 1 {
            Some(&self.scopes[0].name)
        } else {
            None
        }
    }

    /// The fully-qualified `a::b::leaf` key, ignoring `#(...)` args — the
    /// string the elaborator's typedef tables key scoped aliases under.
    pub fn qualified(&self) -> String {
        let mut s = String::new();
        for link in &self.scopes {
            s.push_str(&link.name.name);
            s.push_str("::");
        }
        s.push_str(&self.name.name);
        s
    }

    /// The `::`-joined scope prefix alone (`pkg::cls`), empty when
    /// unqualified — the "owner" of a scoped type.
    pub fn scope_prefix(&self) -> String {
        let mut s = String::new();
        for link in &self.scopes {
            s.push_str(&link.name.name);
            s.push_str("::");
        }
        if s.ends_with("::") {
            s.truncate(s.len() - 2);
        }
        s
    }

    /// Whether any scope link carries a `#(...)` specialization
    /// (`cls#(N)::t`, §8.25.1) — such references need the class walked and
    /// its parameters bound, not just a table lookup.
    pub fn has_specialized_scope(&self) -> bool {
        self.scopes.iter().any(|s| !s.type_args.is_empty())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IntegerVectorType {
    Bit,
    Logic,
    Reg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IntegerAtomType {
    Byte,
    ShortInt,
    Int,
    LongInt,
    Integer,
    Time,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RealType {
    Real,
    ShortReal,
    RealTime,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SimpleType {
    String,
    Chandle,
    Event,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Signing {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PackedDimension {
    Range {
        left: Box<expr::Expression>,
        right: Box<expr::Expression>,
        span: Span,
    },
    Unsized(Span),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnpackedDimension {
    Range {
        left: Box<expr::Expression>,
        right: Box<expr::Expression>,
        span: Span,
    },
    Expression {
        expr: Box<expr::Expression>,
        span: Span,
    },
    Unsized(Span),
    Queue {
        max_size: Option<Box<expr::Expression>>,
        span: Span,
    },
    Associative {
        data_type: Option<Box<DataType>>,
        span: Span,
    },
}

/// struct/union type
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StructUnionType {
    pub kind: StructUnionKind,
    pub packed: bool,
    pub tagged: bool,
    /// IEEE 1800-2023 §7.3.2 `union soft` — a packed union whose members need
    /// not all be the same size; writing one member leaves the others'
    /// unwritten bits unchanged rather than making them invalid. Only legal on
    /// a `union`; `struct soft` is not a thing.
    #[cfg_attr(feature = "serde", serde(default))]
    pub soft: bool,
    pub signing: Option<Signing>,
    pub members: Vec<StructMember>,
    /// Packed array dimensions written AFTER the struct/union body
    /// (`struct packed {...} [N-1:0] x;` — a packed array of the aggregate,
    /// IEEE 1800-2017 §7.4.2). Empty for the usual unadorned struct.
    #[cfg_attr(feature = "serde", serde(default))]
    pub dimensions: Vec<PackedDimension>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StructUnionKind {
    Struct,
    Union,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StructMember {
    pub rand_qualifier: Option<RandQualifier>,
    pub data_type: DataType,
    pub declarators: Vec<StructDeclarator>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RandQualifier {
    Rand,
    Randc,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StructDeclarator {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub init: Option<expr::Expression>,
    pub span: Span,
}

/// enum type
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EnumType {
    pub base_type: Option<Box<DataType>>,
    pub members: Vec<EnumMember>,
    /// Packed array dimensions written AFTER the enum body
    /// (`enum {...} [1:0] x;` — a packed array of the enum, §7.4.2).
    /// Mirrors `StructUnionType::dimensions`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub dimensions: Vec<PackedDimension>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EnumMember {
    pub name: Identifier,
    pub range: Option<(expr::Expression, expr::Expression)>,
    pub init: Option<expr::Expression>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NetType {
    Wire,
    Tri,
    Wand,
    Wor,
    TriAnd,
    TriOr,
    Tri0,
    Tri1,
    Supply0,
    Supply1,
    TriReg,
    Uwire,
    Interconnect,
    /// Verilog-AMS `wreal` -- a net whose value is a real, not a
    /// vector of bits. Multiple drivers are SUMMED (see
    /// `ResolvedNetKind::RealSum`), which is the resolution the
    /// current-summing wrappers this simulator is pointed at rely
    /// on; the Verilog-AMS default leaves it tool-defined.
    Wreal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Lifetime {
    Static,
    Automatic,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PortDirection {
    Input,
    Output,
    Inout,
    Ref,
}
