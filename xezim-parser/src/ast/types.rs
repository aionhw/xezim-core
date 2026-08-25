//! SystemVerilog data types (IEEE 1800-2017 §6, §7)


use super::{Identifier, Span, expr};

/// Data type AST node.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DataType {
    IntegerVector { kind: IntegerVectorType, signing: Option<Signing>, dimensions: Vec<PackedDimension>, span: Span },
    IntegerAtom { kind: IntegerAtomType, signing: Option<Signing>, span: Span },
    Real { kind: RealType, span: Span },
    Simple { kind: SimpleType, span: Span },
    Struct(StructUnionType),
    Enum(EnumType),
    Void(Span),
    TypeReference { name: TypeName, dimensions: Vec<PackedDimension>, type_args: Vec<expr::Expression>, span: Span },
    Interface { name: Identifier, modport: Option<Identifier>, span: Span },
    Implicit { signing: Option<Signing>, dimensions: Vec<PackedDimension>, span: Span },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeName {
    pub scope: Option<Identifier>,
    pub name: Identifier,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IntegerVectorType { Bit, Logic, Reg }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IntegerAtomType { Byte, ShortInt, Int, LongInt, Integer, Time }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RealType { Real, ShortReal, RealTime }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SimpleType { String, Chandle, Event }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Signing { Signed, Unsigned }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PackedDimension {
    Range { left: Box<expr::Expression>, right: Box<expr::Expression>, span: Span },
    Unsized(Span),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnpackedDimension {
    Range { left: Box<expr::Expression>, right: Box<expr::Expression>, span: Span },
    Expression { expr: Box<expr::Expression>, span: Span },
    Unsized(Span),
    Queue { max_size: Option<Box<expr::Expression>>, span: Span },
    Associative { data_type: Option<Box<DataType>>, span: Span },
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
pub enum StructUnionKind { Struct, Union }

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
pub enum RandQualifier { Rand, Randc }

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
pub enum NetType { Wire, Tri, Wand, Wor, TriAnd, TriOr, Tri0, Tri1, Supply0, Supply1, TriReg, Uwire, Interconnect }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Lifetime { Static, Automatic }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PortDirection { Input, Output, Inout, Ref }
