//! SystemVerilog expressions (IEEE 1800-2017 §A.8)


use std::cell::Cell;
use super::{Identifier, Span};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Expression {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expression {
    pub fn new(kind: ExprKind, span: Span) -> Self { Self { kind, span } }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExprKind {
    Number(NumberLiteral),
    StringLiteral(String),
    Ident(HierarchicalIdentifier),
    Unary { op: UnaryOp, operand: Box<Expression> },
    Binary { op: BinaryOp, left: Box<Expression>, right: Box<Expression> },
    Conditional { condition: Box<Expression>, then_expr: Box<Expression>, else_expr: Box<Expression> },
    Concatenation(Vec<Expression>),
    Replication { count: Box<Expression>, exprs: Vec<Expression> },
    AssignmentPattern(Vec<AssignmentPatternItem>),
    Call { func: Box<Expression>, args: Vec<Expression> },
    SystemCall { name: String, args: Vec<Expression> },
    NamedArg { name: Identifier, expr: Option<Box<Expression>> },
    Inside { expr: Box<Expression>, ranges: Vec<Expression> },
    MemberAccess { expr: Box<Expression>, member: Identifier },
    Index { expr: Box<Expression>, index: Box<Expression> },
    RangeSelect { expr: Box<Expression>, kind: RangeKind, left: Box<Expression>, right: Box<Expression> },
    Range(Box<Expression>, Box<Expression>),
    Paren(Box<Expression>),
    Dollar,
    Null,
    This,
    Empty,
    /// Array method with `with` clause: `expr.method with (filter)`
    WithClause { expr: Box<Expression>, filter: Box<Expression> },
    /// Assignment as an expression: `(a = b)` or `(a += 1)`. Returns the
    /// assigned value (after any compound-op evaluation).
    AssignExpr { lvalue: Box<Expression>, rvalue: Box<Expression> },
    /// Streaming concat: `{<<slice {exprs}}` (left_to_right=true) or `{>>slice {...}}`.
    /// slice_size is None when no slice expression was given (defaults to 1).
    StreamOp { left_to_right: bool, slice_size: Option<Box<Expression>>, exprs: Vec<Expression> },
    /// Tagged union constructor: `tagged Name` or `tagged Name (expr)`.
    Tagged { tag: Identifier, inner: Option<Box<Expression>> },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AssignmentPatternItem {
    /// Ordered: `'{expr, expr}`
    Ordered(Expression),
    /// Named: `'{name: expr, name: expr}`
    Named(Identifier, Expression),
    /// Typed: `'{type: expr}`
    Typed(super::types::DataType, Expression),
    /// Default: `'{default: expr}`
    Default(Expression),
}

impl AssignmentPatternItem {
    pub fn expr(&self) -> &Expression {
        match self {
            Self::Ordered(e) => e,
            Self::Named(_, e) => e,
            Self::Typed(_, e) => e,
            Self::Default(e) => e,
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NumberLiteral {
    Integer { size: Option<u32>, signed: bool, base: NumberBase, value: String, #[cfg_attr(feature = "serde", serde(skip))] cached_val: Cell<Option<(u64, u64, u32)>> },
    Real(f64),
    UnbasedUnsized(char),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NumberBase { Decimal, Binary, Octal, Hex }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RangeKind { Constant, IndexedUp, IndexedDown }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnaryOp {
    Plus, Minus, LogNot, BitNot, BitAnd, BitNand, BitOr, BitNor, BitXor, BitXnor,
    PreIncr, PreDecr, PostIncr, PostDecr,
    HashHash,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BinaryOp {
    Add, Sub, Mul, Div, Mod, Power,
    Eq, Neq, CaseEq, CaseNeq, WildcardEq, WildcardNeq,
    LogAnd, LogOr, LogImplies, LogEquiv,
    Lt, Leq, Gt, Geq,
    BitAnd, BitOr, BitXor, BitXnor,
    ShiftLeft, ShiftRight, ArithShiftLeft, ArithShiftRight,
    Assign,
    OrMinusArrow, OrFatArrow,
    HashHash,
    Iff,
}

#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HierarchicalIdentifier {
    pub root: Option<String>,
    pub path: Vec<HierPathSegment>,
    pub span: Span,
    /// Cached signal ID for fast lookup during simulation (set on first access).
    #[cfg_attr(feature = "serde", serde(skip))]
    pub cached_signal_id: Cell<Option<usize>>,
}

impl std::fmt::Debug for HierarchicalIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HierarchicalIdentifier")
            .field("root", &self.root)
            .field("path", &self.path)
            .field("span", &self.span)
            .finish()
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HierPathSegment {
    pub name: Identifier,
    pub selects: Vec<Expression>,
}
