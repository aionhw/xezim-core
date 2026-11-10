//! SystemVerilog expressions (IEEE 1800-2017 §A.8)

use super::{Identifier, Span};
use super::cache::{LiteralCache, NameCache, SignalCache, WidthCache};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Expression {
    pub kind: ExprKind,
    pub span: Span,
    /// The self-determined width the simulator inferred for this node, when
    /// that width is a static property of the node (signal widths, packed
    /// layouts, literals, compositions of those). Filled lazily by
    /// `infer_width`; never filled for shapes whose width depends on runtime
    /// state (a local's current value, an evaluated fallback).
    #[cfg_attr(feature = "serde", serde(skip))]
    pub cached_width: WidthCache,
}

impl Expression {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self {
            kind,
            span,
            cached_width: crate::ast::cache::WidthCache::new(None),
        }
    }

    /// The pattern of a typed assignment pattern `T'{...}`, else `self`. Only
    /// where the context type is unpacked: `T` is then equivalent to it
    /// (§6.22.2) and the items place by the context type.
    pub fn peel_typed_pattern(&self) -> &Expression {
        match &self.kind {
            ExprKind::TypedPattern { pattern, .. } => pattern,
            _ => self,
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExprKind {
    Number(NumberLiteral),
    StringLiteral(String),
    /// A DATA TYPE used as an expression operand — `$bits(logic [7:0])`,
    /// `$size(byte)` (§20.6). Previously parsed and discarded (as `Empty`),
    /// so any ranged type collapsed to width 1.
    TypeLiteral(Box<crate::ast::types::DataType>),
    Ident(HierarchicalIdentifier),
    Unary {
        op: UnaryOp,
        operand: Box<Expression>,
    },
    Binary {
        op: BinaryOp,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Conditional {
        condition: Box<Expression>,
        then_expr: Box<Expression>,
        else_expr: Box<Expression>,
    },
    Concatenation(Vec<Expression>),
    Replication {
        count: Box<Expression>,
        exprs: Vec<Expression>,
    },
    AssignmentPattern(Vec<AssignmentPatternItem>),
    Call {
        func: Box<Expression>,
        args: Vec<Expression>,
    },
    SystemCall {
        name: String,
        args: Vec<Expression>,
    },
    NamedArg {
        name: Identifier,
        expr: Option<Box<Expression>>,
    },
    Inside {
        expr: Box<Expression>,
        ranges: Vec<Expression>,
    },
    /// §12.6 `expr matches pattern` — a boolean conditional-pattern match.
    /// Any `.name` bindings in the pattern are visible in the enclosing `if`'s
    /// then-branch.
    Matches {
        expr: Box<Expression>,
        pattern: Box<crate::ast::stmt::Pattern>,
    },
    MemberAccess {
        expr: Box<Expression>,
        member: Identifier,
    },
    /// §8.25 parameterized-class specialization in a scoped reference, e.g. the
    /// `C#(int,"a")` in `C#(int,"a")::member`. `base` is the (unparameterized)
    /// class reference; `type_args_text` is the canonical raw text of the
    /// `#(...)` parameter list (used to key per-specialization statics under
    /// PURE_SV_LRM). Default mode treats this transparently as `base` — the
    /// simulator's `eval_expr` unwraps it — so behavior is unchanged there.
    Specialization {
        base: Box<Expression>,
        type_args_text: String,
    },
    Index {
        expr: Box<Expression>,
        index: Box<Expression>,
    },
    RangeSelect {
        expr: Box<Expression>,
        kind: RangeKind,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Range(Box<Expression>, Box<Expression>),
    Paren(Box<Expression>),
    Dollar,
    Null,
    This,
    Empty,
    /// Array method with `with` clause: `expr.method with (filter)`
    WithClause {
        expr: Box<Expression>,
        filter: Box<Expression>,
    },
    /// `<call> with { constraints }` — randomize (incl. `std::randomize`) with
    /// an inline constraint block. `call` is the underlying randomize call.
    RandomizeWith {
        call: Box<Expression>,
        constraints: Vec<super::decl::ConstraintItem>,
    },
    /// Assignment as an expression: `(a = b)` or `(a += 1)`. Returns the
    /// assigned value (after any compound-op evaluation).
    AssignExpr {
        lvalue: Box<Expression>,
        rvalue: Box<Expression>,
    },
    /// Streaming concat: `{<<slice {exprs}}` (left_to_right=true) or `{>>slice {...}}`.
    /// slice_size is None when no slice expression was given (defaults to 1).
    StreamOp {
        left_to_right: bool,
        slice_size: Option<Box<Expression>>,
        exprs: Vec<Expression>,
    },
    /// Tagged union constructor: `tagged Name` or `tagged Name (expr)`.
    Tagged {
        tag: Identifier,
        inner: Option<Box<Expression>>,
    },
    /// §16.5 / §9.4.2: a property sampled on the union of its clocking
    /// event terms. Each term keeps its own edge and optional iff guard.
    SvaClocked {
        events: Vec<super::stmt::EventExpr>,
        body: Box<Expression>,
    },
    /// LRM §8.8: the shallow-copy constructor `new <handle>` (parentheseless
    /// `new <expr>` where `<expr>` is an object handle, footnote 23) — a
    /// shallow copy, NOT a constructor call. `new(args)` stays an ordinary
    /// `Call`. APPENDED LAST so older cached ASTs keep their bincode
    /// variant indices (format version bumped regardless).
    ShallowCopy {
        source: Box<Expression>,
    },
    /// §10.9: a typed assignment pattern `T'{...}`, the value a variable of
    /// type `ty` initialized with `pattern` (an `AssignmentPattern`) holds.
    TypedPattern {
        ty: Box<crate::ast::types::DataType>,
        pattern: Box<Expression>,
    },
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
    /// Indexed/keyed: `'{<expr>: <expr>, ...}` — used for associative
    /// arrays and dictionary-style aggregates (IEEE 1800-2023 §10.10).
    Keyed(Expression, Expression),
}

impl AssignmentPatternItem {
    pub fn expr(&self) -> &Expression {
        match self {
            Self::Ordered(e) => e,
            Self::Named(_, e) => e,
            Self::Typed(_, e) => e,
            Self::Default(e) => e,
            Self::Keyed(_, e) => e,
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NumberLiteral {
    Integer {
        size: Option<u32>,
        signed: bool,
        base: NumberBase,
        value: String,
        #[cfg_attr(feature = "serde", serde(skip))]
        cached_val: LiteralCache,
    },
    Real(f64),
    UnbasedUnsized(char),
    /// Time literal `<number><unit>` (`10ns`, `5ps`, …), value stored in
    /// ABSOLUTE SECONDS (LRM §22.7). Kept distinct from `Real` so the simulator
    /// can convert it against the global tick precision, while a *bare* delay
    /// `#5` (no unit) is scaled by its module's timeunit instead. Conflating the
    /// two (the old `Real(ns)` form) broke relative timing in sub-ns timescales.
    Time(f64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NumberBase {
    Decimal,
    Binary,
    Octal,
    Hex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RangeKind {
    Constant,
    IndexedUp,
    IndexedDown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnaryOp {
    Plus,
    Minus,
    LogNot,
    BitNot,
    BitAnd,
    BitNand,
    BitOr,
    BitNor,
    BitXor,
    BitXnor,
    PreIncr,
    PreDecr,
    PostIncr,
    PostDecr,
    HashHash,
    /// LRM §16.12.6 — `s_eventually <expr>` (strong eventually).
    /// `s_always <expr>` and friends use the same Unary encoding.
    SEventually,
    SAlways,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Power,
    Eq,
    Neq,
    CaseEq,
    CaseNeq,
    WildcardEq,
    WildcardNeq,
    LogAnd,
    LogOr,
    LogImplies,
    LogEquiv,
    Lt,
    Leq,
    Gt,
    Geq,
    BitAnd,
    BitOr,
    BitXor,
    BitXnor,
    ShiftLeft,
    ShiftRight,
    ArithShiftLeft,
    ArithShiftRight,
    Assign,
    OrMinusArrow,
    OrFatArrow,
    HashHash,
    Iff,
    /// LRM §16.9 sequence operators. `Throughout` (`expr throughout seq`),
    /// `Within` (`seq1 within seq2`), `Intersect`, `SeqAnd`/`SeqOr`
    /// (sequence `and`/`or`), `Until`/`SUntil` (`until`/`s_until`).
    Throughout,
    Within,
    Intersect,
    SeqAnd,
    SeqOr,
    Until,
    SUntil,
    /// Property/sequence keyword `and` (§16.9.5 / §16.12.3). Distinct from
    /// `SeqAnd`, which the parser uses for cycle-delay CONCATENATION
    /// (`a ##1 b`).
    SvaAnd,
    /// `disable iff (guard) property`: `left` is the guard, `right` the
    /// property (§16.12).
    SvaDisableIff,
}

/// `HierarchicalIdentifier::root` of a §18.7.1 `local::name` reference.
pub const LOCAL_SCOPE_ROOT: &str = "local";

#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HierarchicalIdentifier {
    pub root: Option<String>,
    pub path: Vec<HierPathSegment>,
    pub span: Span,
    /// Cached signal ID for fast lookup during simulation (set on first access).
    #[cfg_attr(feature = "serde", serde(skip))]
    pub cached_signal_id: SignalCache,
    /// Cached resolved hierarchical name (set on first call to
    /// `resolve_hier_name`). Bypasses all path-joining, prefix-stripping and
    /// suffix-scanning on repeat calls — the dominant cost for tight
    /// memory-init loops and `arr[i]` accesses in hot paths.
    #[cfg_attr(feature = "serde", serde(skip))]
    pub cached_resolved_name: NameCache,
    /// §23.9: the binding of the head segment, decided per definition before
    /// expansion.
    #[cfg_attr(feature = "serde", serde(skip))]
    pub bound: super::binding::Bound,
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
