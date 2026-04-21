//! SystemVerilog statements (IEEE 1800-2017 §A.6)


use super::{Identifier, Span};
use super::expr::Expression;
use super::types::{DataType, Lifetime, UnpackedDimension};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

impl Statement {
    pub fn new(kind: StatementKind, span: Span) -> Self { Self { kind, span } }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StatementKind {
    Null,
    Expr(Expression),
    BlockingAssign { lvalue: Expression, rvalue: Expression },
    NonblockingAssign { lvalue: Expression, delay: Option<Expression>, rvalue: Expression },
    If { unique_priority: Option<UniquePriority>, condition: Expression, then_stmt: Box<Statement>, else_stmt: Option<Box<Statement>> },
    Case { unique_priority: Option<UniquePriority>, kind: CaseKind, expr: Expression, items: Vec<CaseItem> },
    For { init: Vec<ForInit>, condition: Option<Expression>, step: Vec<Expression>, body: Box<Statement> },
    Foreach { array: Expression, vars: Vec<Option<Identifier>>, body: Box<Statement> },
    While { condition: Expression, body: Box<Statement> },
    DoWhile { body: Box<Statement>, condition: Expression },
    Repeat { count: Expression, body: Box<Statement> },
    Forever { body: Box<Statement> },
    SeqBlock { name: Option<Identifier>, stmts: Vec<Statement> },
    ParBlock { name: Option<Identifier>, join_type: JoinType, stmts: Vec<Statement> },
    TimingControl { control: TimingControl, stmt: Box<Statement> },
    EventTrigger { nonblocking: bool, name: Identifier, span: Span },
    Wait { condition: Expression, stmt: Box<Statement> },
    WaitFork,
    Disable(Identifier),
    Return(Option<Expression>),
    Break,
    Continue,
    Assertion(AssertionStatement),
    ProceduralContinuous(ProceduralContinuous),
    VarDecl { data_type: DataType, lifetime: Option<Lifetime>, declarators: Vec<VarDeclarator> },
    Coverpoint { name: Option<Identifier>, expr: Expression, span: Span },
    Cross { name: Option<Identifier>, items: Vec<Expression>, span: Span },
    /// Randsequence action-block boundary. Catches an `RsReturn` raised
    /// inside `body` so it exits only this production, not the whole
    /// sequence or the enclosing subroutine.
    RsAction { body: Box<Statement> },
    /// Randsequence `return` — terminates the current production's action
    /// block. Caught by the enclosing `RsAction`.
    RsReturn,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VarDeclarator {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub init: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UniquePriority { Unique, Unique0, Priority }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CaseKind { Case, Casex, Casez, CaseInside }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CaseItem {
    pub patterns: Vec<Expression>,
    pub is_default: bool,
    pub stmt: Statement,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ForInit {
    VarDecl { data_type: DataType, name: Identifier, init: Expression },
    Assign { lvalue: Expression, rvalue: Expression },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum JoinType { Join, JoinAny, JoinNone }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TimingControl {
    Delay(Expression),
    Event(EventControl),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EventControl {
    Star,
    ParenStar,
    Identifier(Identifier),
    HierIdentifier(Expression),
    EventExpr(Vec<EventExpr>),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EventExpr {
    pub edge: Option<Edge>,
    pub expr: Expression,
    pub iff: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Edge { Posedge, Negedge, Edge }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AssertionStatement {
    pub kind: AssertionKind,
    pub expr: Expression,
    pub action: Option<Box<Statement>>,
    pub else_action: Option<Box<Statement>>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AssertionKind { Assert, Assume, Cover }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProceduralContinuous {
    Assign { lvalue: Expression, rvalue: Expression },
    Deassign(Expression),
    Force { lvalue: Expression, rvalue: Expression },
    Release(Expression),
}
