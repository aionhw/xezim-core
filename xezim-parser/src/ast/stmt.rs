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
    /// INTERNAL (not parsed): marks the end of an inlined blocking task/method
    /// body in a process statement stream. When the simulator inlines a
    /// blocking call so its waits can suspend the process, it appends this
    /// sentinel; executing it pops + replays the call's deferred cleanup
    /// (frame/context unwind, output copy-back). See `task_cleanup`.
    ScopePop,
    /// INTERNAL (not parsed): for-loop step barrier. IEEE 1800-2017 §12.7.2 —
    /// `continue` skips the rest of the loop body but the `for` STEP still
    /// runs. The suspend-aware path lowers `for` to `while (cond) { body;
    /// step; }`, so a `continue` in a body that also suspends skipped the step
    /// too and the index never advanced — the loop spun forever. This sentinel
    /// sits between body and step: executing it consumes a pending `continue`
    /// so the step runs, while leaving `break`/`return` set so they still exit.
    LoopStep,
    /// IEEE 1800-2017 §9.6.3: `disable fork` aborts all currently
    /// active child processes of the enclosing scope's most-recent
    /// fork that haven't yet completed.
    DisableFork,
    Expr(Expression),
    BlockingAssign { lvalue: Expression, rvalue: Expression },
    NonblockingAssign { lvalue: Expression, delay: Option<Expression>, rvalue: Expression },
    If { unique_priority: Option<UniquePriority>, condition: Expression, then_stmt: Box<Statement>, else_stmt: Option<Box<Statement>> },
    Case { unique_priority: Option<UniquePriority>, kind: CaseKind, expr: Expression, items: Vec<CaseItem> },
    For { init: Vec<ForInit>, condition: Option<Expression>, step: Vec<Expression>, body: Box<Statement> },
    Foreach { array: Expression, vars: Vec<Option<Identifier>>, body: Box<Statement> },
    /// INTERNAL (not parsed): continuation sentinel for a `foreach` whose
    /// body can block (suspend). Mirrors how `while`/`for` re-append
    /// themselves so a process blocked at a timing control inside the loop
    /// body resumes at the NEXT iteration (IEEE 1800-2023 §9.4.3: a blocked
    /// process shall continue at the point of suspension) instead of
    /// restarting the whole `foreach` from index 0. Carries the materialized
    /// key list (frozen at loop entry) and the next index to execute.
    /// `var_scope` is the array's instance prefix, for aliased loop vars in
    /// submodule foreach bodies. `fe_auto_len` truncates `auto_loop_vars`.
    ForeachTail {
        loop_var: Option<String>,
        var_scope: Option<String>,
        body: Box<Statement>,
        keys: Vec<String>,
        is_str: bool,
        /// (key_width, key_signed) — the AA index type, so signed/narrowed
        /// keys round-trip through the tail continuation without a failed
        /// u64 parse clobbering them to 0.
        key_type: (u32, bool),
        idx: usize,
        fe_auto_len: usize,
        /// When set, `idx` is bounds-checked against the LIVE queue/dynamic-
        /// array size on every iteration resume (not the frozen `keys.len()`).
        /// IEEE 1800-2023 §12.7.3 leaves queue-during-foreach modification
        /// unspecified, but UVM routinely shrinks `arb_sequence_q` mid-loop;
        /// a frozen key list would then access deleted indices (QUEUEDEL).
        live_size_name: Option<String>,
    },
    While { condition: Expression, body: Box<Statement> },
    DoWhile { body: Box<Statement>, condition: Expression },
    Repeat { count: Expression, body: Box<Statement> },
    Forever { body: Box<Statement> },
    /// INTERNAL (not parsed): continuation sentinel for a `forever` whose
    /// body can block (suspend). Like `ForeachTail`, it distinguishes
    /// FIRST entry (the `Forever` arm, which runs the body's first
    /// iteration without gating) from RE-ENTRY after a suspension, so a
    /// `break`/`continue`/`return` raised inside the body is honored on
    /// resume (IEEE 1800-2023 §9.3.3) instead of being silently dropped
    /// while the loop re-arms. Carries only the body; the statements after
    /// the loop live in the surrounding flattened stream.
    ForeverTail { body: Box<Statement> },
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
    /// §18.16 `randcase` (and the alternatives of a §18.17 `randsequence`
    /// production): ONE branch is chosen at RUNTIME with probability
    /// weight_i / sum(weights). Both used to be lowered at parse time to the
    /// first non-zero-weight branch — i.e. not random at all.
    RandCase { items: Vec<(Expression, Statement)> },
    /// Block-local `typedef ...;` (§6.18). Registered when the enclosing
    /// process first executes it, so later VarDecls in the block resolve
    /// the name. Was parsed and DISCARDED before, which broke member access
    /// on locals of block-local packed-struct typedefs.
    Typedef(Box<crate::ast::decl::TypedefDeclaration>),
    Coverpoint { name: Option<Identifier>, expr: Expression, span: Span },
    Cross { name: Option<Identifier>, items: Vec<Expression>, span: Span },
    /// Randsequence action-block boundary. Catches an `RsReturn` raised
    /// inside `body` so it exits only this production, not the whole
    /// sequence or the enclosing subroutine.
    RsAction { body: Box<Statement> },
    /// Randsequence `return` — terminates the current production's action
    /// block. Caught by the enclosing `RsAction`.
    RsReturn,
    /// §15.5.3 `wait_order (a, b, c) pass_stmt else fail_stmt`. Appended LAST
    /// so older cached ASTs (which never contain it) keep their bincode
    /// variant indices. `armed`/`idx` are runtime continuation state: the
    /// executor re-pushes the statement with `armed = true` after parking on
    /// the remaining events, and `idx` is the next event expected to fire.
    WaitOrder {
        events: Vec<Identifier>,
        pass: Option<Box<Statement>>,
        fail: Option<Box<Statement>>,
        #[cfg_attr(feature = "serde", serde(default))]
        armed: bool,
        #[cfg_attr(feature = "serde", serde(default))]
        idx: u32,
        span: Span,
    },
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

/// IEEE 1800-2017 §12.6 pattern (for `case … matches` / `if … matches`).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Pattern {
    /// `.*` — matches anything, binds nothing.
    Wildcard,
    /// `.name` — matches anything and binds the subject to `name`.
    Binding(crate::ast::Identifier),
    /// `tagged Tag [sub_pattern]` — matches a tagged-union member (§7.3.2).
    Tagged { tag: crate::ast::Identifier, inner: Option<Box<Pattern>> },
    /// A constant expression the subject must equal.
    Expr(Expression),
    /// `'{ [name:] pat, … }` — structure pattern.
    Struct(Vec<(Option<crate::ast::Identifier>, Pattern)>),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CaseItem {
    pub patterns: Vec<Expression>,
    pub is_default: bool,
    pub stmt: Statement,
    pub span: Span,
    /// §12.6: the item's pattern in a `case (…) matches` statement. `None` for
    /// an ordinary case item (which uses `patterns` instead).
    #[cfg_attr(feature = "serde", serde(default))]
    pub pattern: Option<Pattern>,
    /// §12.6: the item's optional `&&& <guard>` expression.
    #[cfg_attr(feature = "serde", serde(default))]
    pub guard: Option<Expression>,
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
    /// `assert property (…)` / `assume property (…)` / `cover property (…)`.
    /// LRM §16.5: concurrent assertions evaluate in the observed region
    /// at the property's clocking event, not immediately at the statement
    /// site. Today's runtime distinguishes them by deferring evaluation —
    /// the inline predicate (`expr`) is queued into `pending_observed`
    /// instead of evaluated in place. Captured by the parser (the
    /// `property` keyword previously parsed via `is_property` was
    /// discarded; this field surfaces it for the executor).
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_property: bool,
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
