//! SystemC / C++ types as the lowering sees them, and their SystemVerilog
//! equivalents (IEEE 1666-2023 §7 data types onto IEEE 1800-2017 §6).

use std::collections::BTreeMap;

use super::build::*;
use crate::ast::expr::{BinaryOp, Expression};
use crate::ast::types::{
    DataType, IntegerAtomType, PackedDimension, RealType, SimpleType, UnpackedDimension,
};
use crate::sv_parser::systemc::ast::{self as sc, TemplateArg, TypeName};

/// A bit width: known (`n`) or symbolic (a template parameter), with the SV
/// expression that spells it either way.
#[derive(Debug, Clone)]
pub struct Width {
    pub n: Option<u32>,
    pub expr: Expression,
}

impl Width {
    pub fn known(n: u32) -> Self {
        Width {
            n: Some(n),
            expr: int(n as i64),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Ty {
    Bool,
    /// `sc_uint`/`sc_int`/`sc_biguint`/`sc_bigint` (`bv: false`) and `sc_bv`
    /// (`bv: true`, printed as a bit string): two-state vectors.
    Vec2 {
        w: Width,
        signed: bool,
        bv: bool,
    },
    /// `sc_logic` (`w` = 1) and `sc_lv`: four-state.
    Vec4 {
        w: Width,
    },
    /// C++ integers; `ch` for the character types `cout` prints as text.
    Int {
        bits: u32,
        signed: bool,
        ch: bool,
    },
    Real {
        single: bool,
    },
    Str,
    /// `sc_time`, in picoseconds.
    Time,
    Void,
    /// A C++ object of a class (a user class `sc_c_<name>` or a runtime
    /// class such as `scrt_tlm_gp`), by value or by reference: an SV class
    /// handle to the object itself. C++ copies a value on assignment and
    /// initialization (`__sc_set`, `__sc_copy`); a reference names it.
    Class(String),
    /// A C++ pointer to an object of the class: a handle, shared.
    Handle(String),
    /// A C++ output stream other than `std::cout` (`std::ostream&` in an
    /// `operator<<`, `std::ostringstream`): the text written so far.
    OStream,
    /// A C++ data pointer (`scrt_ptr`); `elem` is the pointee size in bytes.
    Ptr {
        elem: u32,
    },
    Mailbox(Box<Ty>),
    Event,
    /// A fixed-size C array.
    Array(Box<Ty>, Expression),
    /// `std::vector<T>`, a queue.
    Queue(Box<Ty>),
}

impl Ty {
    pub fn int32() -> Ty {
        Ty::Int {
            bits: 32,
            signed: true,
            ch: false,
        }
    }

    pub fn is_scalar_bits(&self) -> bool {
        matches!(
            self,
            Ty::Bool | Ty::Vec2 { .. } | Ty::Vec4 { .. } | Ty::Int { .. }
        )
    }

    /// Size in bytes for `sizeof` and pointer element arithmetic.
    pub fn byte_size(&self) -> Option<u64> {
        Some(match self {
            Ty::Bool => 1,
            Ty::Int { bits, .. } => (*bits / 8) as u64,
            Ty::Real { single: true } => 4,
            Ty::Real { single: false } => 8,
            Ty::Time => 8,
            Ty::Vec2 { w, .. } | Ty::Vec4 { w, .. } => {
                let n = w.n?;
                if n <= 64 {
                    8
                } else {
                    n.div_ceil(64) as u64 * 8
                }
            }
            _ => return None,
        })
    }
}

/// The SV type of `ty`, with the unpacked dimensions a declarator of it needs.
pub fn sv_type(ty: &Ty) -> (DataType, Vec<UnpackedDimension>) {
    match ty {
        Ty::Array(elem, n) => {
            let (dt, mut dims) = sv_type(elem);
            dims.insert(0, unpacked(n.clone()));
            (dt, dims)
        }
        Ty::Queue(elem) => {
            let (dt, mut dims) = sv_type(elem);
            dims.insert(
                0,
                UnpackedDimension::Queue {
                    max_size: None,
                    span: sp(),
                },
            );
            (dt, dims)
        }
        other => (sv_scalar_type(other), Vec::new()),
    }
}

fn vec_dims(w: &Width) -> Vec<PackedDimension> {
    if w.n == Some(1) {
        return Vec::new();
    }
    vec![PackedDimension::Range {
        left: Box::new(match w.n {
            Some(n) => int(n as i64 - 1),
            None => bin(BinaryOp::Sub, w.expr.clone(), int(1)),
        }),
        right: Box::new(int(0)),
        span: sp(),
    }]
}

pub fn sv_scalar_type(ty: &Ty) -> DataType {
    use crate::ast::types::{IntegerVectorType, Signing};
    match ty {
        Ty::Bool => bit_t(1, false),
        Ty::Vec2 { w, signed, .. } => DataType::IntegerVector {
            kind: IntegerVectorType::Bit,
            signing: signed.then_some(Signing::Signed),
            dimensions: vec_dims(w),
            span: sp(),
        },
        Ty::Vec4 { w, .. } => DataType::IntegerVector {
            kind: IntegerVectorType::Logic,
            signing: None,
            dimensions: vec_dims(w),
            span: sp(),
        },
        Ty::Int { bits, signed, .. } => {
            let kind = match bits {
                8 => IntegerAtomType::Byte,
                16 => IntegerAtomType::ShortInt,
                64 => IntegerAtomType::LongInt,
                _ => IntegerAtomType::Int,
            };
            atom_t(kind, !signed)
        }
        Ty::Real { single } => real_t(if *single {
            RealType::ShortReal
        } else {
            RealType::Real
        }),
        Ty::Str | Ty::OStream => simple_t(SimpleType::String),
        Ty::Time => atom_t(IntegerAtomType::LongInt, true),
        Ty::Void => void_t(),
        Ty::Class(n) | Ty::Handle(n) => named_t(n, Vec::new()),
        Ty::Ptr { .. } => named_t("scrt_ptr", Vec::new()),
        // sc_fifo (§6.23): the runtime's update-phase FIFO.
        Ty::Mailbox(elem) => named_t("scrt_fifo", vec![type_arg(&sv_scalar_type(elem))]),
        Ty::Event => simple_t(SimpleType::Event),
        Ty::Array(elem, _) | Ty::Queue(elem) => sv_scalar_type(elem),
    }
}

/// What a template parameter of the module or class being lowered stands
/// for.
#[derive(Debug, Clone)]
pub enum TParam {
    /// A value parameter of a module kept generic: its SV parameter name.
    Value(String),
    /// A value parameter of an instantiated template: its value.
    Const(i64),
    /// A type parameter of an instantiated template: its type.
    Type(Ty),
}

/// A template argument, resolved.
#[derive(Debug, Clone)]
pub enum TArg {
    Ty(Ty),
    Val(i64),
}

/// One instantiation of a class or module template.
#[derive(Debug, Clone)]
pub struct Instantiation {
    pub template: String,
    pub args: Vec<TArg>,
}

/// Names the type mapping resolves: typedefs, enums, template parameters,
/// the user's (non-module) classes and the class and module templates.
#[derive(Debug, Default, Clone)]
pub struct TyEnv {
    pub typedefs: BTreeMap<String, sc::Type>,
    pub enums: std::collections::BTreeSet<String>,
    pub classes: std::collections::BTreeSet<String>,
    pub tparams: BTreeMap<String, TParam>,
    /// Templates instantiated per argument list (those with a type
    /// parameter, and non-module classes): name → parameters.
    pub templates: BTreeMap<String, Vec<sc::TemplateParam>>,
    /// The instantiations found so far, by their (mangled) name.
    pub instances: std::rc::Rc<std::cell::RefCell<BTreeMap<String, Instantiation>>>,
}

/// A type in an instantiation's name: `sc_uint<8>` → `sc_uint8`.
pub fn mangle_ty(t: &Ty) -> String {
    match t {
        Ty::Bool => "bool".into(),
        Ty::Vec2 { w, signed, bv } => format!(
            "{}{}",
            if *bv {
                "sc_bv"
            } else if *signed {
                "sc_int"
            } else {
                "sc_uint"
            },
            w.n.map_or_else(|| "W".to_string(), |n| n.to_string())
        ),
        Ty::Vec4 { w } => format!("sc_lv{}", w.n.map_or_else(|| "W".to_string(), |n| n.to_string())),
        Ty::Int { bits, signed, ch } => match (bits, signed, ch) {
            (8, _, true) => "char".into(),
            (_, true, _) => format!("int{}", bits),
            (_, false, _) => format!("uint{}", bits),
        },
        Ty::Real { single: true } => "float".into(),
        Ty::Real { single: false } => "double".into(),
        Ty::Str => "string".into(),
        Ty::Time => "sc_time".into(),
        Ty::Class(c) | Ty::Handle(c) => c.trim_start_matches("sc_c_").to_string(),
        Ty::Ptr { elem } => format!("ptr{}", elem),
        Ty::Queue(e) => format!("vector_{}", mangle_ty(e)),
        Ty::Array(e, _) => format!("array_{}", mangle_ty(e)),
        Ty::Mailbox(e) => format!("fifo_{}", mangle_ty(e)),
        Ty::Event => "event".into(),
        Ty::OStream => "ostream".into(),
        Ty::Void => "void".into(),
    }
}

/// The name of an instantiation: `dpipe<atom, 4>` → `dpipe__sc_uint121__4`.
pub fn instance_name(template: &str, args: &[TArg]) -> String {
    let mut n = template.to_string();
    for a in args {
        n.push_str("__");
        match a {
            TArg::Ty(t) => n.push_str(&mangle_ty(t)),
            TArg::Val(v) if *v < 0 => n.push_str(&format!("m{}", -v)),
            TArg::Val(v) => n.push_str(&v.to_string()),
        }
    }
    n
}

/// Resolve the arguments of `q` for a template with `params` (defaults
/// filling the missing ones).
pub fn template_args(
    q: &sc::QualifiedName,
    params: &[sc::TemplateParam],
    env: &TyEnv,
    consts: &dyn Fn(&sc::Expr) -> Option<i64>,
) -> Result<Vec<TArg>, String> {
    let given = q.last_args().unwrap_or(&[]);
    let mut out = Vec::new();
    for (i, p) in params.iter().enumerate() {
        let arg = given.get(i);
        match p {
            sc::TemplateParam::Type { default, .. } => {
                let t = match arg {
                    Some(TemplateArg::Type(t)) => ty_of(t, env, consts)?,
                    Some(TemplateArg::Expr(e)) => match &e.kind {
                        sc::ExprKind::Name(n) => ty_of_name(n, env, consts)?,
                        _ => return Err(format!("'{}' needs a type argument", q.last_name())),
                    },
                    None => match default {
                        Some(d) => ty_of(d, env, consts)?,
                        None => return Err(format!("too few template arguments for '{}'", q.last_name())),
                    },
                };
                out.push(TArg::Ty(t));
            }
            sc::TemplateParam::Value { default, .. } => {
                let v = match arg {
                    Some(TemplateArg::Expr(e)) => const_arg(e, env, consts),
                    Some(TemplateArg::Type(t)) => t.name().and_then(|n| match env.tparams.get(n.last_name()) {
                        Some(TParam::Const(v)) => Some(*v),
                        _ => None,
                    }),
                    None => default.as_ref().and_then(|d| const_arg(d, env, consts)),
                };
                match v {
                    Some(v) => out.push(TArg::Val(v)),
                    None => return Err(format!("a template argument of '{}' is not a constant", q.last_name())),
                }
            }
        }
    }
    if given.len() > params.len() {
        return Err(format!("too many template arguments for '{}'", q.last_name()));
    }
    Ok(out)
}

/// A constant template argument: a literal, a constant, or a value
/// parameter of the template being instantiated.
fn const_arg(e: &sc::Expr, env: &TyEnv, consts: &dyn Fn(&sc::Expr) -> Option<i64>) -> Option<i64> {
    consts(e).or_else(|| match &e.kind {
        sc::ExprKind::Name(q) if q.segments.len() == 1 => match env.tparams.get(q.last_name()) {
            Some(TParam::Const(v)) => Some(*v),
            _ => None,
        },
        _ => None,
    })
}

/// The instantiation `q` names, if `q` is a template with arguments (or a
/// template's own name inside it): registered, and its name returned.
pub fn instantiate(
    q: &sc::QualifiedName,
    env: &TyEnv,
    consts: &dyn Fn(&sc::Expr) -> Option<i64>,
) -> Result<Option<String>, String> {
    let name = q.last_name();
    let Some(params) = env.templates.get(name) else {
        return Ok(None);
    };
    if q.last_args().is_none() && !params.iter().all(|p| match p {
        sc::TemplateParam::Type { default, .. } => default.is_some(),
        sc::TemplateParam::Value { default, .. } => default.is_some(),
    }) {
        return Ok(None);
    }
    let args = template_args(q, params, env, consts)?;
    let n = instance_name(name, &args);
    env.instances
        .borrow_mut()
        .entry(n.clone())
        .or_insert_with(|| Instantiation {
            template: name.to_string(),
            args,
        });
    Ok(Some(n))
}

/// Library namespaces a qualified name may carry; they are dropped.
pub fn is_library_ns(n: &str) -> bool {
    matches!(n, "std" | "sc_core" | "sc_dt" | "tlm" | "tlm_utils")
}

/// A constant width argument: a literal, or a value template parameter.
fn width_arg(
    args: Option<&[TemplateArg]>,
    env: &TyEnv,
    consts: &dyn Fn(&sc::Expr) -> Option<i64>,
) -> Result<Width, String> {
    let Some(arg) = args.and_then(|a| a.first()) else {
        return Err("missing width argument".to_string());
    };
    match arg {
        TemplateArg::Expr(e) => {
            if let Some(v) = consts(e) {
                return Ok(Width::known(v as u32));
            }
            if let sc::ExprKind::Name(q) = &e.kind
                && q.segments.len() == 1
            {
                match env.tparams.get(q.last_name()) {
                    Some(TParam::Value(sv)) => {
                        return Ok(Width {
                            n: None,
                            expr: ident(sv),
                        });
                    }
                    Some(TParam::Const(v)) => return Ok(Width::known(*v as u32)),
                    _ => {}
                }
            }
            Err("width is not a constant".to_string())
        }
        TemplateArg::Type(t) => {
            // A bare name parsed as a type: a template value parameter.
            if let Some(q) = t.name() {
                match env.tparams.get(q.last_name()) {
                    Some(TParam::Value(sv)) => {
                        return Ok(Width {
                            n: None,
                            expr: ident(sv),
                        });
                    }
                    Some(TParam::Const(v)) => return Ok(Width::known(*v as u32)),
                    _ => {}
                }
            }
            Err("width is not a constant".to_string())
        }
    }
}

fn first_type_arg(
    q: &sc::QualifiedName,
    env: &TyEnv,
    consts: &dyn Fn(&sc::Expr) -> Option<i64>,
) -> Result<Ty, String> {
    match q.last_args().and_then(|a| a.first()) {
        Some(TemplateArg::Type(t)) => ty_of(t, env, consts),
        Some(TemplateArg::Expr(e)) => match &e.kind {
            sc::ExprKind::Name(n) => ty_of_name(n, env, consts),
            _ => Err(format!("'{}' needs a type argument", q.last_name())),
        },
        None => Err(format!("'{}' needs a type argument", q.last_name())),
    }
}

fn builtin(s: &str) -> Option<Ty> {
    let words: Vec<&str> = s.split_whitespace().collect();
    let has = |w: &str| words.contains(&w);
    if has("void") {
        return Some(Ty::Void);
    }
    if has("bool") {
        return Some(Ty::Bool);
    }
    if has("double") {
        return Some(Ty::Real { single: false });
    }
    if has("float") {
        return Some(Ty::Real { single: true });
    }
    let unsigned = has("unsigned");
    if has("char") {
        return Some(Ty::Int {
            bits: 8,
            signed: !unsigned,
            ch: true,
        });
    }
    let longs = words.iter().filter(|w| **w == "long").count();
    let bits = if has("short") {
        16
    } else if longs >= 1 {
        64
    } else {
        32
    };
    Some(Ty::Int {
        bits,
        signed: !unsigned,
        ch: false,
    })
}

/// The lowering type of a SystemC/C++ type (pointer parts included).
pub fn ty_of(
    t: &sc::Type,
    env: &TyEnv,
    consts: &dyn Fn(&sc::Expr) -> Option<i64>,
) -> Result<Ty, String> {
    let base = match &t.base {
        TypeName::Builtin(s) => builtin(s).ok_or_else(|| format!("unsupported type '{}'", s))?,
        TypeName::Named(q) | TypeName::Elaborated { name: q, .. } => ty_of_name(q, env, consts)?,
        TypeName::Auto => {
            return Err("'auto' needs an initializer type; spell the type out".to_string());
        }
        TypeName::Decltype(_) => return Err("'decltype' is not supported".to_string()),
        TypeName::ClassDef(_) | TypeName::EnumDef(_) => {
            return Err("an inline class or enum definition is not supported here".to_string());
        }
        TypeName::Function { .. } => return Err("function types are not supported".to_string()),
    };
    // `const char*` is a C string.
    let is_c_string = t.is_const
        && matches!(
            base,
            Ty::Int {
                bits: 8,
                ch: true,
                ..
            }
        )
        && t.ptr_ops
            .iter()
            .filter(|o| matches!(o, sc::PtrOp::Pointer { .. }))
            .count()
            == 1;
    if is_c_string {
        return Ok(Ty::Str);
    }
    apply_ptr(base, &t.ptr_ops)
}

/// `base` seen through declarator pointer/reference parts: references are
/// transparent, a pointer to bytes is a data pointer, a pointer to an object
/// is a handle, and `const char*` is a string.
pub fn apply_ptr(base: Ty, ops: &[sc::PtrOp]) -> Result<Ty, String> {
    let ptrs = ops
        .iter()
        .filter(|o| matches!(o, sc::PtrOp::Pointer { .. }))
        .count();
    match ptrs {
        0 => Ok(base),
        1 => Ok(match base {
            Ty::Int { bits, .. } => Ty::Ptr { elem: bits / 8 },
            Ty::Bool => Ty::Ptr { elem: 1 },
            Ty::Void => Ty::Ptr { elem: 1 },
            Ty::Class(c) => Ty::Handle(c),
            Ty::Vec2 { .. } | Ty::Vec4 { .. } | Ty::Real { .. } | Ty::Time => Ty::Ptr {
                elem: base.byte_size().unwrap_or(1) as u32,
            },
            other => return Err(format!("pointers to {:?} are not supported", other)),
        }),
        _ => Err("pointers to pointers are not supported".to_string()),
    }
}

pub fn ty_of_name(
    q: &sc::QualifiedName,
    env: &TyEnv,
    consts: &dyn Fn(&sc::Expr) -> Option<i64>,
) -> Result<Ty, String> {
    let name = q.last_name();
    if q.segments.len() == 1
        && let Some(tp) = env.tparams.get(name)
    {
        return match tp {
            TParam::Type(t) => Ok(t.clone()),
            TParam::Value(_) | TParam::Const(_) => Err(format!("'{}' is a value, not a type", name)),
        };
    }
    // A class template's instantiation.
    if let Some(inst) = instantiate(q, env, consts)? {
        return Ok(Ty::Class(format!("sc_c_{}", inst)));
    }
    if let Some(t) = env.typedefs.get(name) {
        return ty_of(t, env, consts);
    }
    if env.enums.contains(name) {
        return Ok(Ty::int32());
    }
    if env.classes.contains(name) {
        return Ok(Ty::Class(format!("sc_c_{}", name)));
    }
    let args = q.last_args();
    let u = |bits, signed| Ty::Int {
        bits,
        signed,
        ch: false,
    };
    Ok(match name {
        "bool" | "sc_bit" => Ty::Bool,
        "sc_uint" | "sc_biguint" => Ty::Vec2 {
            w: width_arg(args, env, consts)?,
            signed: false,
            bv: false,
        },
        "sc_int" | "sc_bigint" => Ty::Vec2 {
            w: width_arg(args, env, consts)?,
            signed: true,
            bv: false,
        },
        "sc_bv" => Ty::Vec2 {
            w: width_arg(args, env, consts)?,
            signed: false,
            bv: true,
        },
        "sc_lv" => Ty::Vec4 {
            w: width_arg(args, env, consts)?,
        },
        "sc_logic" => Ty::Vec4 { w: Width::known(1) },
        "int8_t" => Ty::Int {
            bits: 8,
            signed: true,
            ch: true,
        },
        "uint8_t" => Ty::Int {
            bits: 8,
            signed: false,
            ch: true,
        },
        "int16_t" => u(16, true),
        "uint16_t" => u(16, false),
        "int32_t" => u(32, true),
        "uint32_t" => u(32, false),
        "int64_t" | "int64" | "ssize_t" | "ptrdiff_t" | "intptr_t" => u(64, true),
        "uint64_t" | "uint64" | "size_t" | "uintptr_t" => u(64, false),
        "string" => Ty::Str,
        "ostringstream" | "stringstream" | "ostream" => Ty::OStream,
        "sc_time" => Ty::Time,
        "sc_event" => Ty::Event,
        "tlm_generic_payload" => Ty::Class("scrt_tlm_gp".to_string()),
        "sc_mutex" => Ty::Class("scrt_mutex".to_string()),
        "sc_semaphore" => Ty::Class("scrt_semaphore".to_string()),
        "sc_event_queue" => Ty::Class("scrt_event_queue".to_string()),
        "sc_spawn_options" => Ty::Class("scrt_spawn_opts".to_string()),
        "sc_process_handle" => Ty::Handle("scrt_proc".to_string()),
        "tlm_command"
        | "tlm_response_status"
        | "tlm_sync_enum"
        | "tlm_phase"
        | "tlm_phase_enum" => Ty::int32(),
        "vector" => Ty::Queue(Box::new(first_type_arg(q, env, consts)?)),
        "sc_fifo" | "tlm_fifo" => Ty::Mailbox(Box::new(first_type_arg(q, env, consts)?)),
        other => return Err(format!("unsupported type '{}'", other)),
    })
}

/// Whether a signal or port type drives a resolved net (§6.13–§6.18): its
/// writers are drivers whose values resolve bit by bit. An input port of
/// one only reads it.
pub fn drives_resolved(q: &sc::QualifiedName) -> bool {
    matches!(
        q.last_name(),
        "sc_signal_resolved"
            | "sc_signal_rv"
            | "sc_out_resolved"
            | "sc_inout_resolved"
            | "sc_out_rv"
            | "sc_inout_rv"
    )
}

/// The basename SystemC generates for a library object constructed without
/// a name (`sc_gen_unique_name`, §5.17): `signal_0`, `port_1`, ….
pub fn default_basename(q: &sc::QualifiedName) -> Option<&'static str> {
    Some(match q.last_name() {
        "sc_signal" => "signal",
        "sc_buffer" => "buffer",
        "sc_signal_resolved" => "signal_resolved",
        "sc_signal_rv" => "signal_rv",
        "sc_in" | "sc_out" | "sc_inout" | "sc_in_clk" | "sc_out_clk" | "sc_inout_clk"
        | "sc_in_rv" | "sc_out_rv" | "sc_inout_rv" | "sc_in_resolved" | "sc_out_resolved"
        | "sc_inout_resolved" | "sc_fifo_in" | "sc_fifo_out" | "sc_port" => "port",
        "sc_export" => "export",
        "sc_clock" => "clock",
        "sc_fifo" => "fifo",
        "sc_mutex" => "mutex",
        "sc_semaphore" => "semaphore",
        "sc_event_queue" => "event_queue",
        "sc_vector" => "vector",
        _ => return None,
    })
}

/// A port, channel or library object type's data type: `sc_in<T>` → `T`.
pub fn payload_ty(
    q: &sc::QualifiedName,
    env: &TyEnv,
    consts: &dyn Fn(&sc::Expr) -> Option<i64>,
) -> Result<Ty, String> {
    match q.last_name() {
        "sc_in_clk" | "sc_out_clk" | "sc_inout_clk" | "sc_clock" => Ok(Ty::Bool),
        // §6.13–§6.15: resolved signals carry an sc_logic.
        "sc_in_resolved" | "sc_out_resolved" | "sc_inout_resolved" | "sc_signal_resolved" => {
            Ok(Ty::Vec4 {
                w: Width::known(1),
            })
        }
        "sc_in_rv" | "sc_out_rv" | "sc_inout_rv" | "sc_signal_rv" => Ok(Ty::Vec4 {
            w: width_arg(q.last_args(), env, consts)?,
        }),
        _ => first_type_arg(q, env, consts),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sv_parser::systemc;

    fn ty(src: &str) -> Ty {
        let r = systemc::parse(&format!("{} x;", src));
        let sc::Item::Var(v) = &r.unit.items[0] else {
            panic!("declaration")
        };
        let lit = |e: &sc::Expr| match &e.kind {
            sc::ExprKind::IntLit { value, .. } => value.map(|v| v as i64),
            _ => None,
        };
        ty_of(&v.ty, &TyEnv::default(), &lit).expect("maps")
    }

    #[test]
    fn systemc_types_map_to_sv() {
        assert!(matches!(ty("bool"), Ty::Bool));
        assert!(matches!(
            ty("sc_uint<12>"),
            Ty::Vec2 {
                w: Width { n: Some(12), .. },
                signed: false,
                bv: false
            }
        ));
        assert!(matches!(ty("sc_int<5>"), Ty::Vec2 { signed: true, .. }));
        assert!(matches!(ty("sc_bv<8>"), Ty::Vec2 { bv: true, .. }));
        assert!(matches!(ty("sc_lv<4>"), Ty::Vec4 { .. }));
        assert!(matches!(
            ty("unsigned long long"),
            Ty::Int {
                bits: 64,
                signed: false,
                ..
            }
        ));
        assert!(matches!(
            ty("unsigned char"),
            Ty::Int {
                bits: 8,
                ch: true,
                ..
            }
        ));
        assert!(matches!(ty("sc_core::sc_time"), Ty::Time));
        assert!(matches!(ty("tlm::tlm_generic_payload"), Ty::Class(c) if c == "scrt_tlm_gp"));
        assert!(matches!(ty("std::vector<int>"), Ty::Queue(_)));
    }
}

/// The runtime's library objects: SystemC kernel channels and helpers that
/// a module or a function constructs and calls (`lib_channel_call`).
pub fn is_lib_class(c: &str) -> bool {
    matches!(
        c,
        "scrt_mutex" | "scrt_semaphore" | "scrt_event_queue" | "scrt_spawn_opts"
    )
}
