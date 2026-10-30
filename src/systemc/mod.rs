//! SystemC simulation: SystemC sources lowered to SystemVerilog.
//!
//! The SystemC files given to the simulator are parsed with
//! [`sv_parser::systemc`] and lowered to SystemVerilog AST descriptions
//! (built in code, never printed and re-parsed), which join the design's
//! own descriptions before elaboration — the same hook as UPF (`upf.rs`).
//! What follows runs unchanged: elaboration, bytecode, simulation.
//!
//! Scheduling (IEEE 1666-2023 §4.2) is mapped onto the SV event regions:
//!
//! - Processes start at the first `sc_start` (`scrt_started`), or at time
//!   0 when the design has no `sc_main` (a SystemVerilog top instantiates
//!   the SystemC modules); a method
//!   runs once at initialization unless `dont_initialize()`; a clocked
//!   thread first runs at its first clock edge.
//! - Signal writes from processes are nonblocking assignments (SystemC's
//!   update phase). Writes made by `sc_main` while the simulation is paused
//!   are held and applied when the next `sc_start` resumes, and clocks
//!   toggle after a `#0`, so those writes are visible to the processes the
//!   clock edge at the same instant wakes — as in SystemC.
//! - `sc_start(t)` advances to 1 ps before the end time and resumes from
//!   there, so the events AT the end time run in the next `sc_start`, as in
//!   SystemC (which stops before evaluating them).
//! - Time is in picoseconds (`timeunit 1ps`), SystemC's default resolution.
//!
//! The fixed SystemVerilog support code — time formatting, the C-pointer
//! memory model behind TLM data pointers, the generic payload and sockets —
//! is the `sc_rt` package in `runtime.sv`.

mod build;
mod lower;
mod module;
mod program;
mod types;

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::ast::Description;
use crate::sv_parser::systemc::{self as scfront, ScParseResult};

#[derive(Default, Clone)]
struct Config {
    files: Vec<String>,
    include_dirs: Vec<String>,
    defines: Vec<(String, String)>,
}

static CONFIG: Mutex<Option<Config>> = Mutex::new(None);

/// The SystemC sources of the design, with the C++ preprocessor's include
/// directories and definitions. Call before elaboration.
pub fn configure(
    files: Vec<String>,
    include_dirs: Vec<String>,
    defines: Vec<(String, Option<String>)>,
) {
    let defines = defines
        .into_iter()
        .map(|(k, v)| (k, v.unwrap_or_else(|| "1".to_string())))
        .collect();
    *CONFIG.lock().unwrap_or_else(|e| e.into_inner()) = if files.is_empty() {
        None
    } else {
        Some(Config {
            files,
            include_dirs,
            defines,
        })
    };
}

/// Whether the design has SystemC sources.
pub fn configured() -> bool {
    CONFIG.lock().unwrap_or_else(|e| e.into_inner()).is_some()
}

/// The runtime package source.
const RUNTIME: &str = include_str!("runtime.sv");

fn parse_all(cfg: &Config) -> Result<Vec<ScParseResult>, String> {
    let inc: Vec<&str> = cfg.include_dirs.iter().map(|s| s.as_str()).collect();
    let defs: Vec<(&str, &str)> = cfg
        .defines
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    let mut results = Vec::new();
    let mut errors = Vec::new();
    for f in &cfg.files {
        let r = scfront::parse_file(f, &inc, &defs)?;
        for d in &r.errors {
            errors.push(r.render(d));
        }
        results.push(r);
    }
    if !errors.is_empty() {
        return Err(format!(
            "{}\nSystemC: {} error(s) while parsing",
            errors.join("\n"),
            errors.len()
        ));
    }
    Ok(results)
}

/// A digest of every C++ text the SystemC sources read (headers included),
/// for the design cache key.
pub fn cache_digest() -> Option<u64> {
    let cfg = CONFIG.lock().unwrap_or_else(|e| e.into_inner()).clone()?;
    let inc: Vec<&str> = cfg.include_dirs.iter().map(|s| s.as_str()).collect();
    let defs: Vec<(&str, &str)> = cfg
        .defines
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    use std::hash::{BuildHasher, Hash, Hasher};
    let mut h = crate::hasher::DeterministicState::default().build_hasher();
    RUNTIME.hash(&mut h);
    for f in &cfg.files {
        f.hash(&mut h);
        let mut pp = scfront::preprocess::Preprocessor::new(&inc, &defs);
        let text = std::fs::read_to_string(f).unwrap_or_default();
        let _ = pp.run(f, text);
        for file in &pp.files {
            file.path.hash(&mut h);
            file.text.hash(&mut h);
        }
    }
    Some(h.finish())
}

/// The runtime package text, with a nettype per resolved-net width the
/// design uses (`scrt_rv<W>_t`, §6.13.4): a driver is {written, value}, and
/// only written drivers take part — a resolved signal reads X until one is.
/// Bits resolve as sc_logic does: Z yields, differing values give X.
fn runtime_text(rv_widths: &std::collections::BTreeSet<u32>) -> String {
    let mut extra = String::new();
    for w in rv_widths {
        extra.push_str(&format!(
            "  function automatic logic [{w}:0] scrt_rv{w}_res(input logic [{w}:0] d[]);
    logic [{hi}:0] r = 'z;
    bit any = 0;
    foreach (d[k]) if (d[k][{w}] === 1'b1) begin
      any = 1;
      for (int i = 0; i < {w}; i++)
        if (r[i] === 1'bz) r[i] = d[k][i];
        else if (d[k][i] !== 1'bz && d[k][i] !== r[i]) r[i] = 1'bx;
    end
    return any ? {{1'b1, r}} : {{1'b0, {{{w}{{1'bx}}}}}};
  endfunction
  nettype logic [{w}:0] scrt_rv{w}_t with scrt_rv{w}_res;
",
            w = w,
            hi = w - 1
        ));
    }
    RUNTIME.replacen("endpackage", &format!("{}endpackage", extra), 1)
}

/// Parse the runtime package, its spans moved into the synthetic range.
fn runtime_package(text: &str) -> Result<Description, String> {
    let mut tokens = crate::lexer::Lexer::new(text).tokenize();
    let base = build::reserve(text.len());
    for t in &mut tokens {
        t.span.start += base;
        t.span.end += base;
    }
    let mut parser = crate::sv_parser::parse::Parser::new(tokens);
    let mut st = parser.parse_source_text();
    if let Some(d) = parser
        .diagnostics()
        .iter()
        .find(|d| d.severity == crate::diagnostics::Severity::Error)
    {
        return Err(format!("SystemC runtime failed to parse: {}", d.message));
    }
    st.descriptions
        .pop()
        .ok_or_else(|| "SystemC runtime is empty".to_string())
}

/// Lower the configured SystemC sources and append them to `descriptions`.
/// Returns the top module to use when none was named (`sc_main`).
pub fn inject(descriptions: &mut Vec<Description>) -> Result<Option<String>, String> {
    let Some(cfg) = CONFIG.lock().unwrap_or_else(|e| e.into_inner()).clone() else {
        return Ok(None);
    };
    let results = parse_all(&cfg)?;
    let prog = program::Program::new(&results);
    let (env, enum_consts) = global_env(&prog);
    let mut lw = lower::Lw::new(&prog, env, enum_consts);
    let mut out = Vec::new();

    // Module interfaces first (instantiation needs every child's ports).
    let modules: Vec<(
        String,
        usize,
        &scfront::ast::ClassDecl,
        Vec<scfront::ast::TemplateParam>,
    )> = prog
        .classes
        .iter()
        .filter(|(n, (_, c, _))| c.sc_module || prog.foreign.contains_key(*n))
        .map(|(n, (tu, c, tp))| (n.clone(), *tu, *c, tp.clone()))
        .collect();
    let mut ifaces = BTreeMap::new();
    let no_ifaces = BTreeMap::new();
    for (name, tu, class, tps) in &modules {
        lw.tu = *tu;
        lw.env.tparams.clear();
        let mut ml = module::ModuleLowering::new(&mut lw, &no_ifaces);
        match ml.iface(class, tps) {
            Ok(i) => {
                let members = i
                    .members
                    .iter()
                    .map(|(k, v)| (k.clone(), v.ty.clone()))
                    .collect();
                prog.module_members
                    .borrow_mut()
                    .insert(name.clone(), members);
                prog.module_names
                    .borrow_mut()
                    .insert(name.clone(), i.sc_names.clone());
                prog.module_resolved
                    .borrow_mut()
                    .insert(name.clone(), i.resolved.clone());
                ifaces.insert(name.clone(), i);
            }
            Err(e) => lw.record(e),
        }
    }
    for (name, tu, class, tps) in &modules {
        let Some(iface) = ifaces.get(name) else {
            continue;
        };
        // A foreign module's body is the SystemVerilog module it names.
        if prog.foreign.contains_key(name) {
            continue;
        }
        lw.tu = *tu;
        lw.env.tparams.clear();
        for tp in tps {
            if let scfront::ast::TemplateParam::Value { name: Some(n), .. } = tp {
                lw.env
                    .tparams
                    .insert(n.name.clone(), types::TParam::Value(n.name.clone()));
            }
        }
        let mut ml = module::ModuleLowering::new(&mut lw, &ifaces);
        match ml.lower_module(name, class, iface) {
            Ok(m) => out.push(Description::Module(m)),
            Err(e) => lw.record(e),
        }
    }
    let mut top = None;
    if let Some((tu, f)) = prog.sc_main {
        lw.tu = tu;
        lw.env.tparams.clear();
        let mut ml = module::ModuleLowering::new(&mut lw, &ifaces);
        match ml.lower_main(f) {
            Ok(m) => {
                out.push(Description::Module(m));
                top = Some("sc_main".to_string());
            }
            Err(e) => lw.record(e),
        }
    }
    if !lw.errors.is_empty() {
        let mut msgs: Vec<String> = lw
            .errors
            .iter()
            .map(|e| {
                let r = &results[e.tu];
                r.render(&scfront::ScDiagnostic::error(
                    format!("SystemC: {}", e.msg),
                    e.span,
                ))
            })
            .collect();
        msgs.dedup();
        return Err(format!(
            "{}\nSystemC: {} construct(s) cannot be simulated",
            msgs.join("\n"),
            msgs.len()
        ));
    }
    if std::env::var_os("XEZIM_SYSTEMC_DUMP").is_some() {
        for d in &out {
            eprintln!("{:#?}", d);
        }
    }
    out.insert(0, runtime_package(&runtime_text(&lw.rv_widths))?);
    descriptions.extend(out);
    Ok(top)
}

/// Typedefs and enums of the whole program.
fn global_env(prog: &program::Program) -> (types::TyEnv, BTreeMap<String, i64>) {
    let mut env = types::TyEnv::default();
    let mut consts = BTreeMap::new();
    for (_, t) in &prog.typedefs {
        for d in &t.declarators {
            env.typedefs.insert(d.name.name.clone(), t.ty.clone());
        }
    }
    for (_, e) in &prog.enums {
        let mut next = 0i64;
        let ename = e.name.as_ref().map(|n| n.name.clone());
        if let Some(n) = &ename {
            env.enums.insert(n.clone());
        }
        for en in &e.enumerators {
            if let Some(v) = &en.value
                && let Some(x) = const_int(v, &consts)
            {
                next = x;
            }
            if let Some(n) = &ename {
                consts.insert(format!("{}::{}", n, en.name.name), next);
            }
            if !e.scoped {
                consts.insert(en.name.name.clone(), next);
            }
            next += 1;
        }
    }
    // Class-scope enums (`enum { SIZE = 256 };` inside a module).
    for (_, c, _) in prog.classes.values() {
        for m in &c.members {
            if let scfront::ast::Member::Enum(e) = m {
                let mut next = 0i64;
                for en in &e.enumerators {
                    if let Some(v) = &en.value
                        && let Some(x) = const_int(v, &consts)
                    {
                        next = x;
                    }
                    consts.insert(en.name.name.clone(), next);
                    next += 1;
                }
                if let Some(n) = &e.name {
                    env.enums.insert(n.name.clone());
                }
            }
        }
    }
    (env, consts)
}

fn const_int(e: &scfront::ast::Expr, consts: &BTreeMap<String, i64>) -> Option<i64> {
    use scfront::ast::ExprKind as K;
    match &e.kind {
        K::IntLit { value, .. } => value.map(|v| v as i64),
        K::Unary {
            op: scfront::ast::UnaryOp::Neg,
            operand,
        } => const_int(operand, consts).map(|v| -v),
        K::Name(q) => consts.get(q.last_name()).copied(),
        K::Binary { op, lhs, rhs } => {
            let (a, b) = (const_int(lhs, consts)?, const_int(rhs, consts)?);
            use scfront::ast::BinaryOp as B;
            Some(match op {
                B::Add => a + b,
                B::Sub => a - b,
                B::Mul => a * b,
                B::Shl => a << b,
                B::BitOr => a | b,
                _ => return None,
            })
        }
        K::Paren(x) => const_int(x, consts),
        _ => None,
    }
}
