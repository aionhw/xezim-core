//! Integration tests for the SystemC front end (`sv_parser::systemc`):
//! RTL modules (IEEE 1666-2023 §5.2, §6), TLM-2.0 sockets and transport
//! interfaces (§10–§16), the C++ preprocessor (ISO/IEC 14882:2017 §19)
//! and diagnostics. Fixtures live in `tests/fixtures/systemc/`.

use sv_parser::systemc::ast::*;
use sv_parser::systemc::classify::ScObjectKind;
use sv_parser::systemc::{self, ScParseResult};

fn fixture(name: &str) -> String {
    format!(
        "{}/tests/fixtures/systemc/{}",
        env!("CARGO_MANIFEST_DIR"),
        name
    )
}

fn parse_fixture(name: &str) -> ScParseResult {
    let r = systemc::parse_file(&fixture(name), &[], &[]).expect("fixture readable");
    assert_clean(&r);
    r
}

fn assert_clean(r: &ScParseResult) {
    let msgs: Vec<String> = r.errors.iter().map(|d| r.render(d)).collect();
    assert!(msgs.is_empty(), "unexpected errors:\n{}", msgs.join("\n"));
}

fn parse_clean(src: &str) -> ScParseResult {
    let r = systemc::parse(src);
    assert_clean(&r);
    r
}

fn names(members: &[sv_parser::systemc::classify::ScMember<'_>]) -> Vec<String> {
    members.iter().map(|m| m.name.name.clone()).collect()
}

/// §5.2.5 SC_MODULE, §5.2.7 SC_CTOR, §5.2.9 SC_METHOD, §5.2.14 static
/// sensitivity, §5.2.16 dont_initialize; include guards (§19.1).
#[test]
fn rtl_counter_module() {
    let r = parse_fixture("counter.cpp");
    let modules = r.unit.modules();
    assert_eq!(modules.len(), 1, "the guarded header is parsed once");
    let counter = modules[0];
    assert!(counter.sc_module_macro);
    assert_eq!(counter.name_str(), Some("counter"));

    let ports = counter.ports();
    assert_eq!(names(&ports), ["clk", "rst_n", "en", "count"]);
    assert_eq!(ports[0].kind, ScObjectKind::InPort);
    assert_eq!(ports[3].kind, ScObjectKind::OutPort);
    // `sc_out<sc_uint<WIDTH> >`: the macro expanded inside the argument.
    let inner = ports[3].ty.name().unwrap().last_args().unwrap();
    let TemplateArg::Type(t) = &inner[0] else {
        panic!("sc_uint<8> is a type")
    };
    let args = t.name().unwrap().last_args().unwrap();
    assert!(matches!(
        &args[0],
        TemplateArg::Expr(Expr {
            kind: ExprKind::IntLit { value: Some(8), .. },
            ..
        })
    ));

    let ctor = counter.constructors().next().unwrap();
    assert!(ctor.sc_ctor);
    assert_eq!(ctor.initializers.len(), 5);

    let procs = counter.processes();
    assert_eq!(procs.len(), 2);
    assert_eq!(procs[0].kind, ProcessKind::Method);
    assert_eq!(procs[0].func.name, "tick");
    assert_eq!(procs[0].sensitivity.len(), 2);
    assert!(procs[0].dont_initialize);
    assert_eq!(procs[1].func.name, "comb");
    assert_eq!(procs[1].sensitivity.len(), 1);
    assert!(!procs[1].dont_initialize);

    // `void counter::tick() {…}` is defined out of class.
    let defs = r.unit.out_of_class_members("counter");
    assert_eq!(defs.len(), 1);
    assert_eq!(defs[0].base_name(), "tick");
    assert!(defs[0].body.is_some());
}

/// §5.2.8 SC_HAS_PROCESS with a plain constructor defined out of class,
/// §5.2.9 SC_CTHREAD, §5.2.13 reset_signal_is, §8.5 sc_vector, a class
/// template module, and §4.3 sc_main.
#[test]
fn hierarchy_templates_and_sc_main() {
    let r = parse_fixture("top_main.cpp");
    let mut module_names: Vec<_> = r
        .unit
        .modules()
        .iter()
        .filter_map(|m| m.name_str())
        .collect();
    module_names.sort();
    assert_eq!(module_names, ["counter", "fsm", "shifter", "top"]);

    // Template module: the CTHREAD's clock and its reset.
    let shifter = r.unit.find_class("shifter").unwrap();
    let p = &shifter.processes()[0];
    assert_eq!(p.kind, ProcessKind::CThread);
    assert!(p.clock.is_some());
    assert_eq!(p.resets.len(), 1);
    assert!(!p.resets[0].is_async);
    let item = r
        .unit
        .items
        .iter()
        .find(|i| matches!(i, Item::Template { .. }))
        .expect("template item");
    let Item::Template { params, .. } = item else {
        unreachable!()
    };
    assert!(
        matches!(&params[0], TemplateParam::Value { name: Some(n), default: Some(_), .. } if n.name == "W")
    );

    // Class-style module: `class fsm : public sc_core::sc_module`.
    let fsm = r.unit.find_class("fsm").unwrap();
    assert!(fsm.sc_module && !fsm.sc_module_macro);
    assert!(
        fsm.members
            .iter()
            .any(|m| matches!(m, Member::ScHasProcess(n) if n.name == "fsm"))
    );
    assert!(fsm.members.iter().any(|m| matches!(m, Member::Destructor(f) if f.special_body == Some(FunctionBodyKind::Defaulted) && f.is_override)));
    let ports = fsm.ports();
    assert_eq!(names(&ports), ["clk", "req", "grant"]);
    assert_eq!(
        ports[1].kind,
        ScObjectKind::Vector(Box::new(ScObjectKind::InPort))
    );
    // Its process is registered in the out-of-class constructor, with a
    // sensitivity added inside a for loop.
    assert!(fsm.processes().is_empty());
    let procs = r.unit.processes(fsm);
    assert_eq!(procs.len(), 1);
    assert_eq!(procs[0].func.name, "step");
    assert_eq!(procs[0].sensitivity.len(), 2);
    let ctor = r
        .unit
        .out_of_class_members("fsm")
        .into_iter()
        .find(|f| f.base_name() == "fsm")
        .unwrap();
    assert_eq!(ctor.params.len(), 2);
    assert_eq!(ctor.initializers[0].name.path(), "sc_module");

    // `top` instantiates a template module with an expression argument.
    let top = r.unit.find_class("top").unwrap();
    let objs = top.objects();
    let sh = objs.iter().find(|o| o.name.name == "sh").unwrap();
    let args = sh.ty.name().unwrap().last_args().unwrap();
    assert!(matches!(&args[0], TemplateArg::Expr(_)));
    let cnt = objs.iter().find(|o| o.name.name == "cnt").unwrap();
    assert!(cnt.is_pointer());
    assert_eq!(names(&top.signals()), ["clk", "rst_n", "en", "count"]);
    assert_eq!(top.processes()[0].kind, ProcessKind::Thread);

    let main = r.unit.sc_main().expect("sc_main");
    assert_eq!(main.params.len(), 2);
    // `top t("t");` is an object, not a function declaration.
    let Stmt::Decl(first) = &main.body.as_ref().unwrap().stmts[0] else {
        panic!("declaration")
    };
    assert!(matches!(
        first.declarators[0].init,
        Some(Initializer::Paren(_))
    ));
}

/// §11 TLM-2.0 base protocol, loosely timed: simple sockets (§16.1),
/// b_transport registration and the generic payload API (§14).
#[test]
fn tlm_loosely_timed() {
    let r = parse_fixture("tlm_lt.cpp");
    let init = r.unit.find_class("Initiator").unwrap();
    assert!(init.sc_module);
    let socks = init.sockets();
    assert_eq!(socks.len(), 1);
    assert_eq!(socks[0].kind, ScObjectKind::InitiatorSocket);

    let mem = r.unit.find_class("Memory").unwrap();
    assert_eq!(mem.sockets()[0].kind, ScObjectKind::TargetSocket);
    let bt = mem.find_method("b_transport").unwrap();
    assert!(bt.specifiers.is_virtual);
    assert_eq!(bt.params.len(), 2);
    assert_eq!(
        bt.params[0].ty.name().unwrap().path(),
        "tlm::tlm_generic_payload"
    );
    assert_eq!(bt.params[0].ty.ptr_ops, [PtrOp::LRef]);

    // socket.register_b_transport(this, &Memory::b_transport);
    let ctor = mem.constructors().next().unwrap();
    let Stmt::Expr(call) = &ctor.body.as_ref().unwrap().stmts[0] else {
        panic!("call statement")
    };
    let ExprKind::Call { callee, args } = &call.kind else {
        panic!("call")
    };
    assert!(
        matches!(&callee.kind, ExprKind::Member { name, .. } if name.ident.name == "register_b_transport")
    );
    assert!(matches!(args[0].kind, ExprKind::This));
    let ExprKind::Unary {
        op: UnaryOp::AddrOf,
        operand,
    } = &args[1].kind
    else {
        panic!("&Memory::b_transport")
    };
    assert_eq!(operand.as_name().unwrap().path(), "Memory::b_transport");

    let top = r.unit.find_class("Top").unwrap();
    assert!(top.ports().is_empty());
    assert!(r.unit.sc_main().is_some());
}

/// Approximately timed (§11.1.2): nb_transport_fw/bw, tlm_phase, a
/// payload event queue, a tagged-socket router template and a process
/// spawned from a lambda (§5.5).
#[test]
fn tlm_approximately_timed() {
    let r = parse_fixture("tlm_at.cpp");
    let target = r.unit.find_class("AtTarget").unwrap();
    assert!(target.sc_module);
    assert_eq!(target.bases.len(), 2);
    assert_eq!(target.bases[1].name.last_name(), "tlm_fw_transport_if");
    assert_eq!(target.bases[1].name.last_args().map(|a| a.len()), Some(0));
    assert_eq!(target.sockets()[0].kind, ScObjectKind::TargetSocket);
    let objs = target.objects();
    let ev = objs
        .iter()
        .find(|o| o.name.name == "target_done_event")
        .unwrap();
    assert_eq!(ev.kind, ScObjectKind::Event);

    let fw = target.find_method("nb_transport_fw").unwrap();
    assert!(fw.is_override);
    assert_eq!(
        fw.return_type.as_ref().unwrap().name().unwrap().path(),
        "tlm_sync_enum"
    );
    let ctor = target.constructors().next().unwrap();
    assert!(ctor.specifiers.is_explicit);
    assert_eq!(ctor.initializers.len(), 3);
    let procs = target.processes();
    assert_eq!(procs.len(), 1);
    assert!(procs[0].dont_initialize);
    let has_lambda = ctor.body.as_ref().unwrap().stmts.iter().any(|s| {
        matches!(s, Stmt::Expr(Expr { kind: ExprKind::Call { args, .. }, .. })
            if matches!(args.first().map(|a| &a.kind), Some(ExprKind::Lambda(l)) if l.captures == [Capture::This]))
    });
    assert!(has_lambda, "sc_spawn([this]() {{…}})");

    let router = r.unit.find_class("Router").unwrap();
    assert!(router.sc_module);
    let socks = router.sockets();
    assert_eq!(names(&socks), ["target_socket", "initiator_socket"]);
    assert_eq!(socks[1].kind, ScObjectKind::InitiatorSocket);
    assert!(socks[1].is_pointer());
    assert_eq!(socks[1].declarator.array_dims.len(), 1);
}

/// `>>` closing two template argument lists (C++11 §14.2/3), a
/// parenthesized `>` inside an argument, and `<`/`>` as comparisons.
#[test]
fn angle_brackets() {
    let r = parse_clean(
        "SC_MODULE(m) {
            sc_signal<sc_uint<8>> s;
            std::map<int, std::vector<sc_bv<4>>> table;
            sc_uint<(4 > 2) ? 8 : 4> w;
            void f() {
                int a = 1, b = 2, c = 3, d = 4;
                bool x = a < b && c > d;
                int y = a >> 2;
                for (int i = 0; i < b; ++i) y = y << 1;
                auto p = std::make_unique<sc_signal<bool>>(\"p\");
            }
            SC_CTOR(m) {}
        };",
    );
    let m = r.unit.find_class("m").unwrap();
    let objs = m.objects();
    assert_eq!(objs.len(), 3);
    assert_eq!(objs[0].kind, ScObjectKind::Signal);
    let table_args = objs[1].ty.name().unwrap().last_args().unwrap();
    assert_eq!(table_args.len(), 2);
    let w_args = objs[2].ty.name().unwrap().last_args().unwrap();
    assert!(matches!(
        &w_args[0],
        TemplateArg::Expr(Expr {
            kind: ExprKind::Conditional { .. },
            ..
        })
    ));

    let f = m.find_method("f").unwrap();
    let stmts = &f.body.as_ref().unwrap().stmts;
    let Stmt::Decl(x) = &stmts[1] else {
        panic!("bool x")
    };
    let Some(Initializer::Assign(e)) = &x.declarators[0].init else {
        panic!("init")
    };
    assert!(matches!(
        &e.kind,
        ExprKind::Binary {
            op: BinaryOp::LogAnd,
            ..
        }
    ));
    let Stmt::Decl(y) = &stmts[2] else {
        panic!("int y")
    };
    let Some(Initializer::Assign(e)) = &y.declarators[0].init else {
        panic!("init")
    };
    assert!(matches!(
        &e.kind,
        ExprKind::Binary {
            op: BinaryOp::Shr,
            ..
        }
    ));
}

/// SystemC-specific expression forms: `(a, b)` concatenation (§7.2.7),
/// part selects, `sensitive(a, b)` and the deprecated `sensitive_pos`,
/// async resets and SC_NAMED (§5.17).
#[test]
fn systemc_statement_forms() {
    let r = parse_clean(
        "SC_MODULE(m) {
            sc_in<bool> clk, rst, a, b;
            sc_out<sc_uint<4>> o;
            sc_signal<int> SC_NAMED(sig);
            sc_signal<int> SC_NAMED(sig2, 7);
            void run() { o.write((a.read(), b.read(), o.read().range(1, 0))); }
            void th() { while (true) { wait(); } }
            SC_CTOR(m) {
                SC_METHOD(run);
                sensitive(a, b);
                sensitive_pos << clk;
                SC_THREAD(th);
                async_reset_signal_is(rst, false);
                sensitive << clk.neg();
            }
        };",
    );
    let m = r.unit.find_class("m").unwrap();
    let procs = m.processes();
    assert_eq!(procs.len(), 2);
    use SensitivityEdge::*;
    let edges: Vec<_> = procs[0].sensitivity.iter().map(|s| s.edge).collect();
    assert_eq!(edges, [Any, Any, Pos]);
    assert!(procs[1].resets[0].is_async);
    assert_eq!(procs[1].sensitivity.len(), 1);

    let sig = m
        .objects()
        .into_iter()
        .find(|o| o.name.name == "sig2")
        .unwrap();
    let Some(Initializer::Brace(args)) = &sig.declarator.init else {
        panic!("SC_NAMED init")
    };
    assert!(matches!(&args[0].kind, ExprKind::StringLit { value, .. } if value == "sig2"));
    assert_eq!(args.len(), 2);

    let run = m.find_method("run").unwrap();
    let Stmt::Expr(call) = &run.body.as_ref().unwrap().stmts[0] else {
        panic!()
    };
    let ExprKind::Call { args, .. } = &call.kind else {
        panic!()
    };
    let ExprKind::Paren(inner) = &args[0].kind else {
        panic!("concat is parenthesized")
    };
    assert!(matches!(
        inner.kind,
        ExprKind::Binary {
            op: BinaryOp::Comma,
            ..
        }
    ));
}

/// Classes deriving from a user module are modules (§5.2.1), through
/// namespaces; nested namespaces and aliases parse.
#[test]
fn derived_modules_and_namespaces() {
    let r = parse_clean(
        "namespace soc::periph {
            namespace tu = tlm_utils;
            struct base_ip : public ::sc_core::sc_module {
                base_ip(sc_core::sc_module_name n) : sc_module(n) {}
            };
            class uart final : public base_ip {
                using base_ip::base_ip;
            };
            struct payload { int addr; unsigned char data[4]; };
        }",
    );
    let mut mods: Vec<_> = r
        .unit
        .modules()
        .iter()
        .filter_map(|m| m.name_str())
        .collect();
    mods.sort();
    assert_eq!(mods, ["base_ip", "uart"]);
    assert!(!r.unit.find_class("payload").unwrap().sc_module);
    assert!(r.unit.find_class("uart").unwrap().is_final);
    let Item::Namespace {
        name: Some(outer),
        items,
        ..
    } = &r.unit.items[0]
    else {
        panic!()
    };
    assert_eq!(outer.name, "soc");
    assert!(matches!(&items[0], Item::Namespace { name: Some(n), .. } if n.name == "periph"));
}

/// `SC_MODULE(name)` expands to the class head `struct name : sc_module`
/// (§5.2.5), so further bases may follow the macro: a module implementing
/// a TLM interface itself.
#[test]
fn sc_module_with_further_bases() {
    let r = parse_clean(
        "SC_MODULE(mem), public tlm::tlm_fw_transport_if<>, private helper {
            SC_CTOR(mem) {}
        };",
    );
    let c = r.unit.find_class("mem").unwrap();
    assert!(c.sc_module);
    let bases: Vec<_> = c.bases.iter().map(|b| b.name.last_name().to_string()).collect();
    assert_eq!(bases, ["sc_module", "tlm_fw_transport_if", "helper"]);
    assert_eq!(c.bases[2].access, Some(Access::Private));
}

/// Quoted includes resolve through `-I`, `#pragma once`, function-like
/// macros with `##`, and `#if` with `defined` (C++17 §19.1–§19.3).
#[test]
fn preprocessor_include_dirs_and_macros() {
    let inc = fixture("include");
    let r = systemc::parse_file(
        &fixture("uses_include_dir.cpp"),
        &[&inc],
        &[("USE_REGS", "1")],
    )
    .unwrap();
    assert_clean(&r);
    let consts: Vec<_> = r
        .unit
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Var(v) if v.specifiers.is_static => Some(v.declarators[0].name.name.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(consts, ["CTRL_OFFSET", "STATUS_OFFSET"]);
    let regs = r.unit.find_class("regs").unwrap();
    let wdata = regs.ports();
    let arg = &wdata[0].ty.name().unwrap().last_args().unwrap()[0];
    // `word_t` is the header's typedef, so the argument is a type.
    assert!(matches!(arg, TemplateArg::Type(_)));
    assert_eq!(
        r.files
            .iter()
            .filter(|f| f.path.ends_with("bus_defs.h"))
            .count(),
        1
    );

    // Without the define, the `#error` branch is taken.
    let r = systemc::parse_file(&fixture("uses_include_dir.cpp"), &[&inc], &[]).unwrap();
    assert_eq!(r.errors.len(), 1);
    assert!(r.errors[0].message.contains("regs need a wide bus"));
    let rendered = r.render(&r.errors[0]);
    assert!(
        rendered.contains("uses_include_dir.cpp:7:1: error"),
        "{}",
        rendered
    );
}

/// A bad member is reported with its location and skipped; the members
/// around it survive.
#[test]
fn error_recovery_and_rendering() {
    let r = systemc::parse(
        "SC_MODULE(m) {\n    sc_in<bool> a;\n    int x = ;\n    sc_out<bool> b;\n    SC_CTOR(m) { SC_METHOD(f); }\n    void f() { b = a; }\n};\n",
    );
    assert_eq!(r.errors.len(), 1, "{:?}", r.errors);
    let rendered = r.render(&r.errors[0]);
    assert!(
        rendered.starts_with("<input>:3:13: error: expected expression, found ';'"),
        "{}",
        rendered
    );
    assert!(rendered.contains("int x = ;"));
    let m = r.unit.find_class("m").unwrap();
    assert_eq!(names(&m.ports()), ["a", "b"]);
    assert_eq!(m.processes().len(), 1);
}

/// Unsupported C++ is rejected with a precise message, never accepted.
#[test]
fn unsupported_constructs_are_diagnosed() {
    for (src, msg) in [
        ("void f() { goto end; end: ; }", "'goto' is not supported"),
        (
            "typedef void (*cb_t)(int);",
            "function pointer typedefs are not supported",
        ),
        (
            "template <template <class> class C> struct s {};",
            "template template parameters are not supported",
        ),
    ] {
        let r = systemc::parse(src);
        assert!(
            r.errors.iter().any(|d| d.message == msg),
            "{}: expected '{}', got {:?}",
            src,
            msg,
            r.errors
        );
    }
}

/// SystemC 3.0 in-class initialization (`sc_initializer_function.h`):
/// `SC_METHOD_IMP`/`SC_CTHREAD_IMP` with init code, `SC_INIT`, and
/// `SC_NAMED_WITH_INIT`; in-class processes come before the constructor's.
#[test]
fn in_class_process_initialization() {
    let r = parse_clean(
        "SC_MODULE(adder) {
            sc_in_clk clock;
            sc_in<bool> reset;
            sc_vector<sc_in<int>> SC_NAMED(din, 4);
            sc_out<int> SC_NAMED(res);
            sc_signal<int> SC_NAMED_WITH_INIT(acc, 0) { acc.write(0); }
            SC_CTOR(adder) { SC_THREAD(late); }
            void late() {}
        private:
            SC_METHOD_IMP(add_method, { for (auto &d : din) sensitive << d; } );
            SC_CTHREAD_IMP(run, clock.pos(), { async_reset_signal_is(reset, true); }) {
                while (true) wait();
            }
            SC_INIT(extra) { SC_METHOD(late); dont_initialize(); }
        };
        void adder::add_method() { int r = 0; for (auto &d : din) r += d.read(); res = r; }",
    );
    let m = r.unit.find_class("adder").unwrap();
    let procs = m.processes();
    let summary: Vec<_> = procs
        .iter()
        .map(|p| (p.func.name.as_str(), p.kind))
        .collect();
    use ProcessKind::*;
    assert_eq!(
        summary,
        [
            ("add_method", Method),
            ("run", CThread),
            ("late", Method),
            ("late", Thread)
        ]
    );
    assert_eq!(
        procs[0].sensitivity.len(),
        1,
        "sensitive << d inside the init block"
    );
    assert!(procs[1].clock.is_some() && procs[1].resets[0].is_async);
    assert!(procs[2].dont_initialize);
    let imp_bodies: Vec<_> = m
        .members
        .iter()
        .filter_map(|mem| match mem {
            Member::ScProcessImp { method, .. } => Some(method.body.is_some()),
            _ => None,
        })
        .collect();
    assert_eq!(
        imp_bodies,
        [false, true],
        "add_method is defined out of class"
    );
    let acc = m
        .objects()
        .into_iter()
        .find(|o| o.name.name == "acc")
        .unwrap();
    assert_eq!(acc.kind, ScObjectKind::Signal);
    assert!(acc.declarator.sc_init.is_some());
}

/// `SC_FORK … SC_JOIN` / `SC_CJOIN` (§5.6) with a trailing comma.
#[test]
fn fork_join() {
    let r = parse_clean(
        "void run(sc_event& e) {
            int r;
            SC_FORK
                sc_spawn(&r, sc_bind(&top::rr, this, \"1\", sc_ref(e))),
                sc_spawn(&r, sc_bind(&top::rr, this, \"2\", sc_ref(e))),
            SC_JOIN
            SC_FORK sc_spawn(f) SC_CJOIN
        }",
    );
    let f = r.unit.functions()[0];
    let forks: Vec<_> = f
        .body
        .as_ref()
        .unwrap()
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::ScFork {
                spawns, clocked, ..
            } => Some((spawns.len(), *clocked)),
            _ => None,
        })
        .collect();
    assert_eq!(forks, [(2, false), (1, true)]);
}

/// §5.2.9: the process macros expand to a block in SystemC 2.3, so the
/// `;` after `SC_METHOD(f)` is optional; §5.2.8 `SC_HAS_PROCESS(m);` may
/// also stand at namespace scope before an out-of-class constructor.
#[test]
fn process_macro_without_semicolon_and_namespace_has_process() {
    let r = parse_clean(
        "SC_MODULE(m) { sc_in<bool> clk; void f(); void g();\n\
         SC_CTOR(m) { SC_METHOD(f) sensitive << clk.pos(); SC_THREAD(g) } };\n\
         class n : public sc_module { public: n(sc_module_name nm); void h(); };\n\
         SC_HAS_PROCESS(n);\n\
         n::n(sc_module_name nm) : sc_module(nm) { SC_THREAD(h); }",
    );
    let m = r.unit.modules()[0];
    assert_eq!(r.unit.processes(m).len(), 2);
}

/// The main file is file 0 even with `-D` definitions, so spans of the
/// top-level source never point into a command-line pseudo-file.
#[test]
fn main_file_is_file_zero() {
    let r = systemc::parse_with_options("SC_MODULE(m) {};", &[], &[("A", "1"), ("B", "2")]);
    assert_clean(&r);
    assert_eq!(r.files[0].path, "<input>");
    assert_eq!(r.unit.modules()[0].span.file, 0);
}

/// The AST serializes to JSON (the `sv-parse --dump-json` envelope).
#[cfg(feature = "json-cli")]
#[test]
fn ast_serializes() {
    let r = parse_fixture("counter.cpp");
    let json = serde_json::to_string(&r.unit).unwrap();
    assert!(json.contains("\"ScProcess\""));
}
