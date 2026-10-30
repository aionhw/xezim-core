// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this file,
// You can obtain one at http://mozilla.org/MPL/2.0/.

//! xezim: tests of xezim's changes to the parser (see README.md).

use crate::ast::token_range::WithTokenSpan;
use crate::ast::*;
use crate::data::{Diagnostic, Source};
use crate::syntax::VHDLParser;
use crate::VHDLStandard;
use std::path::Path;

fn parse(code: &str) -> (DesignFile, Vec<Diagnostic>) {
    let parser = VHDLParser::new(VHDLStandard::VHDL2008);
    let source = Source::inline(Path::new("xezim.vhd"), code);
    let mut diags = Vec::new();
    let file = parser.parse_design_source(&source, &mut diags);
    (file, diags)
}

fn package_decls(file: &DesignFile) -> &[WithTokenSpan<Declaration>] {
    match &file.design_units[0].1 {
        AnyDesignUnit::Primary(AnyPrimaryUnit::Package(p)) => &p.decl,
        _ => panic!("not a package"),
    }
}

/// STD.STANDARD as the IEEE P1076 sources write it.
#[test]
fn range_implementation_defined() {
    let (file, diags) = parse(
        "package p is
           type integer is range implementation_defined;
           type time is range implementation_defined units fs; ps = 1000 fs; end units;
         end package;",
    );
    assert!(diags.is_empty(), "{diags:?}");
    for d in package_decls(&file) {
        let Declaration::Type(t) = &d.item else {
            panic!("not a type")
        };
        let range = match &t.def {
            TypeDefinition::Numeric(r) => r,
            TypeDefinition::Physical(p) => &p.range,
            _ => panic!("not numeric"),
        };
        assert!(matches!(range, Range::Attribute(a) if a.as_range().is_some()));
    }
}

/// LRM 6.4.2.3 signal kinds and LRM 7.4 disconnection specifications.
#[test]
fn guarded_signal_declarations() {
    let (file, diags) = parse(
        "package p is
           signal r : bit register;
           signal b : bit bus := '0';
           signal s : bit;
           disconnect r : bit after 2 ns;
           disconnect others : bit after 1 ns;
         end package;",
    );
    assert!(diags.is_empty(), "{diags:?}");
    let decls = package_decls(&file);
    let kinds: Vec<Option<SignalKind>> = decls[..3]
        .iter()
        .map(|d| match &d.item {
            Declaration::Object(o) => o.signal_kind,
            _ => panic!("not an object"),
        })
        .collect();
    assert_eq!(
        kinds,
        vec![Some(SignalKind::Register), Some(SignalKind::Bus), None]
    );
    assert!(matches!(
        &decls[3].item,
        Declaration::Disconnection(DisconnectionSpecification {
            signals: GuardedSignalList::Names(n),
            ..
        }) if n.len() == 1
    ));
    assert!(matches!(
        &decls[4].item,
        Declaration::Disconnection(DisconnectionSpecification {
            signals: GuardedSignalList::Others,
            ..
        })
    ));
}

/// LRM 11.6 guarded assignments and postponed signal assignments.
#[test]
fn guarded_and_postponed_assignments() {
    let (file, diags) = parse(
        "architecture a of e is
         begin
           q <= guarded d;
           with sel select q2 <= guarded '1' when '1', '0' when others;
           postponed r <= x;
           postponed proc(y);
         end architecture;",
    );
    assert!(diags.is_empty(), "{diags:?}");
    let AnyDesignUnit::Secondary(AnySecondaryUnit::Architecture(a)) = &file.design_units[0].1
    else {
        panic!("not an architecture")
    };
    let flags: Vec<(bool, bool)> = a
        .statements
        .iter()
        .filter_map(|s| match &s.statement.item {
            ConcurrentStatement::Assignment(x) => Some((x.guarded, x.postponed)),
            _ => None,
        })
        .collect();
    assert_eq!(flags, vec![(true, false), (true, false), (false, true)]);
    assert!(matches!(
        &a.statements[3].statement.item,
        ConcurrentStatement::ProcedureCall(c) if c.postponed
    ));
}

/// `pure function` in a protected type declaration (LRM 5.6.2).
#[test]
fn pure_function_in_protected_type() {
    let (_, diags) = parse(
        "package p is
           type t is protected
             pure function f return integer;
             impure function g return integer;
           end protected;
         end package;",
    );
    assert!(diags.is_empty(), "{diags:?}");
}

/// An error keeps the other design units of the file.
#[test]
fn errors_keep_other_design_units() {
    // A missing `)` in a port list; a stray token between units.
    let (file, diags) = parse(
        "entity a is
           port (x : in bit
         end entity;
         garbage;
         entity b is
         end entity;",
    );
    assert!(!diags.is_empty());
    assert_eq!(file.design_units.len(), 2);
}

/// `-- vhdl_ls off` does not hide code.
#[test]
fn vhdl_ls_off_is_not_honoured() {
    let (file, diags) = parse(
        "-- vhdl_ls off
         entity a is
         end entity;",
    );
    assert!(diags.is_empty(), "{diags:?}");
    assert_eq!(file.design_units.len(), 1);
}

fn parse19(code: &str) -> (DesignFile, Vec<Diagnostic>) {
    let parser = VHDLParser::new(VHDLStandard::VHDL2019);
    let source = Source::inline(Path::new("xezim19.vhd"), code);
    let mut diags = Vec::new();
    let file = parser.parse_design_source(&source, &mut diags);
    (file, diags)
}

/// VHDL-2019 LRM 6.5.3 generic type classes.
#[test]
fn generic_type_classes() {
    let (file, diags) = parse19(
        "entity e is
           generic (
             type t0;
             type t1 is private;
             type t2 is <>;
             type t3 is (<>);
             type t4 is range <>;
             type t5 is units <>;
             type t6 is range <> . <>;
             type t7 is array (t3 range <>) of t1;
             type t8 is array (natural range 0 to 3, type is (<>)) of type is private;
             type t9 is access t1;
             type t10 is file of t1
           );
         end entity;",
    );
    assert!(diags.is_empty(), "{diags:?}");
    let AnyDesignUnit::Primary(AnyPrimaryUnit::Entity(e)) = &file.design_units[0].1 else {
        panic!("not an entity")
    };
    let classes: Vec<Option<&IncompleteTypeDefinition>> = e
        .generic_clause
        .as_ref()
        .unwrap()
        .items
        .iter()
        .map(|g| match g {
            InterfaceDeclaration::Type(_) => None,
            InterfaceDeclaration::TypeClass(t) => Some(&t.definition.item),
            _ => panic!("not a type"),
        })
        .collect();
    use IncompleteTypeDefinition as I;
    assert!(classes[0].is_none());
    assert!(matches!(classes[1], Some(I::Private)));
    assert!(matches!(classes[2], Some(I::Scalar)));
    assert!(matches!(classes[3], Some(I::Discrete)));
    assert!(matches!(classes[4], Some(I::Integer)));
    assert!(matches!(classes[5], Some(I::Physical)));
    assert!(matches!(classes[6], Some(I::Floating)));
    assert!(matches!(classes[7], Some(I::Array(i, _))
        if matches!(i[..], [IncompleteArrayIndex::Unbounded(_)])));
    assert!(matches!(classes[8], Some(I::Array(i, e))
        if matches!(i[..], [IncompleteArrayIndex::Constraint(_), IncompleteArrayIndex::Anonymous(_)])
            && matches!(**e, IncompleteSubtype::Anonymous(_))));
    assert!(matches!(classes[9], Some(I::Access(_))));
    assert!(matches!(classes[10], Some(I::File(_))));
}

fn package_body_decls(file: &DesignFile) -> &[WithTokenSpan<Declaration>] {
    match &file.design_units[0].1 {
        AnyDesignUnit::Secondary(AnySecondaryUnit::PackageBody(p)) => &p.decl,
        _ => panic!("not a package body"),
    }
}

/// VHDL-2019 LRM 10.13: `return when c;` and conditional return values.
#[test]
fn conditional_return() {
    let (file, diags) = parse19(
        "package body p is
           function f(a, b : integer) return integer is
           begin
             return a when a > b;
             return a when a > 0 else b when b > 0 else unaffected;
             return a when a < 0 else b;
             return 0;
           end function;
           procedure q(c : boolean) is
           begin
             return when c;
           end procedure;
         end package body;",
    );
    assert!(diags.is_empty(), "{diags:?}");
    let decls = package_body_decls(&file);
    let Declaration::SubprogramBody(f) = &decls[0].item else {
        panic!()
    };
    let rets: Vec<&ReturnStatement> = f
        .statements
        .iter()
        .map(|s| match &s.statement.item {
            SequentialStatement::Return(r) => r,
            _ => panic!("not a return"),
        })
        .collect();
    let c0 = rets[0].conditionals.as_ref().unwrap();
    assert_eq!(c0.conditionals.len(), 1);
    assert!(c0.else_item.is_none());
    let c1 = rets[1].conditionals.as_ref().unwrap();
    assert_eq!(c1.conditionals.len(), 2);
    assert!(matches!(&c1.else_item, Some((None, _))));
    let c2 = rets[2].conditionals.as_ref().unwrap();
    assert!(matches!(&c2.else_item, Some((Some(_), _))));
    assert!(rets[3].expression.is_some() && rets[3].conditionals.is_none());
    let Declaration::SubprogramBody(q) = &decls[1].item else {
        panic!()
    };
    assert!(matches!(&q.statements[0].statement.item,
        SequentialStatement::Return(r) if r.condition.is_some() && r.expression.is_none()));
}

/// VHDL-2019 sequential block statement; an error before 2019.
#[test]
fn sequential_block() {
    let code = "architecture a of e is
         begin
           process
           begin
             blk : block is
               variable v : integer := 1;
             begin
               v := v + 1;
             end block blk;
             block
             begin
               null;
             end;
             wait;
           end process;
         end architecture;";
    let (file, diags) = parse19(code);
    assert!(diags.is_empty(), "{diags:?}");
    let AnyDesignUnit::Secondary(AnySecondaryUnit::Architecture(a)) = &file.design_units[0].1
    else {
        panic!()
    };
    let ConcurrentStatement::Process(p) = &a.statements[0].statement.item else {
        panic!()
    };
    let SequentialStatement::Block(b) = &p.statements[0].statement.item else {
        panic!("not a block")
    };
    assert_eq!((b.decl.len(), b.statements.len()), (1, 1));
    assert!(p.statements[0].label.tree.is_some());
    assert!(matches!(&p.statements[1].statement.item, SequentialStatement::Block(_)));
    let (_, diags) = parse(code);
    assert!(!diags.is_empty());
}

/// VHDL-2019 protected types: a generic clause and map, private variables,
/// and the other declarative items of LRM 5.6.2.
#[test]
fn protected_type_header_and_items() {
    let (file, diags) = parse19(
        "package p is
           type t is protected
             generic (type e; n : natural);
             generic map (e => integer, n => 4);
             use work.q.all;
             private variable inner : other_t;
             alias g is inner.get [return integer];
             attribute a of t : type is 1;
             procedure put(x : integer);
             function h is new hh generic map (x => 1);
           end protected t;
         end package;",
    );
    assert!(diags.is_empty(), "{diags:?}");
    let Declaration::Type(t) = &package_decls(&file)[0].item else {
        panic!()
    };
    let TypeDefinition::Protected(pt) = &t.def else {
        panic!()
    };
    assert_eq!(pt.generic_clause.as_ref().unwrap().items.len(), 2);
    assert!(pt.generic_map.is_some());
    let kinds: Vec<&str> = pt
        .items
        .iter()
        .map(|i| match i {
            ProtectedTypeDeclarativeItem::Subprogram(_) => "sub",
            ProtectedTypeDeclarativeItem::Other(_) => "other",
            ProtectedTypeDeclarativeItem::Private(_) => "private",
        })
        .collect();
    assert_eq!(kinds, ["other", "private", "other", "other", "sub", "other"]);
}

/// VHDL-2019 §5.6.4 protected type instantiation; an error before 2019.
#[test]
fn protected_type_instance() {
    let code = "package p is
           type q is new work.g.queue_pt generic map (elem => integer, n => 4);
           type r is new queue_pt;
         end package;";
    let (file, diags) = parse19(code);
    assert!(diags.is_empty(), "{diags:?}");
    let decls = package_decls(&file);
    assert!(matches!(&decls[0].item, Declaration::Type(t)
        if matches!(&t.def, TypeDefinition::ProtectedInstance(_, Some(_)))));
    assert!(matches!(&decls[1].item, Declaration::Type(t)
        if matches!(&t.def, TypeDefinition::ProtectedInstance(_, None))));
    let (_, diags) = parse(code);
    assert!(!diags.is_empty());
}
