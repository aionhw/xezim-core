// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this file,
// You can obtain one at http://mozilla.org/MPL/2.0/.

//! xezim: tests of xezim's changes to the parser (see README.md).

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

fn package_decls(file: &DesignFile) -> &[crate::ast::token_range::WithTokenSpan<Declaration>] {
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
