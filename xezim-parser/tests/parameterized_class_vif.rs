//! IEEE 1800-2017 §25.9 / §8.4: parameterized virtual interface properties.
//! Class-item parsing retains `virtual` as a qualifier for the elaborator;
//! the remaining `interface` type must consume its parameter assignments.

use sv_parser::{
    ast::{
        Description,
        decl::{ClassItem, ClassMethodKind, ClassQualifier},
        expr::{ExprKind, NumberLiteral},
        types::DataType,
    },
    parse,
};

#[test]
fn named_parameterized_class_vif_reproducer() {
    let source = include_str!("fixtures/parameterized_class_vif.sv");
    let result = parse(source);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Description::Class(class) = &result.source.descriptions[1] else {
        panic!("expected agent class");
    };
    let ClassItem::Property(property) = &class.items[0] else {
        panic!("expected vif property");
    };
    assert_eq!(property.qualifiers, [ClassQualifier::Virtual]);
    assert_eq!(property.declarators[0].name.name, "vif");
    let DataType::Interface {
        name,
        modport,
        type_args,
        ..
    } = &property.data_type
    else {
        panic!("expected interface data type: {:?}", property.data_type);
    };
    assert_eq!(name.name, "bus_if");
    assert!(modport.is_none());
    assert_eq!(type_args.len(), 2);
    for (arg, (expected_name, expected_value)) in
        type_args.iter().zip([("WIDTH", "16"), ("LANES", "2")])
    {
        let ExprKind::NamedArg { name, expr } = &arg.kind else {
            panic!("expected named parameter: {arg:?}");
        };
        assert_eq!(name.name, expected_name);
        let ExprKind::Number(NumberLiteral::Integer { value, .. }) =
            &expr.as_ref().expect("parameter value").kind
        else {
            panic!("expected integer parameter value: {arg:?}");
        };
        assert_eq!(value, expected_value);
    }
}

#[test]
fn class_vif_type_preserves_parameters_modport_and_qualifiers() {
    for keyword in ["virtual", "virtual interface"] {
        for (params, count) in [("", 0), ("#(16, 2)", 2), ("#(.LANES(2), .WIDTH(16))", 2)] {
            for modport in ["", ".driver"] {
                for (prefix, expected_qualifiers) in [
                    ("", vec![ClassQualifier::Virtual]),
                    (
                        "protected ",
                        vec![ClassQualifier::Protected, ClassQualifier::Virtual],
                    ),
                    (
                        "static ",
                        vec![ClassQualifier::Static, ClassQualifier::Virtual],
                    ),
                ] {
                    let source = format!(
                        "class agent; {prefix}{keyword} bus_if {params}{modport} first, second; endclass"
                    );
                    let result = parse(&source);
                    assert!(result.errors.is_empty(), "{source}: {:?}", result.errors);
                    let Description::Class(class) = &result.source.descriptions[0] else {
                        panic!("expected class: {source}");
                    };
                    assert_eq!(class.items.len(), 1, "{source}");
                    let ClassItem::Property(property) = &class.items[0] else {
                        panic!("expected property: {source}");
                    };
                    assert_eq!(property.qualifiers, expected_qualifiers, "{source}");
                    assert_eq!(property.declarators.len(), 2, "{source}");
                    assert_eq!(property.declarators[0].name.name, "first");
                    assert_eq!(property.declarators[1].name.name, "second");
                    let (name, parsed_modport, type_args) = match &property.data_type {
                        DataType::Interface {
                            name,
                            modport,
                            type_args,
                            ..
                        } => (name.as_ref(), modport.as_deref(), type_args),
                        DataType::TypeReference {
                            name, type_args, ..
                        } if keyword == "virtual" && modport.is_empty() => {
                            (&name.name, None, type_args)
                        }
                        other => panic!("expected interface type: {source}: {other:?}"),
                    };
                    assert_eq!(name.name, "bus_if");
                    assert_eq!(type_args.len(), count, "{source}");
                    assert_eq!(
                        parsed_modport.map(|m| m.name.as_str()),
                        if modport.is_empty() {
                            None
                        } else {
                            Some("driver")
                        },
                        "{source}"
                    );
                }
            }
        }
    }
}

#[test]
fn virtual_methods_keep_their_qualifiers() {
    let result = parse(
        "virtual class agent;
           virtual function void run(); endfunction
           virtual task drive(); endtask
           pure virtual function void check();
           extern virtual function void report();
         endclass",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Description::Class(class) = &result.source.descriptions[0] else {
        panic!("expected class");
    };
    assert_eq!(class.items.len(), 4);
    for item in &class.items {
        let ClassItem::Method(method) = item else {
            panic!("expected method: {item:?}");
        };
        assert!(method.qualifiers.contains(&ClassQualifier::Virtual));
    }
    assert!(
        matches!(&class.items[2], ClassItem::Method(m) if matches!(m.kind, ClassMethodKind::PureVirtual(_)))
    );
    assert!(
        matches!(&class.items[3], ClassItem::Method(m) if matches!(m.kind, ClassMethodKind::Extern(_)))
    );
}
