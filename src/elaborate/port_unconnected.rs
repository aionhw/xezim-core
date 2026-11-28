//! §23.3.2: a port that an instance leaves out of its connection list is
//! unconnected. An input then reads z (or its declared default, §23.2.2.4)
//! and an output drives nothing. That is legal, but it is the classic wiring
//! slip, and commercial simulators warn about it. An explicit `.p()` or an
//! empty positional slot states that the port is meant to be open, and `.*`
//! connects every port, so neither is reported.

use super::*;

/// The ports of `ports` that `conns` leaves out: not named, not covered by a
/// positional slot and not covered by `.*`. Inputs with a declared default
/// are skipped, since §23.2.2.4 makes leaving them out the way to use the
/// default.
pub(super) fn omitted_ports<'a>(ports: &'a PortList, conns: &[PortConnection]) -> Vec<&'a str> {
    let count = match ports {
        PortList::Ansi(p) => p.len(),
        PortList::NonAnsi(p) => p.len(),
        PortList::Empty => 0,
    };
    // Fast path: a list as long as the port list covers every port unless
    // it repeats a name, which is reported elsewhere.
    if conns.len() >= count || conns.iter().any(|c| matches!(c, PortConnection::Wildcard)) {
        return Vec::new();
    }
    let ordered = conns
        .iter()
        .filter(|c| matches!(c, PortConnection::Ordered(_)))
        .count();
    let named = |name: &str| {
        conns.iter().any(|c| match c {
            PortConnection::Named { name: n, .. } | PortConnection::NamedIdent { name: n, .. } => {
                n.name == name
            }
            _ => false,
        })
    };
    (ordered..count)
        .filter_map(|i| ports.get(i))
        .filter(|p| match p {
            GenericPort::Ansi(a) => {
                let input = !matches!(
                    a.direction,
                    Some(PortDirection::Output) | Some(PortDirection::Inout)
                );
                !(input && a.default.is_some())
            }
            GenericPort::NonAnsi(_) => true,
        })
        .map(|p| match p {
            GenericPort::Ansi(a) => a.name.name.as_str(),
            GenericPort::NonAnsi(n) => n.name.as_str(),
        })
        .filter(|name| !name.is_empty() && !named(name))
        .collect()
}

/// Warn, once per (module, port), that instance `inst_prefix` of
/// `sub_mod_name` leaves `port` out of its connection list.
pub(super) fn warn_omitted_port(
    sub_mod_name: &str,
    port: &str,
    inst_prefix: &str,
    span: Span,
    elab: &ElaboratedModule,
    parent_def: &str,
) {
    use std::sync::{Mutex, OnceLock};
    static SEEN: OnceLock<Mutex<std::collections::HashSet<(String, String)>>> = OnceLock::new();
    if crate::elab_diags_muted() {
        return;
    }
    let seen = SEEN.get_or_init(|| Mutex::new(std::collections::HashSet::new()));
    let key = (sub_mod_name.to_string(), port.to_string());
    if !seen.lock().map(|mut g| g.insert(key)).unwrap_or(false) {
        return;
    }
    let where_ = match span_location_of(elab, span, parent_def) {
        Some(loc) => format!("at {loc}"),
        None => format!("at source offset {}", span.start),
    };
    crate::elab_diag(format!(
        "[xezim][warning] unconnected port: module '{sub_mod_name}' port '{port}' is not in \
         the connection list of instance '{}' ({where_}); an input left out reads z and an \
         output left out drives nothing (IEEE 1800-2017 §23.3.2). Connect it, or write \
         `.{port}()` to leave it open on purpose. Further instances of this (module, port) \
         pair are not reported.",
        inst_prefix.trim_end_matches('.'),
    ));
}
