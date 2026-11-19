//! §25.10, §23.3.3: an instance with an interface port sees the parameters
//! of the interface instance bound to it through the port formal, and finds
//! them under the bound instance's path in the design-wide parameter table.
//! An ordered index of the table's dotted keys answers that lookup with a
//! range scan instead of a pass over every entry. It is built on the first
//! lookup (a design without interface ports never builds it) and kept exact
//! by `set_param`/`remove_param`, through which elaboration makes every write
//! to the table; a table whose size no longer matches the tracked changes is
//! re-indexed before the next lookup.
//!
//! The parameters of one instance differ in their last component only, so
//! the index holds the path of an instance once (aionhw/xezim#721). A key is
//! stored with its last `.` written as a separator no name contains, which
//! puts the keys of one path next to each other in plain byte order. A path
//! with one key holds that key whole, which costs what a plain set of the
//! keys costs; a path with more holds the path and the sorted last
//! components.

use super::{ElaboratedModule, params_insert_traced};
use crate::value::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Bound;

/// Stands for the last `.` of a stored key.
const SEP: char = '\u{1}';

/// The sorted last components of the keys of one path.
type Leaves = Box<Vec<Box<str>>>;

/// `key` as its stored path (through the separator) and last component.
fn stored(key: &str) -> (String, &str) {
    let dot = key.rfind('.').unwrap_or(0);
    let mut path = String::with_capacity(key.len());
    path.push_str(&key[..dot]);
    path.push(SEP);
    (path, &key[dot + 1..])
}

/// The dotted keys of the table.
#[derive(Debug, Default)]
struct Keys {
    /// `None` beside a whole stored key, the last components beside a stored
    /// path. A path has either one whole key or one entry of two or more
    /// components (of any number when one is empty, which a whole key cannot
    /// express). No other stored key begins with a stored path.
    paths: BTreeMap<Box<str>, Option<Leaves>>,
    /// Keys that contain the separator themselves, as they are.
    odd: BTreeSet<Box<str>>,
}

impl Keys {
    /// Add `key`, which contains a `.`.
    fn insert(&mut self, key: &str) {
        if key.contains(SEP) {
            self.odd.insert(key.into());
            return;
        }
        let (mut path, leaf) = stored(key);
        // The path's own entry, else the one whole key of this path, is the
        // first entry from the path on.
        let mut alone = None;
        if let Some((have, leaves)) = self
            .paths
            .range_mut::<str, _>((Bound::Included(path.as_str()), Bound::Unbounded))
            .next()
            && have.starts_with(path.as_str())
        {
            match leaves {
                Some(leaves) => {
                    if let Err(at) = leaves.binary_search_by(|have| (**have).cmp(leaf)) {
                        leaves.insert(at, leaf.into());
                    }
                    return;
                }
                None => alone = Some(have.clone()),
            }
        }
        match alone {
            Some(alone) if &alone[path.len()..] != leaf => {
                self.paths.remove(&alone);
                let mut leaves: Vec<Box<str>> = vec![alone[path.len()..].into(), leaf.into()];
                leaves.sort_unstable();
                self.paths.insert(path.into(), Some(Box::new(leaves)));
            }
            Some(_) => {}
            None if leaf.is_empty() => {
                self.paths
                    .insert(path.into(), Some(Box::new(vec![leaf.into()])));
            }
            None => {
                path.push_str(leaf);
                self.paths.insert(path.into(), None);
            }
        }
    }

    fn remove(&mut self, key: &str) {
        if key.contains(SEP) {
            self.odd.remove(key);
            return;
        }
        let (mut path, leaf) = stored(key);
        let Some(Some(leaves)) = self.paths.get_mut(path.as_str()) else {
            path.push_str(leaf);
            self.paths.remove(path.as_str());
            return;
        };
        if let Ok(at) = leaves.binary_search_by(|have| (**have).cmp(leaf)) {
            leaves.remove(at);
        }
        match leaves.as_slice() {
            [] => {
                self.paths.remove(path.as_str());
            }
            [last] if !last.is_empty() => {
                let whole = format!("{path}{last}");
                self.paths.remove(path.as_str());
                self.paths.insert(whole.into(), None);
            }
            _ => {}
        }
    }

    /// Every key that starts with `prefix` (a path and its `.`), in key
    /// order.
    fn with_prefix(&self, prefix: &str, mut f: impl FnMut(&str)) {
        let under = |from: &str| {
            let from = from.to_string();
            self.paths
                .range::<str, _>((Bound::Included(from.as_str()), Bound::Unbounded))
                .take_while(move |(have, _)| have.starts_with(from.as_str()))
        };
        // The keys of the path itself: one entry, in order as it is.
        let (own, _) = stored(prefix);
        let mut key = String::from(prefix);
        let mut own_keys = |f: &mut dyn FnMut(&str)| {
            for (have, leaves) in under(&own) {
                let mut each = |leaf: &str| {
                    key.truncate(prefix.len());
                    key.push_str(leaf);
                    f(&key);
                };
                match leaves {
                    None => each(&have[own.len()..]),
                    Some(leaves) => leaves.iter().for_each(|leaf| each(leaf)),
                }
            }
        };
        // The keys of the paths below it, and those held as they are.
        let mut deeper = under(prefix).peekable();
        let mut odd = self
            .odd
            .range::<str, _>((Bound::Included(prefix), Bound::Unbounded))
            .take_while(|have| have.starts_with(prefix))
            .peekable();
        if deeper.peek().is_none() && odd.peek().is_none() {
            return own_keys(&mut f);
        }
        // A deeper path can sort between the keys of a shallower one
        // (`a.b.c.W` before `a.b.d`).
        let mut keys = Vec::new();
        own_keys(&mut |key| keys.push(key.to_string()));
        for (have, leaves) in deeper {
            let (path, last) = have.split_once(SEP).unwrap_or((have, ""));
            match leaves {
                None => keys.push(format!("{path}.{last}")),
                Some(leaves) => keys.extend(leaves.iter().map(|leaf| format!("{path}.{leaf}"))),
            }
        }
        keys.extend(odd.map(|key| key.to_string()));
        keys.sort_unstable();
        keys.iter().for_each(|key| f(key));
    }
}

#[derive(Debug, Default)]
pub struct ParamPrefixIndex {
    /// The keys of `parameters` that contain a `.`, once built.
    keys: Option<Keys>,
    /// The size of `parameters` that the tracked changes imply.
    len: usize,
    /// How many times the index was built.
    #[cfg(test)]
    builds: usize,
}

impl ElaboratedModule {
    /// Insert into `parameters`, keeping the prefix index exact.
    pub(crate) fn set_param(&mut self, site: u32, key: String, value: Value) -> Option<Value> {
        let index = &mut self.param_index;
        if let Some(keys) = index.keys.as_mut()
            && key.contains('.')
            && !self.parameters.contains_key(&key)
        {
            keys.insert(&key);
        }
        let previous = params_insert_traced(&mut self.parameters, site, key, value);
        if previous.is_none() {
            index.len += 1;
        }
        previous
    }

    /// Remove from `parameters`, keeping the prefix index exact.
    pub(crate) fn remove_param(&mut self, key: &str) -> Option<Value> {
        let previous = self.parameters.remove(key);
        if previous.is_some() {
            let index = &mut self.param_index;
            index.len = index.len.saturating_sub(1);
            if let Some(keys) = index.keys.as_mut()
                && key.contains('.')
            {
                keys.remove(key);
            }
        }
        previous
    }

    /// Call `f` with the rest of each key of `parameters` that starts with
    /// `prefix` (a path and its `.`) and its value, in key order.
    pub(crate) fn for_each_parameter_with_prefix(
        &mut self,
        prefix: &str,
        mut f: impl FnMut(&str, &Value),
    ) {
        if !prefix.ends_with('.') {
            // Not a path: the index cannot answer; read the table.
            let mut found: Vec<_> = self
                .parameters
                .iter()
                .filter(|(key, _)| key.starts_with(prefix))
                .collect();
            found.sort_unstable_by(|a, b| a.0.cmp(b.0));
            for (key, value) in found {
                f(&key[prefix.len()..], value);
            }
            return;
        }
        let index = &mut self.param_index;
        if index.keys.is_none() || index.len != self.parameters.len() {
            let mut keys = Keys::default();
            for key in self.parameters.keys().filter(|key| key.contains('.')) {
                keys.insert(key);
            }
            index.keys = Some(keys);
            index.len = self.parameters.len();
            #[cfg(test)]
            {
                index.builds += 1;
            }
        }
        let keys = index.keys.as_ref().expect("index built above");
        keys.with_prefix(prefix, |key| {
            f(&key[prefix.len()..], &self.parameters[key]);
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What the lookup replaced: a scan of the whole table.
    fn scan(m: &ElaboratedModule, prefix: &str) -> Vec<(String, i64)> {
        let mut found: Vec<_> = m
            .parameters
            .iter()
            .filter(|(k, _)| k.starts_with(prefix))
            .map(|(k, v)| (k[prefix.len()..].to_string(), v.to_i64().unwrap_or(-1)))
            .collect();
        found.sort();
        found
    }

    fn lookup(m: &mut ElaboratedModule, prefix: &str) -> Vec<(String, i64)> {
        let mut found = Vec::new();
        m.for_each_parameter_with_prefix(prefix, |rest, v| {
            found.push((rest.to_string(), v.to_i64().unwrap_or(-1)))
        });
        found
    }

    #[test]
    fn lookup_matches_a_scan_of_the_table_after_any_sequence_of_changes() {
        let stems = [
            "a", "a.b", "a.bc", "a.b.c", "a.b[1]", "a.b[10]", "b", "g[1].c", "g[10].c", "g[1]",
        ];
        let leaves = ["W", "V", "k.V", "W[0]"];
        let mut m = ElaboratedModule::new("top".into());
        // A deterministic sequence of insertions, overwrites and removals,
        // with lookups at every prefix in between.
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        for step in 0..3000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let stem = stems[(state % stems.len() as u64) as usize];
            let leaf = leaves[((state >> 8) % leaves.len() as u64) as usize];
            let key = format!("{stem}.{leaf}");
            if (state >> 16) % 3 == 0 {
                m.remove_param(&key);
            } else {
                m.set_param(line!(), key, Value::from_u64(step, 32));
            }
            if step % 7 == 0 {
                for stem in stems {
                    let prefix = format!("{stem}.");
                    assert_eq!(lookup(&mut m, &prefix), scan(&m, &prefix), "{prefix}");
                }
            }
        }
    }

    #[test]
    fn the_index_is_built_once_for_a_design_of_many_interface_ports() {
        // Each instance also writes the members of a struct parameter into
        // the table; they go through the tracked path, so no rebuild.
        let mut src = String::from(
            "typedef struct packed {logic [3:0] a; logic [3:0] b;} cfg_t;
interface cfg_if #(parameter int W = 4) ();
endinterface
module user(cfg_if c, output logic [7:0] y);
  localparam cfg_t K = '{a: 4'd1, b: 4'd2};
  localparam int WW = c.W;
  assign y = WW + K.a - 1;
endmodule
module top;
  logic [7:0] y [100];
",
        );
        for i in 0..100 {
            src += &format!("  cfg_if #(.W({i})) c{i}();\n  user u{i}(.c(c{i}), .y(y[{i}]));\n");
        }
        src += "endmodule\n";
        let (_, m) = crate::parse_and_elaborate_multi(
            &[src],
            Some("top"),
            &[],
            &["top.sv".to_string()],
            &[],
        )
        .expect("elaborate");
        for i in 0..100 {
            assert_eq!(m.parameters[&format!("u{i}.WW")].to_i64(), Some(i));
        }
        assert_eq!(m.param_index.builds, 1);
    }

    #[test]
    fn a_write_that_bypasses_the_tracked_methods_is_picked_up() {
        let mut m = ElaboratedModule::new("top".into());
        m.set_param(line!(), "c.W".into(), Value::from_u64(1, 32));
        assert_eq!(lookup(&mut m, "c."), [("W".to_string(), 1)]);
        m.parameters.insert("c.V".into(), Value::from_u64(2, 32));
        assert_eq!(lookup(&mut m, "c."), scan(&m, "c."));
        m.parameters.remove("c.W");
        assert_eq!(lookup(&mut m, "c."), scan(&m, "c."));
    }

    /// The entries and stored text of the index: what its memory is
    /// proportional to.
    fn held(m: &ElaboratedModule) -> (usize, usize) {
        let keys = m.param_index.keys.as_ref().expect("index built");
        let bytes = keys
            .paths
            .iter()
            .map(|(key, leaves)| {
                key.len()
                    + leaves
                        .iter()
                        .flat_map(|l| l.iter())
                        .map(|l| l.len())
                        .sum::<usize>()
            })
            .sum::<usize>()
            + keys.odd.iter().map(|key| key.len()).sum::<usize>();
        (keys.paths.len() + keys.odd.len(), bytes)
    }

    /// aionhw/xezim#721: the parameters of one instance hold its path once.
    /// A path with a single parameter costs the key and nothing more.
    #[test]
    fn the_keys_of_one_path_hold_the_path_once() {
        let path = |i: usize| format!("top.block_{i}.{}", "p".repeat(200));
        let mut dense = ElaboratedModule::new("top".into());
        let mut sparse = ElaboratedModule::new("top".into());
        let mut text = 0;
        for i in 0..40 {
            for p in 0..25 {
                let key = format!("{}.P{p}", path(i));
                text += key.len();
                dense.set_param(line!(), key, Value::from_u64(p, 32));
            }
            sparse.set_param(line!(), format!("{}.P0", path(i)), Value::from_u64(0, 32));
        }
        assert_eq!(lookup(&mut dense, &format!("{}.", path(7))).len(), 25);
        assert_eq!(lookup(&mut sparse, &format!("{}.", path(7))).len(), 1);
        let (entries, bytes) = held(&dense);
        assert_eq!(entries, 40);
        // 40 paths and 1000 short names, where the keys themselves are 40
        // paths 25 times over.
        assert!(bytes < text / 15, "{bytes} of {text}");
        let (entries, bytes) = held(&sparse);
        assert_eq!(entries, 40);
        assert_eq!(bytes, (0..40).map(|i| path(i).len() + 3).sum::<usize>());
        let keys = sparse.param_index.keys.as_ref().unwrap();
        assert!(keys.paths.values().all(|leaves| leaves.is_none()));
    }

    /// A path moves between its two forms as keys come and go, and the
    /// lookup answers the same in both.
    #[test]
    fn a_path_gains_and_loses_keys() {
        let mut m = ElaboratedModule::new("top".into());
        m.set_param(line!(), "u.c.W".into(), Value::from_u64(1, 32));
        // Built here, with one key under the path.
        assert_eq!(lookup(&mut m, "u.c."), [("W".to_string(), 1)]);
        assert_eq!(held(&m), (1, 5));
        m.set_param(line!(), "u.c.A".into(), Value::from_u64(2, 32));
        m.set_param(line!(), "u.c.Z".into(), Value::from_u64(3, 32));
        // Written again: the table has it already.
        m.set_param(line!(), "u.c.A".into(), Value::from_u64(4, 32));
        assert_eq!(held(&m), (1, 4 + 3));
        assert_eq!(
            lookup(&mut m, "u.c."),
            [
                ("A".to_string(), 4),
                ("W".to_string(), 1),
                ("Z".to_string(), 3)
            ]
        );
        m.remove_param("u.c.W");
        m.remove_param("u.c.A");
        assert_eq!(held(&m), (1, 5));
        assert_eq!(lookup(&mut m, "u.c."), [("Z".to_string(), 3)]);
        m.set_param(line!(), "u.c.B".into(), Value::from_u64(5, 32));
        assert_eq!(
            lookup(&mut m, "u."),
            [("c.B".to_string(), 5), ("c.Z".to_string(), 3)]
        );
        m.remove_param("u.c.B");
        m.remove_param("u.c.Z");
        assert_eq!(held(&m), (0, 0));
        assert_eq!(lookup(&mut m, "u."), []);
        assert_eq!(m.param_index.builds, 1);
    }

    /// The keys under a prefix come in key order whatever paths hold them:
    /// a deeper path sorts between the keys of a shallower one, and a path
    /// that only begins like the prefix is not under it.
    #[test]
    fn keys_of_nested_paths_come_in_key_order() {
        let mut m = ElaboratedModule::new("top".into());
        let keys = [
            "a.b.Z",
            "a.b.d",
            "a.b.c.W",
            "a.b.c.V",
            "a.b.e.k.V",
            "a.b.a",
            "a.b[1].W",
            "a.bc.W",
            "a.b.",
            "a.W",
            "b.W",
            "top_level",
        ];
        for (i, key) in keys.iter().enumerate() {
            m.set_param(line!(), key.to_string(), Value::from_u64(i as u64, 32));
            if i == 3 {
                // Built part way, so both the build and the tracked writes
                // are exercised.
                assert_eq!(lookup(&mut m, "a.b.").len(), 4);
            }
        }
        let mut order = Vec::new();
        m.for_each_parameter_with_prefix("a.b.", |rest, _| order.push(rest.to_string()));
        assert_eq!(order, ["", "Z", "a", "c.V", "c.W", "d", "e.k.V"]);
        order.clear();
        m.for_each_parameter_with_prefix("a.", |rest, _| order.push(rest.to_string()));
        assert_eq!(
            order,
            [
                "W", "b.", "b.Z", "b.a", "b.c.V", "b.c.W", "b.d", "b.e.k.V", "b[1].W", "bc.W"
            ]
        );
        for prefix in [
            "a.b.c.", "a.b[1].", "a.bc.", "b.", "c.", "a.b.e.", "a.b.e.k.",
        ] {
            assert_eq!(lookup(&mut m, prefix), scan(&m, prefix), "{prefix}");
        }
        // A key that holds the index's own separator is kept as it is.
        m.set_param(line!(), "a.b.\u{1}x.W".into(), Value::from_u64(90, 32));
        m.set_param(line!(), "a.b.y\u{1}".into(), Value::from_u64(91, 32));
        for prefix in ["a.b.", "a.", "a.b.\u{1}x.", "a.b.c."] {
            assert_eq!(lookup(&mut m, prefix), scan(&m, prefix), "{prefix:?}");
        }
        m.remove_param("a.b.\u{1}x.W");
        m.remove_param("a.b.y\u{1}");
        assert_eq!(lookup(&mut m, "a.b."), scan(&m, "a.b."));
        // A prefix that is no path is answered from the table.
        order.clear();
        m.for_each_parameter_with_prefix("a.b", |rest, _| order.push(rest.to_string()));
        assert_eq!(order.len(), 9);
        assert_eq!(order[0], ".");
        assert_eq!(m.param_index.builds, 1);
    }
}
