//! §25.10, §23.3.3: an instance with an interface port sees the parameters
//! of the interface instance bound to it through the port formal, and finds
//! them under the bound instance's path in the design-wide parameter table.
//! A sorted set of the table's dotted keys answers that lookup with a range
//! scan instead of a pass over every entry. It is built on the first lookup
//! (a design without interface ports never builds it) and kept exact by
//! `set_param`/`remove_param`, through which elaboration makes every write to
//! the table; a table whose size no longer matches the tracked changes is
//! re-indexed before the next lookup.

use super::{ElaboratedModule, params_insert_traced};
use crate::value::Value;
use std::collections::BTreeSet;
use std::ops::Bound;

#[derive(Debug, Default)]
pub struct ParamPrefixIndex {
    /// The keys of `parameters` that contain a `.`, once built.
    keys: Option<BTreeSet<String>>,
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
        let new_key =
            index.keys.is_some() && key.contains('.') && !self.parameters.contains_key(&key);
        let indexed = new_key.then(|| key.clone());
        let previous = params_insert_traced(&mut self.parameters, site, key, value);
        if previous.is_none() {
            index.len += 1;
        }
        if let (Some(keys), Some(key)) = (index.keys.as_mut(), indexed) {
            keys.insert(key);
        }
        previous
    }

    /// Remove from `parameters`, keeping the prefix index exact.
    pub(crate) fn remove_param(&mut self, key: &str) -> Option<Value> {
        let previous = self.parameters.remove(key);
        if previous.is_some() {
            let index = &mut self.param_index;
            index.len = index.len.saturating_sub(1);
            if let Some(keys) = index.keys.as_mut() {
                keys.remove(key);
            }
        }
        previous
    }

    /// Call `f` with the rest of each key of `parameters` that starts with
    /// `prefix` (which must contain a `.`) and its value, in key order.
    pub(crate) fn for_each_parameter_with_prefix(
        &mut self,
        prefix: &str,
        mut f: impl FnMut(&str, &Value),
    ) {
        debug_assert!(prefix.contains('.'));
        let index = &mut self.param_index;
        if index.keys.is_none() || index.len != self.parameters.len() {
            index.keys = Some(
                self.parameters
                    .keys()
                    .filter(|key| key.contains('.'))
                    .cloned()
                    .collect(),
            );
            index.len = self.parameters.len();
            #[cfg(test)]
            {
                index.builds += 1;
            }
        }
        let keys = index.keys.as_ref().expect("index built above");
        for key in keys
            .range::<str, _>((Bound::Included(prefix), Bound::Unbounded))
            .take_while(|key| key.starts_with(prefix))
        {
            f(&key[prefix.len()..], &self.parameters[key]);
        }
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
}
