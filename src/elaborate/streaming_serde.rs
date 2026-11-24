//! Streaming `serde::Serialize` for [`ElaboratedModule`].
//!
//! Deferred instance bodies (`pending_always`, `pending_initial`,
//! `pending_cont_assign`, `deferred_function_bodies`, `deferred_task_bodies`)
//! are materialized one item at a time directly into the serializer and dropped
//! immediately. The serialized stream is byte-for-byte identical to calling
//! [`ElaboratedModule::materialize_pending`] first, without retaining every
//! materialized AST simultaneously in memory (aionhw/xezim#721).

use super::*;
use serde::ser::{Serialize, SerializeMap, SerializeSeq, SerializeStruct, Serializer};

/// Returns `false` only when `p` is guaranteed not to trigger unpacked-array
/// expansion (`expanded_array_assign_parts`), avoiding a redundant rewrite
/// during the length-counting pass for ordinary scalar continuous assignments.
fn pending_ca_may_expand_array(p: &PendingContAssign, elab: &ElaboratedModule) -> bool {
    if elab.arrays.is_empty() && elab.unpacked_decl_dims.is_empty() {
        return false;
    }
    let is_plain_non_array_ident = |expr: &Expression, is_net_init: bool| -> bool {
        let ExprKind::Ident(h) = &expr.kind else {
            return false;
        };
        if h.root.is_some() || h.path.len() != 1 || !h.path[0].selects.is_empty() {
            return false;
        }
        let name = h.path[0].name.name.as_str();
        if name.starts_with("$unit::") {
            return false;
        }
        if is_net_init {
            let full = cat2(&p.ctx.prefix, name);
            return !elab.arrays.contains_key(&full)
                && !elab.unpacked_decl_dims.contains_key(full.as_str());
        }
        if p.ctx.port_map.contains_key(name) || p.ctx.interface_map.contains_key(name) {
            return false;
        }
        if p.ctx.local_names.contains(name) {
            let full = cat2(&p.ctx.prefix, name);
            !elab.arrays.contains_key(&full) && !elab.unpacked_decl_dims.contains_key(full.as_str())
        } else {
            !elab.arrays.contains_key(name)
                && !elab.unpacked_decl_dims.contains_key(name)
                && !name.contains('.')
        }
    };
    !(is_plain_non_array_ident(&p.lhs_source, p.lhs_is_net_initializer)
        && is_plain_non_array_ident(&p.rhs_source, false))
}

struct StreamingAlways<'a> {
    eager: &'a [AlwaysBlock],
    pending: &'a [PendingAlways],
}

impl Serialize for StreamingAlways<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.eager.len() + self.pending.len()))?;
        for block in self.eager {
            seq.serialize_element(block)?;
        }
        for pending in self.pending {
            let block = pending.materialize_ref();
            seq.serialize_element(&block)?;
        }
        seq.end()
    }
}

struct StreamingInitial<'a> {
    eager: &'a [InitialBlock],
    pending: &'a [PendingInitial],
}

impl Serialize for StreamingInitial<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.eager.len() + self.pending.len()))?;
        for block in self.eager {
            seq.serialize_element(block)?;
        }
        for pending in self.pending {
            let block = pending.materialize_ref();
            seq.serialize_element(&block)?;
        }
        seq.end()
    }
}

struct StreamingContAssigns<'a>(&'a ElaboratedModule);

impl Serialize for StreamingContAssigns<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let elab = self.0;
        let mut total = elab.continuous_assigns.len();
        for p in &elab.pending_cont_assign {
            if pending_ca_may_expand_array(p, elab) {
                let ca = p.materialize_ref(&elab.parameters);
                if let Some(parts) = expanded_array_assign_parts(&ca, elab) {
                    total += parts.len();
                    continue;
                }
            }
            total += 1;
        }
        let mut seq = serializer.serialize_seq(Some(total))?;
        for ca in &elab.continuous_assigns {
            seq.serialize_element(ca)?;
        }
        for p in &elab.pending_cont_assign {
            let ca = p.materialize_ref(&elab.parameters);
            if pending_ca_may_expand_array(p, elab)
                && let Some(parts) = expanded_array_assign_parts(&ca, elab)
            {
                for part in &parts {
                    seq.serialize_element(part)?;
                }
            } else {
                seq.serialize_element(&ca)?;
            }
        }
        seq.end()
    }
}

struct StreamingFunctions<'a> {
    functions: &'a FuncTable,
    deferred: &'a HashMap<String, Rc<CallableRewriteCtx>>,
}

impl Serialize for StreamingFunctions<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.functions.len()))?;
        for (key, fd) in self.functions.iter() {
            if let Some(ctx) = self.deferred.get(key) {
                let mut materialized = fd.clone();
                materialized.items = crate::ast::cache::without_scope_caches(|| {
                    ctx.materialize_body(&fd.ports, &fd.items)
                })
                .into();
                map.serialize_entry(key, &materialized)?;
            } else {
                map.serialize_entry(key, fd)?;
            }
        }
        map.end()
    }
}

struct StreamingTasks<'a> {
    tasks: &'a HashMap<String, TaskDeclaration>,
    deferred: &'a HashMap<String, Rc<CallableRewriteCtx>>,
}

impl Serialize for StreamingTasks<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.tasks.len()))?;
        for (key, td) in self.tasks.iter() {
            if let Some(ctx) = self.deferred.get(key) {
                let mut materialized = td.clone();
                materialized.items = crate::ast::cache::without_scope_caches(|| {
                    ctx.materialize_body(&td.ports, &td.items)
                })
                .into();
                map.serialize_entry(key, &materialized)?;
            } else {
                map.serialize_entry(key, td)?;
            }
        }
        map.end()
    }
}

impl Serialize for ElaboratedModule {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // Exhaustive destructuring: adding, renaming, or removing any field on
        // `ElaboratedModule` fails to compile until updated here to match
        // `#[derive(Deserialize)]` field order.
        let ElaboratedModule {
            name,
            tick_s,
            signals,
            typed_decls: _,
            completed_ports: _,
            ranged_port_widths: _,
            unit_member_slots: _,
            hidden_bare_types: _,
            wildcard_shadowed,
            port_order,
            continuous_assigns,
            tran_switches,
            udp_instances,
            always_blocks,
            initial_blocks,
            final_blocks,
            static_init_blocks,
            program_initial_blocks,
            parameters,
            declared_parameters,
            typedefs,
            typedef_elem_widths,
            typedef_types,
            nettype_resolvers: _,
            shadowed_nettypes: _,
            arrays,
            associative_arrays,
            assoc_elem_widths,
            assoc_index_widths,
            classes,
            covergroups,
            functions,
            tasks,
            func_decl_scope,
            class_decl_pkg,
            dpi_imports,
            dpi_import_pkg,
            dpi_import_in_design,
            dpi_exports,
            dpi_export_c_names,
            clocking_blocks,
            lets,
            modport_views,
            clocking_signal_dirs,
            clocking_output_stages,
            specify_delays,
            module_paths,
            timing_checks,
            resolved_net_kinds,
            gate_fall_delays,
            gate_driven_nets,
            assoc_defaults,
            dynamic_arrays,
            net_strengths,
            strength_drivers,
            supply_nets,
            descending_arrays,
            unpacked_decl_dims,
            ascending_packed,
            typedef_unpacked_dims,
            queue_max_sizes,
            queue_vars,
            arrays_2d,
            packages,
            pkg_subr_owner,
            pkg_var_decls,
            pkg_var_init_blocks,
            def_pkg_imports,
            sequences,
            packed_struct_fields,
            struct_field_range_idents,
            var_decl_types,
            param_decl_types,
            struct_members,
            packed_signal_elem_widths,
            packed_full_dims,
            vector_nets,
            string_signals,
            modport_member_dirs,
            class_type_args,
            interfaces,
            interface_param_defaults,
            checker_decls,
            property_decls,
            property_params,
            property_param_defaults,
            array_elem_class,
            assoc_key_type_names,
            coll_shapes,
            arrays_nd,
            deferred_param_exprs,
            nets,
            implicit_nets,
            interconnect_nets,
            elab_diagnostics,
            instances,
            upward_scopes: _,
            resolved_binds,
            bind_sites: _,
            param_index: _,
            out_of_class_constraints,
            timeunit_exp,
            timeprecision_exp,
            module_timescale_exp,
            modules_without_timescale,
            enum_members,
            package_enum_members,
            decl_sites,
            foreign_package_names,
            foreign_displaced,
            two_state_signals,
            z_init_signals,
            pending_always,
            pending_initial,
            pending_cont_assign,
            deferred_function_bodies,
            deferred_task_bodies,
            net_delays: _,
            const_decl_inits,
            forward_typedef_names,
            events,
            port_aliases,
            tri_select_pulls: _,
            interface_port_aliases,
            input_port_actuals,
            sampled_input_ports,
            elided_port_hashes,
            elided_port_count,
            elided_port_leaves,
            alias_pairs,
            alias_groups,
            alias_canon,
            net_port_merges,
            source_texts: _,
            source_files,
            src_file_of_module,
            source_orig_lines,
            source_line_maps: _,
        } = self;

        let mut st = serializer.serialize_struct("ElaboratedModule", 119)?;
        st.serialize_field("name", name)?;
        st.serialize_field("tick_s", tick_s)?;
        st.serialize_field("signals", signals)?;
        st.serialize_field("wildcard_shadowed", wildcard_shadowed)?;
        st.serialize_field("port_order", port_order)?;
        if pending_cont_assign.is_empty() {
            st.serialize_field("continuous_assigns", continuous_assigns)?;
        } else {
            st.serialize_field("continuous_assigns", &StreamingContAssigns(self))?;
        }
        st.serialize_field("tran_switches", tran_switches)?;
        st.serialize_field("udp_instances", udp_instances)?;
        if pending_always.is_empty() {
            st.serialize_field("always_blocks", always_blocks)?;
        } else {
            st.serialize_field(
                "always_blocks",
                &StreamingAlways {
                    eager: always_blocks,
                    pending: pending_always,
                },
            )?;
        }
        if pending_initial.is_empty() {
            st.serialize_field("initial_blocks", initial_blocks)?;
        } else {
            st.serialize_field(
                "initial_blocks",
                &StreamingInitial {
                    eager: initial_blocks,
                    pending: pending_initial,
                },
            )?;
        }
        st.serialize_field("final_blocks", final_blocks)?;
        st.serialize_field("static_init_blocks", static_init_blocks)?;
        st.serialize_field("program_initial_blocks", program_initial_blocks)?;
        st.serialize_field("parameters", parameters)?;
        st.serialize_field("declared_parameters", declared_parameters)?;
        st.serialize_field("typedefs", typedefs)?;
        st.serialize_field("typedef_elem_widths", typedef_elem_widths)?;
        st.serialize_field("typedef_types", typedef_types)?;
        st.serialize_field("arrays", arrays)?;
        st.serialize_field("associative_arrays", associative_arrays)?;
        st.serialize_field("assoc_elem_widths", assoc_elem_widths)?;
        st.serialize_field("assoc_index_widths", assoc_index_widths)?;
        st.serialize_field("classes", classes)?;
        st.serialize_field("covergroups", covergroups)?;
        if deferred_function_bodies.is_empty() {
            st.serialize_field("functions", functions)?;
        } else {
            st.serialize_field(
                "functions",
                &StreamingFunctions {
                    functions,
                    deferred: deferred_function_bodies,
                },
            )?;
        }
        if deferred_task_bodies.is_empty() {
            st.serialize_field("tasks", tasks)?;
        } else {
            st.serialize_field(
                "tasks",
                &StreamingTasks {
                    tasks,
                    deferred: deferred_task_bodies,
                },
            )?;
        }
        st.serialize_field("func_decl_scope", func_decl_scope)?;
        st.serialize_field("class_decl_pkg", class_decl_pkg)?;
        st.serialize_field("dpi_imports", dpi_imports)?;
        st.serialize_field("dpi_import_pkg", dpi_import_pkg)?;
        st.serialize_field("dpi_import_in_design", dpi_import_in_design)?;
        st.serialize_field("dpi_exports", dpi_exports)?;
        st.serialize_field("dpi_export_c_names", dpi_export_c_names)?;
        st.serialize_field("clocking_blocks", clocking_blocks)?;
        st.serialize_field("lets", lets)?;
        st.serialize_field("modport_views", modport_views)?;
        st.serialize_field("clocking_signal_dirs", clocking_signal_dirs)?;
        st.serialize_field("clocking_output_stages", clocking_output_stages)?;
        st.serialize_field("specify_delays", specify_delays)?;
        st.serialize_field("module_paths", module_paths)?;
        st.serialize_field("timing_checks", timing_checks)?;
        st.serialize_field("resolved_net_kinds", resolved_net_kinds)?;
        st.serialize_field("gate_fall_delays", gate_fall_delays)?;
        st.serialize_field("gate_driven_nets", gate_driven_nets)?;
        st.serialize_field("assoc_defaults", assoc_defaults)?;
        st.serialize_field("dynamic_arrays", dynamic_arrays)?;
        st.serialize_field("net_strengths", net_strengths)?;
        st.serialize_field("strength_drivers", strength_drivers)?;
        st.serialize_field("supply_nets", supply_nets)?;
        st.serialize_field("descending_arrays", descending_arrays)?;
        st.serialize_field("unpacked_decl_dims", unpacked_decl_dims)?;
        st.serialize_field("ascending_packed", ascending_packed)?;
        st.serialize_field("typedef_unpacked_dims", typedef_unpacked_dims)?;
        st.serialize_field("queue_max_sizes", queue_max_sizes)?;
        st.serialize_field("queue_vars", queue_vars)?;
        st.serialize_field("arrays_2d", arrays_2d)?;
        st.serialize_field("packages", packages)?;
        st.serialize_field("pkg_subr_owner", pkg_subr_owner)?;
        st.serialize_field("pkg_var_decls", pkg_var_decls)?;
        st.serialize_field("pkg_var_init_blocks", pkg_var_init_blocks)?;
        st.serialize_field("def_pkg_imports", def_pkg_imports)?;
        st.serialize_field("sequences", sequences)?;
        st.serialize_field("packed_struct_fields", packed_struct_fields)?;
        st.serialize_field("struct_field_range_idents", struct_field_range_idents)?;
        st.serialize_field("var_decl_types", var_decl_types)?;
        st.serialize_field("param_decl_types", param_decl_types)?;
        st.serialize_field("struct_members", struct_members)?;
        st.serialize_field("packed_signal_elem_widths", packed_signal_elem_widths)?;
        st.serialize_field("packed_full_dims", packed_full_dims)?;
        st.serialize_field("vector_nets", vector_nets)?;
        st.serialize_field("string_signals", string_signals)?;
        st.serialize_field("modport_member_dirs", modport_member_dirs)?;
        st.serialize_field("class_type_args", class_type_args)?;
        st.serialize_field("interfaces", interfaces)?;
        st.serialize_field("interface_param_defaults", interface_param_defaults)?;
        st.serialize_field("checker_decls", checker_decls)?;
        st.serialize_field("property_decls", property_decls)?;
        st.serialize_field("property_params", property_params)?;
        st.serialize_field("property_param_defaults", property_param_defaults)?;
        st.serialize_field("array_elem_class", array_elem_class)?;
        st.serialize_field("assoc_key_type_names", assoc_key_type_names)?;
        st.serialize_field("coll_shapes", coll_shapes)?;
        st.serialize_field("arrays_nd", arrays_nd)?;
        st.serialize_field("deferred_param_exprs", deferred_param_exprs)?;
        st.serialize_field("nets", nets)?;
        st.serialize_field("implicit_nets", implicit_nets)?;
        st.serialize_field("interconnect_nets", interconnect_nets)?;
        st.serialize_field("elab_diagnostics", elab_diagnostics)?;
        st.serialize_field("instances", instances)?;
        st.serialize_field("resolved_binds", resolved_binds)?;
        st.serialize_field("out_of_class_constraints", out_of_class_constraints)?;
        st.serialize_field("timeunit_exp", timeunit_exp)?;
        st.serialize_field("timeprecision_exp", timeprecision_exp)?;
        st.serialize_field("module_timescale_exp", module_timescale_exp)?;
        st.serialize_field("modules_without_timescale", modules_without_timescale)?;
        st.serialize_field("enum_members", enum_members)?;
        st.serialize_field("package_enum_members", package_enum_members)?;
        st.serialize_field("decl_sites", decl_sites)?;
        st.serialize_field("foreign_package_names", foreign_package_names)?;
        st.serialize_field("foreign_displaced", foreign_displaced)?;
        st.serialize_field("two_state_signals", two_state_signals)?;
        st.serialize_field("z_init_signals", z_init_signals)?;
        st.serialize_field("const_decl_inits", const_decl_inits)?;
        st.serialize_field("forward_typedef_names", forward_typedef_names)?;
        st.serialize_field("events", events)?;
        st.serialize_field("port_aliases", port_aliases)?;
        st.serialize_field("interface_port_aliases", interface_port_aliases)?;
        st.serialize_field("input_port_actuals", input_port_actuals)?;
        st.serialize_field("sampled_input_ports", sampled_input_ports)?;
        st.serialize_field("elided_port_hashes", elided_port_hashes)?;
        st.serialize_field("elided_port_count", elided_port_count)?;
        st.serialize_field("elided_port_leaves", elided_port_leaves)?;
        st.serialize_field("alias_pairs", alias_pairs)?;
        st.serialize_field("alias_groups", alias_groups)?;
        st.serialize_field("alias_canon", alias_canon)?;
        st.serialize_field("net_port_merges", net_port_merges)?;
        st.serialize_field("source_files", source_files)?;
        st.serialize_field("src_file_of_module", src_file_of_module)?;
        st.serialize_field("source_orig_lines", source_orig_lines)?;
        st.end()
    }
}
