//! IEEE 1800 §5.6.1, §22 and §27: original identifiers and include/macro
//! positions survive artifact reload without changing simulation serialization.
use xezim_core::{XEZIM_BYTECODE_MAGIC, parse_and_elaborate_multi, read_compiled_bytes};

fn design() -> xezim_core::ElaboratedModule {
    let source = "module leaf #(parameter W=2)(input logic [W-1:0] a); endmodule\nmodule top;\n`define DECL logic macro_signal;\n`DECL\nlogic \\dotted.signal ;\nfor(genvar i=0;i<2;i++) begin:g leaf #(.W(i+2)) u(); end\nleaf \\escaped.instance ();\nendmodule\n";
    parse_and_elaborate_multi(&[source.into()], Some("top"), &[], &["nav.sv".into()], &[])
        .unwrap()
        .1
}
#[test]
fn trailer_roundtrip_and_legacy_layout() {
    let elab = design();
    let body = bincode::serde::encode_to_vec(&elab, xezim_core::xez_bincode_config()).unwrap();
    let mut legacy = XEZIM_BYTECODE_MAGIC.to_vec();
    legacy.extend(&body);
    let old = read_compiled_bytes(&legacy).unwrap();
    assert!(old.navigation.symbols.is_empty());
    assert_eq!(old.instances.len(), elab.instances.len());
    let file = std::env::temp_dir().join(format!("xez-nav-{}.xez", std::process::id()));
    for raw in [false, true] {
        xezim_core::set_artifact_uncompressed(raw);
        xezim_core::write_compiled(&elab, file.to_str().unwrap()).unwrap();
        let bytes = std::fs::read(&file).unwrap();
        let loaded = read_compiled_bytes(&bytes).unwrap();
        let disk = xezim_core::read_compiled(file.to_str().unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(
            loaded.navigation.symbols.len(),
            disk.navigation.symbols.len()
        );
        assert_eq!(loaded.signals.len(), elab.signals.len());
        for (name, signal) in &elab.signals {
            assert_eq!(loaded.signals[name].width, signal.width);
        }
        let macro_sym = loaded
            .navigation
            .symbols
            .iter()
            .find(|s| s.path == "macro_signal")
            .unwrap();
        assert_eq!(macro_sym.location.as_ref().unwrap().line, 4);
        assert!(macro_sym.location.as_ref().unwrap().macro_expansion);
        let escaped = loaded
            .navigation
            .symbols
            .iter()
            .find(|s| s.path == "escaped.instance")
            .unwrap();
        assert_eq!(escaped.name, "escaped.instance");
        assert_eq!(escaped.parent, "");
        let generated = loaded
            .navigation
            .symbols
            .iter()
            .find(|s| s.path == "g[1].u")
            .unwrap();
        assert_eq!(generated.parent, "g[1]");
        assert_eq!(generated.name, "u");
        assert_eq!(
            loaded
                .navigation
                .symbols
                .iter()
                .find(|s| s.path == "g[1]")
                .unwrap()
                .location
                .as_ref()
                .unwrap()
                .line,
            6
        );
        // A pre-trailer reader decodes exactly the unchanged simulation object.
        let payload = if raw {
            bytes[8..].to_vec()
        } else {
            zstd::stream::decode_all(&bytes[8..]).unwrap()
        };
        let (legacy_read, used): (xezim_core::ElaboratedModule, usize) =
            bincode::serde::decode_from_slice(&payload, xezim_core::xez_bincode_config()).unwrap();
        assert_eq!(legacy_read.instances.len(), elab.instances.len());
        assert_eq!(used, body.len());
        let mut damaged = XEZIM_BYTECODE_MAGIC.to_vec();
        damaged.extend(&payload[..payload.len() - 1]);
        assert!(
            read_compiled_bytes(&damaged)
                .unwrap_err()
                .contains("truncated navigation")
        );
        let mut wrong = XEZIM_BYTECODE_MAGIC.to_vec();
        wrong.extend(&payload);
        wrong[8 + used + 7] = 99;
        assert!(
            read_compiled_bytes(&wrong)
                .unwrap_err()
                .contains("navigation trailer version")
        );
    }
    xezim_core::set_artifact_uncompressed(false);
    std::fs::remove_file(file).unwrap();
}
