//! Elaborating the same design twice writes the same artifact bytes. Each
//! `std` hash map or set iterates in an order of its own random keys, so one
//! that is serialized, or that fills a serialized map, reorders the artifact
//! between runs: the module timescales were filled from one, and the
//! gate-driven nets, wildcard-shadowed names and foreign package names were
//! held in them, and so were the names a struct typedef's member ranges read
//! (§7.2), kept per member for the port width diagnostic.

const SRC: &str = "\
package p; localparam int a = 1; localparam int b = 2; localparam int c = 3; endpackage
`timescale 1ns/1ps
module m1; wire x1, x2, x3, x4; and g1(x1, x2, x3); or g2(x2, x3, x4); not g3(x3, x4); buf g4(x4, x1); endmodule
`timescale 10ns/1ns
module m2; import p::*; localparam int a = 5; localparam int b = 6; wire y1, y2; nand n1(y1, y2, y2); nor n2(y2, y1, y1); endmodule
`timescale 1us/1ns
module m3; m1 u1 (); m2 u2 (); endmodule
`timescale 100ps/10ps
module m4; m1 u1 (); endmodule
`timescale 1ms/1us
module top; m3 a (); m4 b (); m2 c (); initial #1 $display(\"%0d\", p::c); endmodule
";

/// Several typedefs, each with several members whose ranges read parameters.
const STRUCT_SRC: &str = "\
package cfg; parameter int AW = 12; parameter int DW = 32; parameter int SW = DW / 8; parameter int IW = 4; endpackage
package bus;
  import cfg::*;
  typedef struct packed { logic [SW-1:0] strb; logic [AW-1:0] addr; logic [DW-1:0] data; logic [IW-1:0] id; } req_t;
  typedef struct packed { logic [DW-1:0] data; logic [IW-1:0] id; logic [SW-1:0] keep; } rsp_t;
  typedef struct packed { logic [AW-1:0] lo; logic [AW-1:0] hi; logic [IW:0] tag; logic [SW:0] mask; } range_t;
endpackage
module leaf (input bus::req_t req, output bus::rsp_t rsp);
  bus::range_t r;
  assign rsp = '{data: req.data, id: req.id, keep: req.strb};
endmodule
module top; bus::req_t q; bus::rsp_t p0, p1; leaf a (.req(q), .rsp(p0)); leaf b (.req(q), .rsp(p1)); endmodule
";

fn artifact(dir: &std::path::Path, n: usize) -> Vec<u8> {
    artifact_of(SRC, dir, n)
}

fn artifact_of(src: &str, dir: &std::path::Path, n: usize) -> Vec<u8> {
    let (_, m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("elaboration failed: {e}"));
    let path = dir.join(format!("a{n}.xez"));
    xezim_core::write_compiled(&m, path.to_str().unwrap()).expect("write artifact");
    std::fs::read(&path).expect("read artifact")
}

#[test]
fn same_design_writes_same_bytes() {
    let dir = std::env::temp_dir().join(format!("xezim_core_det_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mkdir");
    let first = artifact(&dir, 0);
    for n in 1..8 {
        assert!(
            first == artifact(&dir, n),
            "elaboration {n} wrote different bytes"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn struct_member_range_names_write_same_bytes() {
    let dir = std::env::temp_dir().join(format!("xezim_core_det_struct_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mkdir");
    let first = artifact_of(STRUCT_SRC, &dir, 0);
    for n in 1..8 {
        assert!(
            first == artifact_of(STRUCT_SRC, &dir, n),
            "elaboration {n} wrote different bytes"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
