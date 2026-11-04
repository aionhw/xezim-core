//! IEEE 1800-2023 §13.4.3: a constant function call made for each instance
//! evaluates over that instance's parameters (#737). The call starts from the
//! parameters its body can read rather than a copy of the whole design-wide
//! table; a body whose reads are not listed (`$bits`) keeps the copy.

const ITER: &str = "
  function automatic int ceil_log2(input int v);
    int r;
    r = 0;
    while ((1 << r) < v) r++;
    return r;
  endfunction
";

/// `top` has a `localparam int N` of its own, which the instance's `N`
/// shadows; instance `g[k].u` gets `N = 3*k*k + 1`.
fn design(variant: &str) -> String {
    let rec = "
  function automatic int ceil_log2(input int v);
    return (v <= 1) ? 0 : 1 + ceil_log2((v + 1) / 2);
  endfunction
";
    let bits = "
  function automatic int ceil_log2(input int v);
    int r;
    r = 0;
    while ((1 << r) < v) r++;
    return r + $bits(v) - 32;
  endfunction
";
    // A package parameter read bare and qualified from the package's function.
    let biased = "
  localparam int BIAS = 3;
  function automatic int ceil_log2(input int v);
    int r;
    for (r = 0; (1 << r) < v; r++) ;
    return r + 2 * BIAS - pk::BIAS - 3;
  endfunction
";
    let val = "3*k*k + 1";
    let (pre, leaf, top_decl, inst) = match variant {
        "body" | "recursive" | "bits" => (
            String::new(),
            format!(
                "module leaf #(parameter int N = 8);{}  localparam int L = ceil_log2(N);\nendmodule\n",
                match variant {
                    "body" => ITER,
                    "recursive" => rec,
                    _ => bits,
                }
            ),
            "",
            format!("leaf #(.N({val})) u();"),
        ),
        "header" => (
            format!("package pk;{ITER}endpackage\n"),
            "module leaf #(parameter int N = 8, parameter int L = pk::ceil_log2(N));\nendmodule\n"
                .to_string(),
            "",
            format!("leaf #(.N({val})) u();"),
        ),
        "override" => (
            String::new(),
            "module leaf #(parameter int N = 8, parameter int L = 0);\nendmodule\n".to_string(),
            ITER,
            format!("leaf #(.N({val}), .L(ceil_log2({val}))) u();"),
        ),
        "package" | "package_param" => (
            format!(
                "package pk;{}endpackage\n",
                if variant == "package" { ITER } else { biased }
            ),
            "module leaf #(parameter int N = 8);\n  localparam int L = pk::ceil_log2(N);\nendmodule\n"
                .to_string(),
            "",
            format!("leaf #(.N({val})) u();"),
        ),
        _ => unreachable!(),
    };
    format!(
        "{pre}{leaf}module top;\n  localparam int N = 6;{top_decl}\n  \
         for (genvar k = 0; k < N; k++) begin : g\n    {inst}\n  end\nendmodule\n"
    )
}

#[test]
fn each_instance_gets_its_own_parameters_function_result() {
    for variant in [
        "body",
        "header",
        "override",
        "package",
        "package_param",
        "recursive",
        "bits",
    ] {
        let source = design(variant);
        let design = xezim_core::parse_and_elaborate_multi(
            &[source.clone()],
            Some("top"),
            &[],
            &["top.sv".to_string()],
            &[],
        )
        .unwrap_or_else(|e| panic!("{variant}: {e}\n{source}"))
        .1;
        for k in 0..6u64 {
            let n = 3 * k * k + 1;
            let want = if n <= 1 {
                0
            } else {
                64 - (n - 1).leading_zeros() as u64
            };
            let path = format!("g[{k}].u");
            assert_eq!(
                design.parameters[&format!("{path}.N")].to_u64(),
                Some(n),
                "{variant} {path}.N"
            );
            assert_eq!(
                design.parameters[&format!("{path}.L")].to_u64(),
                Some(want),
                "{variant} {path}.L\n{source}"
            );
        }
    }
}
