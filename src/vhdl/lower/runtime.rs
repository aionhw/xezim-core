//! Fixed SystemVerilog support code of a lowered VHDL design: GHDL-format
//! messages, check failures, integer arithmetic, and the per-element-type
//! array helpers (instantiated from a template for each array element
//! representation the design uses).

/// Module items emitted once per lowered design.
pub const COMMON: &str = r#"
  // ---- VHDL runtime -------------------------------------------------------
  // Time in GHDL's report format: the largest unit up to ms that divides it
  // exactly; 0 is "0ms".
  function automatic string vh_time_at(longint t);
    if (t == 0) return "0ms";
    if (t % 64'sd1000000000000 == 0) return $sformatf("%0dms", t / 64'sd1000000000000);
    if (t % 64'sd1000000000 == 0) return $sformatf("%0dus", t / 64'sd1000000000);
    if (t % 64'sd1000000 == 0) return $sformatf("%0dns", t / 64'sd1000000);
    if (t % 64'sd1000 == 0) return $sformatf("%0dps", t / 64'sd1000);
    return $sformatf("%0dfs", t);
  endfunction
  // A report or assertion message (IEEE 1076-2008 §10.3, §10.4), formatted
  // as GHDL does; severity FAILURE ends the simulation with exit status 1.
  function automatic void vh_report(string file, int line, int col, int sev, string msg, bit is_assert);
    string sv_s;
    case (sev)
      0: sv_s = "note";
      1: sv_s = "warning";
      2: sv_s = "error";
      default: sv_s = "failure";
    endcase
    $display("%s:%0d:%0d:@%s:(%s %s): %s", file, line, col, vh_time_at($time), is_assert ? "assertion" : "report", sv_s, msg);
    if (sev >= 3) begin
      $display("ghdl:error: %s failed", is_assert ? "assertion" : "report");
      $display("ghdl:error: simulation failed");
      $__vh_fail;
    end
  endfunction
  function automatic void vh_fatal(string msg);
    $display("ghdl:error: %s", msg);
    $display("ghdl:error: simulation failed");
    $__vh_fail;
  endfunction
  // A value outside its subtype's range (§14.7.3.1 checks).
  function automatic longint vh_chk(longint v, longint lo, longint hi, string file, int line);
    if (v < lo || v > hi) vh_fatal($sformatf("bound check failure at %s:%0d", file, line));
    return v;
  endfunction
  function automatic real vh_chk_r(real v, real lo, real hi, string file, int line);
    if (v < lo || v > hi) vh_fatal($sformatf("bound check failure at %s:%0d", file, line));
    return v;
  endfunction
  // Integer arithmetic outside the base type's range.
  function automatic longint vh_ovf(longint v, longint lo, longint hi);
    if (v < lo || v > hi) vh_fatal("overflow detected");
    return v;
  endfunction
  // `a mod b` (§9.2.7): the sign of b.
  function automatic longint vh_mod(longint a, longint b);
    longint m;
    if (b == 0) begin vh_fatal("division by zero"); return 0; end
    m = a % b;
    if (m != 0 && ((m < 0) != (b < 0))) m = m + b;
    return m;
  endfunction
  function automatic longint vh_rem(longint a, longint b);
    if (b == 0) begin vh_fatal("division by zero"); return 0; end
    return a % b;
  endfunction
  function automatic longint vh_div(longint a, longint b);
    if (b == 0) begin vh_fatal("division by zero"); return 0; end
    return a / b;
  endfunction
  function automatic longint vh_pow(longint a, longint b);
    longint r;
    r = 1;
    for (longint i = 0; i < b; i++) r = r * a;
    return r;
  endfunction
  function automatic real vh_powr(real a, longint b);
    real r;
    r = 1.0;
    if (b >= 0) for (longint i = 0; i < b; i++) r = r * a;
    else for (longint i = 0; i < -b; i++) r = r / a;
    return r;
  endfunction
  // Real to integer: round to nearest, halves away from zero (§9.3.6).
  function automatic longint vh_rtoi(real r);
    if (r >= 0.0) return longint'($floor(r + 0.5));
    return -longint'($floor(-r + 0.5));
  endfunction
  // An array index → storage offset (0-based from 'left), checked.
  function automatic longint vh_ix(longint i, longint l, longint r, bit dn, string file, int line);
    if (dn ? (i > l || i < r) : (i < l || i > r)) begin
      vh_fatal($sformatf("index (%0d) out of bounds (%0d %s %0d) at %s:%0d", i, l, dn ? "downto" : "to", r, file, line));
      return 0;
    end
    return dn ? l - i : i - l;
  endfunction
"#;

/// Helpers for arrays whose elements are represented as `ELEM`, with the
/// array struct named `ARR`. `EQ(a,b)` compares two elements.
pub const ARRAY_TEMPLATE: &str = r#"
  typedef struct { longint l; longint r; bit dn; ELEM d[]; } ARR;
  // An array value with bounds l..r (dn: downto) and n elements.
  function automatic ARR ARR_new(longint l, bit dn, longint n);
    ARR a;
    ELEM t[];
    t = new[n];
    a.l = l;
    a.dn = dn;
    a.r = dn ? l - n + 1 : l + n - 1;
    a.d = t;
    return a;
  endfunction
  function automatic ARR ARR_from(longint l, bit dn, ELEM t[]);
    ARR a;
    a.l = l;
    a.dn = dn;
    a.r = dn ? l - t.size() + 1 : l + t.size() - 1;
    a.d = t;
    return a;
  endfunction
  // `x & y` (§9.2.5): the left operand's bounds and direction, unless it is
  // a null array; `il`/`idn` are the index subtype's left bound and
  // direction (for a result whose left operand is an element).
  function automatic ARR ARR_cat(ARR x, ARR y);
    ELEM t[];
    int nx, ny;
    nx = x.d.size();
    ny = y.d.size();
    t = new[nx + ny];
    for (int i = 0; i < nx; i++) t[i] = x.d[i];
    for (int i = 0; i < ny; i++) t[nx + i] = y.d[i];
    if (nx == 0) return ARR_from(y.l, y.dn, t);
    return ARR_from(x.l, x.dn, t);
  endfunction
  function automatic ARR ARR_cat_ae(ARR x, ELEM e, longint il, bit idn);
    ELEM t[];
    int nx;
    nx = x.d.size();
    t = new[nx + 1];
    for (int i = 0; i < nx; i++) t[i] = x.d[i];
    t[nx] = e;
    if (nx == 0) return ARR_from(il, idn, t);
    return ARR_from(x.l, x.dn, t);
  endfunction
  function automatic ARR ARR_cat_ea(ELEM e, ARR y, longint il, bit idn);
    ELEM t[];
    int ny;
    ny = y.d.size();
    t = new[ny + 1];
    t[0] = e;
    for (int i = 0; i < ny; i++) t[i + 1] = y.d[i];
    return ARR_from(il, idn, t);
  endfunction
  function automatic ARR ARR_cat_ee(ELEM e, ELEM f, longint il, bit idn);
    ELEM t[];
    t = new[2];
    t[0] = e;
    t[1] = f;
    return ARR_from(il, idn, t);
  endfunction
  // Array equality: same length, equal elements in order (§9.2.3).
  function automatic bit ARR_eq(ARR x, ARR y);
    if (x.d.size() != y.d.size()) return 0;
    for (int i = 0; i < x.d.size(); i++) if (!(EQ(x.d[i], y.d[i]))) return 0;
    return 1;
  endfunction
  // Lexicographic `<` (§9.2.3), elements compared as numbers.
  function automatic bit ARR_lt(ARR x, ARR y);
    int n;
    n = x.d.size() < y.d.size() ? x.d.size() : y.d.size();
    for (int i = 0; i < n; i++) begin
      if (x.d[i] < y.d[i]) return 1;
      if (x.d[i] > y.d[i]) return 0;
    end
    return x.d.size() < y.d.size();
  endfunction
  // Slice x(left dir right) (§8.5), checked against x's bounds.
  function automatic ARR ARR_slice(ARR x, longint left, longint right, bit dn, string file, int line);
    ELEM t[];
    longint n, off;
    n = dn ? left - right + 1 : right - left + 1;
    if (n <= 0) return ARR_from(left, dn, t);
    if (dn != x.dn) vh_fatal($sformatf("slice direction mismatch at %s:%0d", file, line));
    off = vh_ix(left, x.l, x.r, x.dn, file, line);
    void'(vh_ix(right, x.l, x.r, x.dn, file, line));
    t = new[n];
    for (longint i = 0; i < n; i++) t[i] = x.d[off + i];
    return ARR_from(left, dn, t);
  endfunction
  // Assign v to a target with bounds of `tgt` (§10.6.2.1): lengths must
  // match; the target keeps its bounds.
  function automatic ARR ARR_conv(ARR tgt, ARR v, string file, int line);
    ELEM t[];
    if (tgt.d.size() != v.d.size()) begin
      vh_fatal($sformatf("bound check failure at %s:%0d", file, line));
      return tgt;
    end
    // Through a local: a struct formal's member passed on directly
    // arrives empty in the simulator.
    t = v.d;
    return ARR_from(tgt.l, tgt.dn, t);
  endfunction
  // Write v into elements of x from offset `off` (slice assignment).
  function automatic ARR ARR_put(ARR x, longint off, ARR v, string file, int line);
    ELEM t[];
    t = x.d;
    if (off < 0 || off + v.d.size() > t.size()) begin
      vh_fatal($sformatf("bound check failure at %s:%0d", file, line));
      return x;
    end
    for (int i = 0; i < v.d.size(); i++) t[off + i] = v.d[i];
    return ARR_from(x.l, x.dn, t);
  endfunction
  function automatic ARR ARR_set(ARR x, longint off, ELEM e);
    ELEM t[];
    t = x.d;
    t[off] = e;
    return ARR_from(x.l, x.dn, t);
  endfunction
"#;

/// Element-wise logical operators for arrays of BIT/BOOLEAN codes (§9.2.2).
pub const LOGIC_TEMPLATE: &str = r#"
  function automatic ARR ARR_lop(ARR x, ARR y, int op, string file, int line);
    ELEM t[];
    if (x.d.size() != y.d.size()) begin
      vh_fatal($sformatf("length mismatch at %s:%0d", file, line));
      return x;
    end
    t = new[x.d.size()];
    for (int i = 0; i < x.d.size(); i++)
      case (op)
        0: t[i] = x.d[i] & y.d[i];
        1: t[i] = x.d[i] | y.d[i];
        2: t[i] = !(x.d[i] & y.d[i]);
        3: t[i] = !(x.d[i] | y.d[i]);
        4: t[i] = x.d[i] ^ y.d[i];
        default: t[i] = !(x.d[i] ^ y.d[i]);
      endcase
    return ARR_from(x.l, x.dn, t);
  endfunction
  function automatic ARR ARR_not(ARR x);
    ELEM t[];
    t = new[x.d.size()];
    for (int i = 0; i < x.d.size(); i++) t[i] = !x.d[i];
    return ARR_from(x.l, x.dn, t);
  endfunction
"#;

/// GHDL's `real'image`: the shortest digits that round-trip, written
/// `d.ddd` (exponent 0) or `d.ddde<exp>`.
pub fn real_image(v: f64) -> String {
    if v == 0.0 {
        return if v.is_sign_negative() {
            "-0.0".into()
        } else {
            "0.0".into()
        };
    }
    let s = format!("{:e}", v);
    let (mant, exp) = s.split_once('e').unwrap_or((&s, "0"));
    let mant = if mant.contains('.') {
        mant.to_string()
    } else {
        format!("{}.0", mant)
    };
    if exp == "0" {
        mant
    } else {
        format!("{}e{}", mant, exp)
    }
}

#[cfg(test)]
mod tests {
    use super::real_image;

    /// Values and images taken from GHDL 4.1 (`real'image`).
    #[test]
    fn real_image_matches_ghdl() {
        for (v, img) in [
            (0.0, "0.0"),
            (1.0, "1.0"),
            (-1.0, "-1.0"),
            (10.0, "1.0e1"),
            (99999.0, "9.9999e4"),
            (0.5, "5.0e-1"),
            (1.5, "1.5"),
            (12345.678, "1.2345678e4"),
            (123456789.0, "1.23456789e8"),
            (1.0 / 3.0, "3.333333333333333e-1"),
            (2.5e-7, "2.5e-7"),
            (3.25, "3.25"),
            (1.0e10, "1.0e10"),
            (0.1, "1.0e-1"),
        ] {
            assert_eq!(real_image(v), img, "{}", v);
        }
    }
}
