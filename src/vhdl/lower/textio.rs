//! STD.TEXTIO (IEEE 1076-2008 §16.4): READLINE, WRITELINE and TEE of TEXT
//! files, and READ / WRITE of the standard types on a LINE, behaving and
//! failing as GHDL does. A LINE is a handle into the STRING heap.

use std::fmt::Write as _;

use super::{Lw, Repr, sv_string};
use crate::vhdl::sema::hir::*;

/// Support code of the TEXTIO procedures (after the heaps).
const TEXTIO: &str = r#"
  // JUSTIFY (§16.4): s padded with spaces to `field` characters, on the
  // left (RIGHT = 0) or the right (LEFT = 1).
  function automatic vh_a_u8 vh_tio_justify(vh_a_u8 s, byte unsigned just, longint field);
    byte unsigned t[];
    longint n, pad;
    n = s.d.size();
    pad = field > n ? field - n : 0;
    t = new[n + pad];
    for (longint i = 0; i < n + pad; i++) t[i] = 32;
    for (longint i = 0; i < n; i++) t[(just == 0 ? pad : 0) + i] = s.d[i];
    return vh_a_u8_from(1, 0, t);
  endfunction
  // L := new STRING'(L.all & JUSTIFY(s, just, field)).
  function automatic void vh_tio_write(inout longint l, input vh_a_u8 s, input byte unsigned just, input longint field);
    vh_a_u8 j;
    vh_a_u8 cur;
    byte unsigned t[];
    j = vh_tio_justify(s, just, field);
    if (l == 0) l = vh_new_vh_a_u8(vh_str(""));
    cur = vh_heap_vh_a_u8[l];
    t = new[cur.d.size() + j.d.size()];
    for (int i = 0; i < cur.d.size(); i++) t[i] = cur.d[i];
    for (int i = 0; i < j.d.size(); i++) t[cur.d.size() + i] = j.d[i];
    vh_heap_vh_a_u8[l] = vh_a_u8_from(1, 0, t);
  endfunction
  // WRITELINE (F, L): the line and a line end, then L designates an empty
  // line.
  function automatic void vh_tio_writeline(int f, inout longint l);
    string s;
    vh_fchk(f, 0);
    s = l == 0 ? "" : vh_sv(vh_heap_vh_a_u8[l]);
    if (f == -1) $display("%s", s);
    else $fwrite(f, "%s\n", s);
    if (l != 0) vh_heap_vh_a_u8.delete(l);
    l = vh_new_vh_a_u8(vh_str(""));
  endfunction
  // TEE (F, L): the line to F and to OUTPUT.
  function automatic void vh_tio_tee(int f, inout longint l);
    string s;
    vh_fchk(f, 0);
    s = l == 0 ? "" : vh_sv(vh_heap_vh_a_u8[l]);
    if (f != -1) $fwrite(f, "%s\n", s);
    $display("%s", s);
    if (l != 0) vh_heap_vh_a_u8.delete(l);
    l = vh_new_vh_a_u8(vh_str(""));
  endfunction
  // READLINE (F, L): the next line of F, without its line end.
  function automatic void vh_tio_readline(int f, inout longint l);
    byte unsigned q[$];
    byte unsigned t[];
    int c;
    vh_fchk(f, 1);
    c = $fgetc(vh_fd(f));
    if (c == -1) vh_report("../../src/std/v08/textio-body.vhdl", 422, 5, 3, "eof in std.textio.readline", 1);
    while (c != -1 && c != 10) begin
      q.push_back(c);
      c = $fgetc(vh_fd(f));
    end
    // A CR before the LF is part of the line end (as GHDL reads it).
    if (c == 10 && q.size() > 0 && q[q.size() - 1] == 13) void'(q.pop_back());
    t = new[q.size()];
    foreach (q[i]) t[i] = q[i];
    if (l != 0) vh_heap_vh_a_u8.delete(l);
    l = vh_new_vh_a_u8(vh_a_u8_from(1, 0, t));
  endfunction
  // A READ that failed without GOOD: GHDL's assertion in its TEXTIO body.
  function automatic void vh_tio_rfail(int line, string what);
    vh_report("../../src/std/v08/textio-body.vhdl", line, 5, 3, {what, " read failure"}, 1);
  endfunction
  // The characters of line L (a null line is dereferenced).
  function automatic vh_a_u8 vh_tio_line(longint l);
    if (l == 0) begin
      vh_fatal("NULL access dereferenced");
      return vh_str("");
    end
    return vh_heap_vh_a_u8[l];
  endfunction
  // L after a READ used its first n characters: the rest, with their
  // indices; an empty rest is a new empty line (1 to 0) unless keep.
  function automatic void vh_tio_used(inout longint l, input longint n, input bit keep);
    vh_a_u8 cur;
    byte unsigned t[];
    longint m;
    cur = vh_heap_vh_a_u8[l];
    m = cur.d.size() - n;
    if (m == 0 && !keep) begin
      vh_heap_vh_a_u8[l] = vh_str("");
      return;
    end
    t = new[m];
    for (longint i = 0; i < m; i++) t[i] = cur.d[n + i];
    vh_heap_vh_a_u8[l] = vh_a_u8_mk(cur.dn ? cur.l - n : cur.l + n, cur.r, cur.dn, t);
  endfunction
  function automatic bit vh_tio_ws(byte unsigned c);
    return c == 32 || c == 9 || c == 160;
  endfunction
  function automatic bit vh_tio_dig(byte unsigned c);
    return c >= 48 && c <= 57;
  endfunction
  // The first index of s from p on that is not whitespace.
  function automatic longint vh_tio_skip(vh_a_u8 s, longint p);
    while (p < s.d.size() && vh_tio_ws(s.d[p])) p++;
    return p;
  endfunction
  // Lower case of an ASCII letter.
  function automatic byte unsigned vh_tio_lc(byte unsigned c);
    return (c >= 65 && c <= 90) ? c + 32 : c;
  endfunction
  // Whether s has `w` (lower case) at p, ignoring case.
  function automatic bit vh_tio_at(vh_a_u8 s, longint p, string w);
    if (p + w.len() > s.d.size()) return 0;
    for (int i = 0; i < w.len(); i++) if (vh_tio_lc(s.d[p + i]) != w.getc(i)) return 0;
    return 1;
  endfunction
  // An INTEGER: whitespace, an optional sign and digits; ok tells whether
  // it was read. The result is the number of characters used: at the end of
  // the line, all of them (a sign alone reads as 1 or -1, whitespace alone
  // fails), as GHDL does.
  function automatic longint vh_tio_rint(vh_a_u8 s, output longint v, output byte unsigned ok);
    longint p;
    int st;
    v = 1;
    ok = 0;
    st = 0;
    for (p = 0; p < s.d.size(); p++) begin
      if (st == 0) begin
        if (vh_tio_ws(s.d[p])) continue;
        if (s.d[p] == 43) st = 1;
        else if (s.d[p] == 45) begin
          v = -1;
          st = 1;
        end else if (vh_tio_dig(s.d[p])) begin
          v = s.d[p] - 48;
          st = 2;
        end else return 0;
      end else if (st == 1) begin
        if (!vh_tio_dig(s.d[p])) return 0;
        v = v * (s.d[p] - 48);
        st = 2;
      end else begin
        if (!vh_tio_dig(s.d[p])) begin
          ok = 1;
          return p;
        end
        v = v * 10;
        v = v < 0 ? v - (s.d[p] - 48) : v + (s.d[p] - 48);
        if (v > 64'sd2147483647 || v < -64'sd2147483648) begin
          vh_fatal("overflow detected");
          return 0;
        end
      end
    end
    ok = st != 0;
    return s.d.size();
  endfunction
  // A REAL from index p: an optional sign, digits, a point, digits and an
  // optional exponent. The index after it (p: none).
  function automatic longint vh_tio_real_at(vh_a_u8 s, longint p, output real v);
    longint b, q, n;
    string t;
    n = s.d.size();
    v = 0.0;
    b = p;
    if (p < n && (s.d[p] == 45 || s.d[p] == 43)) p++;
    q = p;
    while (p < n && vh_tio_dig(s.d[p])) p++;
    if (p == q || p >= n || s.d[p] != 46) return b;
    p++;
    q = p;
    while (p < n && vh_tio_dig(s.d[p])) p++;
    if (p == q) return b;
    if (p < n && (s.d[p] == 101 || s.d[p] == 69)) begin
      p++;
      if (p < n && (s.d[p] == 45 || s.d[p] == 43)) p++;
      q = p;
      while (p < n && vh_tio_dig(s.d[p])) p++;
      if (p == q) return b;
    end
    t = "";
    for (longint i = b; i < p; i++) t = {t, string'(s.d[i])};
    v = t.atoreal();
    return p;
  endfunction
  function automatic longint vh_tio_rreal(vh_a_u8 s, output real v);
    longint p, e;
    p = vh_tio_skip(s, 0);
    e = vh_tio_real_at(s, p, v);
    return e == p ? 0 : e;
  endfunction
  // A BOOLEAN: TRUE or FALSE in any case.
  function automatic longint vh_tio_rbool(vh_a_u8 s, output byte unsigned v);
    longint p;
    v = 0;
    p = vh_tio_skip(s, 0);
    if (vh_tio_at(s, p, "true")) begin
      v = 1;
      return p + 4;
    end
    if (vh_tio_at(s, p, "false")) return p + 5;
    return 0;
  endfunction
  // A CHARACTER: the first one, whatever it is.
  function automatic longint vh_tio_rchar(vh_a_u8 s, output byte unsigned v);
    v = 0;
    if (s.d.size() == 0) return 0;
    v = s.d[0];
    return 1;
  endfunction
  // A BIT: 0 or 1 after whitespace.
  function automatic longint vh_tio_rbit(vh_a_u8 s, output byte unsigned v);
    longint p;
    v = 0;
    p = vh_tio_skip(s, 0);
    if (p >= s.d.size() || (s.d[p] != 48 && s.d[p] != 49)) return 0;
    v = s.d[p] - 48;
    return p + 1;
  endfunction
  // A BIT_VECTOR in binary (w = 1, no underscores), octal (3) or hex (4)
  // digits into v, which keeps its bounds; the bits a digit has beyond v's
  // length must be 0.
  function automatic longint vh_tio_rbv(vh_a_u8 s, inout vh_a_u8 v, input int w);
    longint p, n, nd, d, x;
    byte unsigned b[];
    int c, dv;
    n = v.d.size();
    nd = (n + w - 1) / w;
    b = new[nd * w];
    p = vh_tio_skip(s, 0);
    d = 0;
    while (d < nd) begin
      if (p >= s.d.size()) return 0;
      c = s.d[p];
      if (c == 95 && w > 1 && d > 0) begin
        p++;
        continue;
      end
      if (c >= 48 && c <= 57) dv = c - 48;
      else if (c >= 97 && c <= 102) dv = c - 87;
      else if (c >= 65 && c <= 70) dv = c - 55;
      else return 0;
      if (dv >= (1 << w)) return 0;
      for (int k = 0; k < w; k++) b[d * w + k] = (dv >> (w - 1 - k)) & 1;
      d++;
      p++;
    end
    x = nd * w - n;
    for (longint i = 0; i < x; i++) if (b[i] != 0) return 0;
    for (longint i = 0; i < n; i++) v.d[i] = b[x + i];
    return p;
  endfunction
  // A STRING of v's length, as it is (no whitespace skipped).
  function automatic longint vh_tio_rstr(vh_a_u8 s, inout vh_a_u8 v);
    if (s.d.size() < v.d.size() || v.d.size() == 0) return 0;
    for (longint i = 0; i < v.d.size(); i++) v.d[i] = s.d[i];
    return v.d.size();
  endfunction
  // SREAD: whitespace, then up to v's length characters other than
  // whitespace; n is how many.
  function automatic longint vh_tio_sread(vh_a_u8 s, inout vh_a_u8 v, output longint n);
    longint p;
    p = vh_tio_skip(s, 0);
    n = 0;
    while (n < v.d.size() && p < s.d.size() && !vh_tio_ws(s.d[p])) begin
      v.d[n] = s.d[p];
      n++;
      p++;
    end
    return p;
  endfunction
  // A REAL: as REAL'IMAGE (DIGITS = 0), else with DIGITS decimals.
  function automatic vh_a_u8 vh_tio_real(real x, longint digits);
    if (digits == 0) return vh_str($__vh_real_image(x));
    return vh_str($__vh_real_fixed(x, digits));
  endfunction
  function automatic vh_a_u8 vh_chr(byte unsigned c);
    byte unsigned t[];
    t = new[1];
    t[0] = c;
    return vh_a_u8_from(1, 0, t);
  endfunction
"#;

impl<'a> Lw<'a> {
    /// A call of a TEXTIO procedure.
    pub(super) fn textio_call(
        &mut self,
        name: &str,
        info: &SubInfo,
        args: &[HExpr],
        ind: usize,
        loc: &Loc,
    ) -> String {
        let pad = " ".repeat(ind);
        self.textio = true;
        // The STRING heap backs LINE.
        if let Some(a) = args.iter().find(|a| self.d.is_access(a.ty)) {
            self.heap(a.ty, loc);
        }
        match name {
            "writeline" | "readline" | "tee" => {
                self.files = true;
                let f = self.ex(&args[0]);
                let l = self.ex(&args[1]);
                format!("{}vh_tio_{}({}, {});\n", pad, name, f, l)
            }
            "read" | "sread" | "hread" | "oread" if self.d.is_access(args[0].ty) => {
                self.textio_read(name, info, args, ind, loc)
            }
            "write" | "swrite" | "hwrite" | "owrite"
                if args.len() >= 2 && self.d.is_access(args[0].ty) =>
            {
                let l = self.ex(&args[0]);
                let s = match name {
                    // The digits of a BIT_VECTOR (§16.4).
                    "hwrite" | "owrite" => {
                        let v = self.ex(&args[1]);
                        format!("vh_bvstr({}, {})", v, if name == "hwrite" { 4 } else { 3 })
                    }
                    _ => match self.write_image(info, args, loc) {
                        Some(s) => s,
                        None => return String::new(),
                    },
                };
                let (just, field) = if args.len() >= 4 {
                    (self.ex(&args[2]), self.ex(&args[3]))
                } else {
                    ("0".to_string(), "64'sd0".to_string())
                };
                format!("{}vh_tio_write({}, {}, {}, {});\n", pad, l, s, just, field)
            }
            _ => {
                self.err(loc, format!("'std.textio.{}' is not supported yet", name));
                String::new()
            }
        }
    }

    /// READ, SREAD, OREAD and HREAD of a LINE (§16.4). A read that fails
    /// uses nothing of the line and leaves a scalar VALUE at its subtype's
    /// leftmost value (an array keeps its value); without GOOD it stops
    /// the simulation with GHDL's assertion.
    fn textio_read(
        &mut self,
        name: &str,
        info: &SubInfo,
        args: &[HExpr],
        ind: usize,
        loc: &Loc,
    ) -> String {
        let pad = " ".repeat(ind);
        let std = self.d.std.clone();
        let l = self.ex(&args[0]);
        let target = &args[1];
        let vt = self.d.base(self.d.objects[info.params[1]].ty);
        let r = self.repr(vt, loc);
        self.tmp += 1;
        let n = self.tmp;
        let (used, val, good) = (
            format!("vh_tu{}", n),
            format!("vh_tv{}", n),
            format!("vh_tg{}", n),
        );
        let src = format!("vh_tio_line({})", l);
        self.temps.push((used.clone(), "longint".into()));
        self.temps.push((val.clone(), r.sv()));
        self.temps.push((good.clone(), "byte unsigned".into()));
        let mut out = String::new();
        let is_arr = matches!(r, Repr::Arr(..));
        if is_arr {
            let x = self.ex(target);
            let _ = writeln!(out, "{}{} = {};", pad, val, x);
        }
        // The function reading the value, and GHDL's failure line and name.
        let (call, fail): (String, Option<(u32, &str)>) = if name == "sread" {
            let len = format!("vh_tn{}", n);
            self.temps.push((len.clone(), "longint".into()));
            let _ = writeln!(
                out,
                "{p}{u} = vh_tio_sread({s}, {v}, {len});\n{p}vh_tio_used({l}, {u}, 1);",
                p = pad,
                u = used,
                s = src,
                v = val,
                len = len,
                l = l
            );
            out.push_str(&self.assign_to(target, val.clone(), ind));
            let len_v = self.checked_int(len, args[2].ty, loc);
            out.push_str(&self.assign_to(&args[2], len_v, ind));
            return out;
        } else if name == "hread" || name == "oread" {
            let w = if name == "hread" { 4 } else { 3 };
            (
                format!("vh_tio_rbv({}, {}, {})", src, val, w),
                Some(if w == 4 {
                    (1553, "hexa bit_vector")
                } else {
                    (1456, "octal bit_vector")
                }),
            )
        } else if vt == std.string {
            (
                format!("vh_tio_rstr({}, {})", src, val),
                Some((1280, "string")),
            )
        } else if vt == std.character {
            (
                format!("vh_tio_rchar({}, {})", src, val),
                Some((533, "character")),
            )
        } else if vt == std.bit {
            (format!("vh_tio_rbit({}, {})", src, val), Some((570, "bit")))
        } else if vt == std.bit_vector {
            (
                format!("vh_tio_rbv({}, {}, 1)", src, val),
                Some((650, "bit_vector")),
            )
        } else if vt == std.boolean {
            (
                format!("vh_tio_rbool({}, {})", src, val),
                Some((735, "boolean")),
            )
        } else if vt == std.integer {
            (
                format!("vh_tio_rint({}, {}, {})", src, val, good),
                Some((817, "integer")),
            )
        } else if vt == std.real {
            (
                format!("vh_tio_rreal({}, {})", src, val),
                Some((969, "real")),
            )
        } else if vt == std.time {
            let f = self.time_read_fn();
            (format!("{}({}, {})", f, src, val), Some((1241, "time")))
        } else {
            self.err(
                loc,
                format!("'std.textio.{}' of this type is not supported yet", name),
            );
            return String::new();
        };
        let _ = writeln!(out, "{}{} = {};", pad, used, call);
        if vt != std.integer || name != "read" {
            let _ = writeln!(out, "{}{} = {} != 0;", pad, good, used);
        }
        let _ = writeln!(
            out,
            "{}if ({} != 0) vh_tio_used({}, {}, 0);",
            pad, used, l, used
        );
        // The value read, or (scalar) the leftmost value of the formal's
        // subtype on a failure.
        let rv = self.read_value(target.ty, &val, loc);
        let mut store = self.assign_to(target, rv, ind + 2);
        if !is_arr {
            let left = self.default_value(self.d.objects[info.params[1]].ty, loc);
            let lv = self.read_value(target.ty, &left, loc);
            let on_fail = self.assign_to(target, lv, ind + 2);
            store = format!(
                "{p}if ({g}) begin\n{s}{p}end else begin\n{f}{p}end\n",
                p = pad,
                g = good,
                s = store,
                f = on_fail
            );
        } else {
            store = format!(
                "{p}if ({g}) begin\n{s}{p}end\n",
                p = pad,
                g = good,
                s = store
            );
        }
        out.push_str(&store);
        if args.len() >= 3 {
            out.push_str(&self.assign_to(&args[2], good, ind));
        } else if let Some((line, what)) = fail {
            let _ = writeln!(
                out,
                "{}if (!{}) vh_tio_rfail({}, {});",
                pad,
                good,
                line,
                sv_string(what)
            );
        }
        out
    }

    /// A value read into a target: an integer is range checked.
    fn read_value(&mut self, t: TypeId, v: &str, loc: &Loc) -> String {
        if self.d.is_integer(t) {
            self.checked_int(v.to_string(), t, loc)
        } else {
            v.to_string()
        }
    }

    /// The text WRITE puts for its VALUE (§16.4).
    fn write_image(&mut self, info: &SubInfo, args: &[HExpr], loc: &Loc) -> Option<String> {
        let v = &args[1];
        let vt = self.d.base(self.d.objects[info.params[1]].ty);
        let std = self.d.std.clone();
        let x = self.ex(v);
        if vt == std.string {
            return Some(x);
        }
        if vt == std.character {
            return Some(format!("vh_chr({})", x));
        }
        if vt == std.bit {
            return Some(format!("vh_chr(8'd48 + {})", x));
        }
        if vt == std.time {
            let unit = match args.get(4) {
                Some(u) => self.ex(u),
                None => "64'sd1000000".into(),
            };
            let f = self.time_image_fn();
            return Some(format!("{}({}, {})", f, x, unit));
        }
        if vt == std.real {
            if info.params.len() == 3 {
                self.err(loc, "WRITE of a REAL with a FORMAT is not supported yet");
                return None;
            }
            let digits = match args.get(4) {
                Some(dg) => self.ex(dg),
                None => "0".into(),
            };
            return Some(format!("vh_tio_real({}, {})", x, digits));
        }
        // BIT_VECTOR, BOOLEAN, INTEGER: as TO_STRING.
        Some(self.image(v, v.ty, false))
    }

    /// A TIME value in a unit, as GHDL writes it: the integer part, the
    /// fraction without trailing zeros, and the unit name.
    fn time_image_fn(&mut self) -> String {
        let f = "vh_tio_time".to_string();
        if self.lits.contains_key(&f) {
            return f;
        }
        let units = match &self.d.types[self.d.std.time].kind {
            TypeKind::Physical(u) => u.clone(),
            _ => Vec::new(),
        };
        let mut s = String::from(
            "  function automatic vh_a_u8 vh_tio_time(longint v, longint unit);\n    string name, frac;\n    longint a, fr, w;\n    case (unit)\n",
        );
        for (n, m) in &units {
            let _ = writeln!(s, "      64'sd{}: name = {};", m, sv_string(n));
        }
        s.push_str(
            "      default: name = \"\";\n    endcase\n    a = v < 0 ? -v : v;\n    fr = a % unit;\n    if (fr == 0) return vh_str($sformatf(\"%s%0d %s\", v < 0 ? \"-\" : \"\", a / unit, name));\n    // The fraction's digits: as many as the unit has decimal places.\n    frac = \"\";\n    for (w = unit / 10; w > 0; w = w / 10) begin\n      frac = {frac, string'(8'd48 + (fr / w) % 10)};\n    end\n    while (frac.len() > 0 && frac.getc(frac.len() - 1) == 8'd48) frac = frac.substr(0, frac.len() - 2);\n    return vh_str($sformatf(\"%s%0d.%s %s\", v < 0 ? \"-\" : \"\", a / unit, frac, name));\n  endfunction\n",
        );
        self.lit_items.push_str(&s);
        self.lits.insert(f.clone(), f.clone());
        f
    }

    /// A TIME read from a line (as GHDL reads it): a number with optional
    /// sign, decimals and exponent, whitespace, and a unit found by its
    /// first two letters (and its third, for a three-letter unit); the
    /// value is computed exactly in the primary unit. Leading zeros carry
    /// no weight, also right after the point (so "0.05 ns" is 0.5 ns, as
    /// in GHDL).
    fn time_read_fn(&mut self) -> String {
        let f = "vh_tio_rtime".to_string();
        if self.lits.contains_key(&f) {
            return f;
        }
        let units = match &self.d.types[self.d.std.time].kind {
            TypeKind::Physical(u) => u.clone(),
            _ => Vec::new(),
        };
        let mut s = String::from(
            r#"  function automatic longint vh_tio_rtime(vh_a_u8 s, output longint v);
    // States: 0 leading, 1 sign, 2 digits, 3 decimals, 4 exponent mark,
    // 5 exponent sign, 6 exponent, 7 blank before the unit, 8-10 unit
    // letters.
    int st, c;
    bit neg, eneg, hd;
    longint p, n, nd, ex, pos, un, w, res, used;
    byte unsigned u1, u2, u3;
    v = 0;
    st = 0;
    neg = 0;
    eneg = 0;
    nd = 0;
    ex = 0;
    pos = 0;
    u3 = 32;
    n = s.d.size();
    for (p = 0; p < n; p++) begin
      c = s.d[p];
      if (vh_tio_ws(c)) begin
        if (st == 1 || st == 4 || st == 5) return 0;
        if (st == 2 || st == 3 || st == 6) st = 7;
        else if (st == 8 || st == 9) break;
      end else if (c == 43 || c == 45) begin
        if (st == 0) begin
          neg = c == 45;
          st = 1;
        end else if (st == 4) begin
          eneg = c == 45;
          st = 5;
        end else return 0;
      end else if (vh_tio_dig(c)) begin
        if (st >= 4 && st <= 6) begin
          ex = ex * 10 + (c - 48);
          st = 6;
        end else if (st <= 2) begin
          if (nd > 0 || c != 48) nd++;
          st = 2;
        end else if (st != 3) return 0;
      end else if ((c >= 97 && c <= 122) || (c >= 65 && c <= 90)) begin
        if (st == 2 || st == 3) begin
          if (c == 101 || c == 69) st = 4;
          else return 0;
        end else if (st == 7) begin
          u1 = vh_tio_lc(c);
          st = 8;
        end else if (st == 8) begin
          u2 = vh_tio_lc(c);
          st = 9;
          pos = p;
        end else if (st == 9) begin
          u3 = vh_tio_lc(c);
          st = 10;
          break;
        end else return 0;
      end else if (c == 46) begin
        if (st == 2) st = 3;
        else break;
      end else break;
    end
    if (st != 9 && st != 10) return 0;
    if (eneg) ex = -ex;
    un = 0;
"#,
        );
        for (name, m) in &units {
            let b = name.as_bytes();
            if b.len() < 2 || b.len() > 3 {
                continue;
            }
            let third = if b.len() == 3 {
                format!(" && u3 == {}", b[2])
            } else {
                String::new()
            };
            let _ = writeln!(
                s,
                "    if (un == 0 && u1 == {} && u2 == {}{}) begin un = 64'sd{}; used = pos + {}; end",
                b[0],
                b[1],
                third,
                m,
                if b.len() == 3 { 2 } else { 1 }
            );
        }
        s.push_str(
            r#"    if (un == 0) return 0;
    // The weight of the first significant digit.
    nd = nd + ex - 1;
    w = un;
    if (nd < 0) for (longint i = 0; i < -nd; i++) w = w / 10;
    else for (longint i = 0; i < nd; i++) w = w * 10;
    res = 0;
    hd = 0;
    for (p = 0; p < n; p++) begin
      c = s.d[p];
      if (vh_tio_ws(c) || (c >= 97 && c <= 122) || (c >= 65 && c <= 90)) begin
        if (hd) break;
      end else if (c == 43 || c == 45) hd = 1;
      else if (vh_tio_dig(c)) begin
        if (c != 48 || res != 0) begin
          res = res + (c - 48) * w;
          w = w / 10;
        end
        hd = 1;
      end
    end
    v = neg ? -res : res;
    return used;
  endfunction
"#,
        );
        self.lit_items.push_str(&s);
        self.lits.insert(f.clone(), f.clone());
        f
    }

    /// The TEXTIO support code, when the design uses it.
    pub(super) fn textio_sv(&mut self) -> String {
        if self.textio {
            TEXTIO.to_string()
        } else {
            String::new()
        }
    }
}
