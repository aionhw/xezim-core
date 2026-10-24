//! STD.TEXTIO output (IEEE 1076-2008 §16.4): WRITE of the standard types
//! into a LINE, and WRITELINE to the file OUTPUT, formatted as GHDL does.
//! A LINE is a handle into the STRING heap.

use std::fmt::Write as _;

use super::{Lw, sv_string};
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
  // WRITELINE (OUTPUT, L): the line, then L designates an empty line.
  function automatic void vh_tio_writeline(inout longint l);
    if (l == 0) $display("");
    else begin
      $display("%s", vh_sv(vh_heap_vh_a_u8[l]));
      vh_heap_vh_a_u8.delete(l);
    end
    l = vh_new_vh_a_u8(vh_str(""));
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
            "writeline" => {
                if !self.is_output(&args[0]) {
                    self.err(loc, "files other than OUTPUT are not supported yet");
                    return String::new();
                }
                let l = self.ex(&args[1]);
                format!("{}vh_tio_writeline({});\n", pad, l)
            }
            "write" | "swrite" if args.len() >= 2 && self.d.is_access(args[0].ty) => {
                let l = self.ex(&args[0]);
                let Some(s) = self.write_image(info, args, loc) else {
                    return String::new();
                };
                let (just, field) = if args.len() >= 4 {
                    (self.ex(&args[2]), self.ex(&args[3]))
                } else {
                    ("0".to_string(), "64'sd0".to_string())
                };
                format!("{}vh_tio_write({}, {}, {}, {});\n", pad, l, s, just, field)
            }
            _ => {
                self.err(
                    loc,
                    format!("'std.textio.{}' is not supported yet", name),
                );
                String::new()
            }
        }
    }

    /// Whether a file name denotes STD.TEXTIO.OUTPUT.
    fn is_output(&self, f: &HExpr) -> bool {
        matches!(&f.kind, HExprKind::Obj(o)
            if self.d.objects[*o].name == "output"
                && matches!(self.d.objects[*o].kind, ObjKind::File)
                && self.pkg_objs.contains(o))
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

    /// The TEXTIO support code, when the design uses it.
    pub(super) fn textio_sv(&mut self) -> String {
        if self.textio {
            TEXTIO.to_string()
        } else {
            String::new()
        }
    }
}
