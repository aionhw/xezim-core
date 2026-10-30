//! File objects and the operations of file types (IEEE 1076-2008 §5.5.2,
//! §6.4.2.5): FILE_OPEN, FILE_CLOSE, READ, WRITE, FLUSH and ENDFILE.
//! Values are stored as GHDL stores them, so each simulator reads the
//! other's files: the scalars of a value in order, least significant byte
//! first (enumerations 1 byte, INTEGER 4, larger integers, physical types
//! and REAL 8), an unconstrained array preceded by its length (4 bytes),
//! and a file of a composite type starting with a header naming the type.
//!
//! A file object holds 0 when it is closed, -1 for STD_OUTPUT (written
//! with $display, like reports), and otherwise an SV file descriptor
//! (STD_INPUT is -2: /dev/stdin, opened when first read).

use std::fmt::Write as _;

use super::{Lw, Repr, sv_string};
use crate::vhdl::sema::hir::*;

/// Support code of the file operations.
const FILES: &str = r#"
  // ---- files (§5.5.2) ---------------------------------------------------
  byte unsigned vh_fmode[int];
  // The header length of each open binary file: positions count after it;
  // and its name (FILE_TRUNCATE).
  int vh_fhdr[int];
  string vh_fname[int];
  // VHDL-2019 §5.5.2 FILE_STATE, FILE_MODE, FILE_POSITION, FILE_SIZE,
  // FILE_CANSEEK, FILE_SEEK (origins 0 begin, 1 current, 2 end).
  function automatic byte unsigned vh_fstate(int f);
    return f == 0 ? 1 : 0;
  endfunction
  function automatic byte unsigned vh_fmodeof(int f);
    if (f == 0) begin
      vh_ffail("file_mode called on a non-open file");
      return 0;
    end
    return vh_fmode[f];
  endfunction
  function automatic bit vh_fcanseek(int f);
    return f > 0 || f < -2;
  endfunction
  function automatic longint vh_fpos(int f);
    if (f == 0) vh_ffail("file_position called on a non-open file");
    if (!vh_fcanseek(f)) return 0;
    return $ftell(f) - vh_fhdr[f];
  endfunction
  function automatic longint vh_fsize(int f);
    longint p, n;
    int c;
    if (f == 0) vh_ffail("file_size called on a non-open file");
    if (!vh_fcanseek(f)) return 0;
    p = $ftell(f);
    c = $fseek(f, 0, 2);
    n = $ftell(f);
    c = $fseek(f, p, 0);
    return n - vh_fhdr[f];
  endfunction
  // VHDL-2019 FILE_TRUNCATE: the file's length becomes the position size
  // bytes from the origin; the file position stays (at most the end).
  function automatic void vh_ftrunc(int f, longint size, byte unsigned origin);
    longint p, n;
    int c;
    string r;
    if (!vh_fcanseek(f)) begin
      vh_ffail("file_truncate called on a file that cannot seek");
      return;
    end
    $fflush(f);
    p = $ftell(f);
    if (origin == 0) n = vh_fhdr[f] + size;
    else if (origin == 1) n = p + size;
    else n = vh_fsize(f) + vh_fhdr[f] + size;
    if (n < vh_fhdr[f]) n = vh_fhdr[f];
    r = $__vh_os("truncate", $sformatf("%s\n%0d", vh_fname[f], n));
    if (r != "ok") vh_ffail($sformatf("file_truncate failed: %s", r));
    if (p > n) c = $fseek(f, n, 0);
  endfunction
  function automatic void vh_fseekto(int f, longint off, byte unsigned origin);
    int c;
    if (!vh_fcanseek(f)) begin
      vh_ffail("file_seek called on a file that cannot seek");
      return;
    end
    if (origin == 0) c = $fseek(f, off + vh_fhdr[f], 0);
    else if (origin == 1) c = $fseek(f, off, 1);
    else c = $fseek(f, off, 2);
  endfunction
  // A failure GHDL reports without its "ghdl:error:" prefix.
  function automatic void vh_ffail(string msg);
    $display("%s", msg);
    $display("ghdl:error: simulation failed");
    $__vh_fail;
  endfunction
  // FILE_OPEN with an open kind READ_MODE, READ_WRITE_MODE, WRITE_MODE or
  // APPEND_MODE (0..3, as STD.STANDARD declares them): the status OPEN_OK,
  // STATUS_ERROR, NAME_ERROR or MODE_ERROR. A file of a composite type
  // starts with `hdr`.
  function automatic byte unsigned vh_fopen(inout int f, input string name, input byte unsigned kind, input string hdr);
    int fd, c;
    if (f != 0) return 1;
    if (name == "STD_INPUT" || name == "STD_OUTPUT") begin
      if (name == "STD_INPUT" ? kind != 0 : kind < 2) return 3;
      f = kind == 0 ? -2 : -1;
      vh_fmode[f] = kind;
      return 0;
    end
    c = -1;
    if (kind == 0) fd = $fopen(name, "rb");
    else if (kind == 1) fd = $fopen(name, "r+b");
    else if (kind == 2) fd = $fopen(name, "wb");
    else begin
      // Appending to a file that has values: no second header.
      fd = $fopen(name, "rb");
      if (fd != 0) begin
        c = $fgetc(fd);
        $fclose(fd);
      end
      fd = $fopen(name, "ab");
    end
    if (fd == 0) return 2;
    if (hdr != "") begin
      if (kind < 2) for (int i = 0; i < hdr.len(); i++) c = $fgetc(fd);
      else if (c == -1) $fwrite(fd, "%s", hdr);
    end
    f = fd;
    vh_fmode[fd] = kind;
    vh_fhdr[fd] = hdr.len();
    vh_fname[fd] = name;
    return 0;
  endfunction
  function automatic void vh_fopen_chk(inout int f, input string name, input byte unsigned kind, input string hdr);
    if (vh_fopen(f, name, kind, hdr) != 0) vh_fatal($sformatf("cannot open file \"%s\"", name));
  endfunction
  // The SV descriptor to read: STD_INPUT (-2) is opened, through its
  // device file, when first read.
  int vh_stdin;
  function automatic int vh_fd(int f);
    if (f != -2) return f;
    if (vh_stdin == 0) vh_stdin = $fopen("/dev/stdin", "rb");
    return vh_stdin;
  endfunction
  function automatic void vh_fclose(inout int f);
    if (f > 0 || f < -2) $fclose(f);
    if (f != 0) vh_fmode.delete(f);
    if (f != 0) vh_fhdr.delete(f);
    if (f != 0) vh_fname.delete(f);
    f = 0;
  endfunction
  // The file must be open for reading (rd) or for writing.
  function automatic void vh_fchk(int f, bit rd);
    if (f == 0) vh_ffail(rd ? "read called on a non-open file" : "write called on a non-open file");
    else if (rd && vh_fmode[f] > 1) vh_ffail("read called on a write-only file");
    else if (!rd && vh_fmode[f] == 0) vh_ffail("write called on a read-only file");
  endfunction
  function automatic bit vh_endfile(int f);
    int c;
    if (f == 0) begin
      vh_ffail("endfile with a non-opened file");
      return 1;
    end
    if (vh_fmode[f] > 1) return 1;
    c = $fgetc(vh_fd(f));
    if (c == -1) return 1;
    c = $ungetc(c, vh_fd(f));
    return 0;
  endfunction
  function automatic void vh_fflush(int f);
    if (f > 0 || f < -2) $fflush(f);
  endfunction
  // n bytes of x, least significant first.
  function automatic void vh_fput(int f, longint x, int n);
    for (int i = 0; i < n; i++) $fwrite(f, "%c", byte'(x >> (8 * i)));
  endfunction
  // n bytes, least significant first; sign-extended when sgn.
  function automatic longint vh_fget(int f, int n, bit sgn);
    longint x;
    int c;
    x = 0;
    for (int i = 0; i < n; i++) begin
      c = $fgetc(f);
      if (c == -1) begin
        vh_fatal("read_scalar failed");
        return 0;
      end
      x = x | (longint'(c & 255) << (8 * i));
    end
    if (sgn && n < 8 && ((x >> (8 * n - 1)) & 1) == 1) x = x | (-64'sd1 << (8 * n));
    return x;
  endfunction
  function automatic void vh_fskip(int f, longint n);
    int c;
    for (longint i = 0; i < n; i++) c = $fgetc(f);
  endfunction
"#;

impl<'a> Lw<'a> {
    /// A call of an operation of a file type.
    pub(super) fn file_call(
        &mut self,
        b: &Builtin,
        args: &[HExpr],
        ind: usize,
        loc: &Loc,
    ) -> String {
        let pad = " ".repeat(ind);
        self.files = true;
        match b {
            Builtin::FileOpen => {
                let (status, rest) = if args.len() == 4 {
                    (Some(&args[0]), &args[1..])
                } else {
                    (None, args)
                };
                let f = self.ex(&rest[0]);
                let name = self.ex(&rest[1]);
                let kind = self.ex(&rest[2]);
                let hdr = sv_string(&self.file_header(rest[0].ty));
                match status {
                    Some(s) => {
                        let v = format!("vh_fopen({}, vh_sv({}), {}, {})", f, name, kind, hdr);
                        self.assign_to(s, v, ind)
                    }
                    None => format!(
                        "{}vh_fopen_chk({}, vh_sv({}), {}, {});\n",
                        pad, f, name, kind, hdr
                    ),
                }
            }
            Builtin::FileClose => {
                let f = self.ex(&args[0]);
                format!("{}vh_fclose({});\n", pad, f)
            }
            Builtin::Flush => {
                let f = self.ex(&args[0]);
                format!("{}vh_fflush({});\n", pad, f)
            }
            Builtin::Write => {
                let f = self.ex(&args[0]);
                let v = if self.ndims(args[1].ty) >= 1 {
                    self.ex_fat(&args[1])
                } else {
                    self.ex(&args[1])
                };
                let mut out = format!("{}vh_fchk({}, 0);\n", pad, f);
                if self.is_text(args[0].ty) {
                    // A string written to a TEXT file: its characters.
                    let _ = writeln!(
                        out,
                        "{p}if ({f} == -1) $write(\"%s\", vh_sv({v})); else $fwrite({f}, \"%s\", vh_sv({v}));",
                        p = pad,
                        f = f,
                        v = v
                    );
                    return out;
                }
                let t = args[1].ty;
                // The value, once.
                let r = self.fat_repr(t, loc);
                let v = if matches!(r, Repr::Arr(..) | Repr::Rec(_)) {
                    self.tmp += 1;
                    let n = format!("vh_fv{}", self.tmp);
                    self.temps.push((n.clone(), r.sv()));
                    let _ = writeln!(out, "{}{} = {};", pad, n, v);
                    n
                } else {
                    v
                };
                if !self.d.constrained(self.file_elem(args[0].ty)) {
                    let _ = writeln!(out, "{}vh_fput({}, {}.d.size(), 4);", pad, f, v);
                }
                out.push_str(&self.file_put(t, &v, &f, ind, 0, loc));
                out
            }
            Builtin::Read => {
                if self.is_text(args[0].ty) {
                    self.err(
                        loc,
                        "READ of a TEXT file is not supported yet (use READLINE)",
                    );
                    return String::new();
                }
                let f = self.ex(&args[0]);
                let t = args[1].ty;
                let mut out = format!("{}vh_fchk({}, 1);\n", pad, f);
                // A packed target is read through a struct temporary.
                let tr = self.erepr(&args[1]);
                let fat = self.fat_repr(t, loc);
                let (v, back) = if matches!(tr, Repr::Pk(..)) {
                    self.tmp += 1;
                    let n = format!("vh_fv{}", self.tmp);
                    self.temps.push((n.clone(), fat.sv()));
                    let x = self.ex_as(&args[1], &fat);
                    let _ = writeln!(out, "{}{} = {};", pad, n, x);
                    let b = self.coerce(n.clone(), &fat, &tr, None, loc);
                    (n, Some(self.assign_to(&args[1], b, ind)))
                } else {
                    (self.ex(&args[1]), None)
                };
                let back = back.unwrap_or_default();
                if args.len() == 3 {
                    // An unconstrained array (§5.5.2): as many elements as
                    // fit, the rest skipped.
                    self.tmp += 1;
                    let n = format!("vh_fn{}", self.tmp);
                    let i = format!("vh_fj{}", self.tmp);
                    self.temps.push((n.clone(), "longint".into()));
                    self.temps.push((i.clone(), "longint".into()));
                    let Some(elem) = self.d.element_subtype(t) else {
                        return String::new();
                    };
                    let Some(size) = self.file_size(elem) else {
                        self.err(loc, "READ of elements of this type is not supported yet");
                        return String::new();
                    };
                    let _ = writeln!(out, "{}{} = vh_fget({}, 4, 0);", pad, n, f);
                    let _ = writeln!(
                        out,
                        "{p}for ({i} = 0; {i} < {n}; {i}++) begin\n{p}  if ({i} < {v}.d.size()) begin",
                        p = pad,
                        i = i,
                        n = n,
                        v = v
                    );
                    out.push_str(&self.file_get(
                        elem,
                        &format!("{}.d[{}]", v, i),
                        &f,
                        ind + 4,
                        1,
                        loc,
                    ));
                    let _ = writeln!(
                        out,
                        "{p}  end else vh_fskip({f}, {s});\n{p}end",
                        p = pad,
                        f = f,
                        s = size
                    );
                    // LENGTH: the elements stored in VALUE (as GHDL sets it).
                    let stored = format!("({n} < {v}.d.size() ? {n} : {v}.d.size())", n = n, v = v);
                    out.push_str(&back);
                    out.push_str(&self.assign_to(&args[2], stored, ind));
                    return out;
                }
                out.push_str(&self.file_get(t, &v, &f, ind, 0, loc));
                out.push_str(&back);
                out
            }
            _ => String::new(),
        }
    }

    /// ENDFILE (§5.5.2).
    pub(super) fn endfile(&mut self, f: &HExpr) -> String {
        self.files = true;
        let f = self.ex(f);
        format!("byte'(vh_endfile({}))", f)
    }

    /// Opening a file object declared with file open information
    /// (§14.4.2.5), at elaboration.
    pub(super) fn file_decl_open(&mut self, o: ObjId, ind: usize) -> String {
        let Some((name, kind)) = self.d.file_opens.get(&o).cloned() else {
            return String::new();
        };
        self.files = true;
        let f = self.obj_name(o);
        let n = self.ex(&name);
        let k = self.ex(&kind);
        let hdr = sv_string(&self.file_header(self.d.objects[o].ty));
        let pre = self.flush_pre(ind);
        format!(
            "{}{}vh_fopen_chk({}, vh_sv({}), {}, {});\n",
            pre,
            " ".repeat(ind),
            f,
            n,
            k,
            hdr
        )
    }

    /// Whether a file type is STD.TEXTIO.TEXT.
    pub(super) fn is_text(&self, ft: TypeId) -> bool {
        self.d.std.text == Some(self.d.base(ft))
    }

    fn file_elem(&self, ft: TypeId) -> TypeId {
        match self.d.types[self.d.base(ft)].kind {
            TypeKind::File(e) => e,
            _ => ft,
        }
    }

    /// The header GHDL starts a file of a composite type with.
    fn file_header(&mut self, ft: TypeId) -> String {
        if self.is_text(ft) {
            return String::new();
        }
        let e = self.file_elem(ft);
        if self.d.is_scalar(e) {
            return String::new();
        }
        let loc = Loc {
            file: 0,
            span: 0..0,
        };
        format!("#GHDL-BINARY-FILE-0.0\n{}.", self.file_sig(e, &loc))
    }

    /// GHDL's signature of a type: `b` BOOLEAN, `e` another enumeration,
    /// `i`/`I` 32/64-bit integer, `P` physical, `F` real, `[...]` array,
    /// `<...>` record.
    fn file_sig(&mut self, t: TypeId, loc: &Loc) -> String {
        let b = self.d.base(t);
        match &self.d.types[b].kind {
            TypeKind::Enum(lits) => {
                if b == self.d.std.boolean {
                    "b".into()
                } else if lits.len() <= 256 {
                    "e".into()
                } else {
                    "E".into()
                }
            }
            TypeKind::Integer => match self.repr(b, loc) {
                Repr::I32 => "i".into(),
                _ => "I".into(),
            },
            TypeKind::Physical(_) => "P".into(),
            TypeKind::Real => "F".into(),
            TypeKind::Array { elem, .. } => {
                let e = *elem;
                format!("[{}]", self.file_sig(e, loc))
            }
            TypeKind::Record(_) => {
                let fields = self.d.record_fields(t);
                let mut s = String::from("<");
                for (_, ft) in fields {
                    s.push_str(&self.file_sig(ft, loc));
                }
                s.push('>');
                s
            }
            _ => String::new(),
        }
    }

    /// The bytes of a value of a constrained subtype, when static.
    fn file_size(&mut self, t: TypeId) -> Option<i64> {
        let loc = Loc {
            file: 0,
            span: 0..0,
        };
        let b = self.d.base(t);
        Some(match &self.d.types[b].kind {
            TypeKind::Enum(lits) => {
                if lits.len() <= 256 {
                    1
                } else {
                    4
                }
            }
            TypeKind::Integer => match self.repr(b, &loc) {
                Repr::I32 => 4,
                _ => 8,
            },
            TypeKind::Physical(_) | TypeKind::Real => 8,
            TypeKind::Array { .. } => {
                let mut n = 1;
                for k in 0..self.ndims(t) {
                    n *= self.static_dim(t, k)?.length();
                }
                n * self.file_size(self.d.element_subtype(t)?)?
            }
            TypeKind::Record(_) => {
                let mut n = 0;
                for (_, ft) in self.d.record_fields(t) {
                    n += self.file_size(ft)?;
                }
                n
            }
            _ => return None,
        })
    }

    /// Statements writing value `v` of subtype `t` to file `f`.
    fn file_put(&mut self, t: TypeId, v: &str, f: &str, ind: usize, k: usize, loc: &Loc) -> String {
        let pad = " ".repeat(ind);
        let b = self.d.base(t);
        match self.d.types[b].kind.clone() {
            TypeKind::Enum(_) | TypeKind::Integer | TypeKind::Physical(_) => {
                let n = self.file_size(b).unwrap_or(8);
                format!("{}vh_fput({}, {}, {});\n", pad, f, v, n)
            }
            TypeKind::Real => format!("{}vh_fput({}, $realtobits({}), 8);\n", pad, f, v),
            TypeKind::Array { .. } => self.file_arr(t, 0, v, f, ind, k, loc, true),
            TypeKind::Record(_) => {
                let mut out = String::new();
                for (i, ft) in self.field_storage(t).into_iter().enumerate() {
                    out.push_str(&self.file_put(ft, &format!("{}.f{}", v, i), f, ind, k, loc));
                }
                out
            }
            _ => {
                self.err(loc, "a value of this type cannot be written to a file");
                String::new()
            }
        }
    }

    /// Statements reading a value of subtype `t` from file `f` into `lv`.
    fn file_get(
        &mut self,
        t: TypeId,
        lv: &str,
        f: &str,
        ind: usize,
        k: usize,
        loc: &Loc,
    ) -> String {
        let pad = " ".repeat(ind);
        let b = self.d.base(t);
        match self.d.types[b].kind.clone() {
            TypeKind::Enum(_) => {
                let n = self.file_size(b).unwrap_or(1);
                format!("{}{} = vh_fget({}, {}, 0);\n", pad, lv, f, n)
            }
            TypeKind::Integer | TypeKind::Physical(_) => {
                let n = self.file_size(b).unwrap_or(8);
                format!("{}{} = vh_fget({}, {}, 1);\n", pad, lv, f, n)
            }
            TypeKind::Real => format!("{}{} = $bitstoreal(vh_fget({}, 8, 0));\n", pad, lv, f),
            TypeKind::Array { .. } => self.file_arr(t, 0, lv, f, ind, k, loc, false),
            TypeKind::Record(_) => {
                let mut out = String::new();
                for (i, ft) in self.field_storage(t).into_iter().enumerate() {
                    out.push_str(&self.file_get(ft, &format!("{}.f{}", lv, i), f, ind, k, loc));
                }
                out
            }
            _ => {
                self.err(loc, "a value of this type cannot be read from a file");
                String::new()
            }
        }
    }

    /// The elements of dimension `dim` onwards of array `v`, in order.
    #[allow(clippy::too_many_arguments)]
    fn file_arr(
        &mut self,
        t: TypeId,
        dim: usize,
        v: &str,
        f: &str,
        ind: usize,
        k: usize,
        loc: &Loc,
        put: bool,
    ) -> String {
        let pad = " ".repeat(ind);
        let i = format!("vh_fi{}", k);
        // A packed array: its elements by position.
        let pk = match self.repr(t, loc) {
            Repr::Pk(w, n) => Some((w, n)),
            _ => None,
        };
        let e = match pk {
            Some((w, n)) => Lw::pk_sel(v, w, n, &i),
            None => format!("{}.d[{}]", v, i),
        };
        let count = match pk {
            Some((_, n)) => n.to_string(),
            None => format!("{}.d.size()", v),
        };
        let inner = if dim + 1 < self.ndims(t) {
            self.file_arr(t, dim + 1, &e, f, ind + 2, k + 1, loc, put)
        } else {
            let Some(et) = self.d.element_subtype(t) else {
                return String::new();
            };
            if put {
                self.file_put(et, &e, f, ind + 2, k + 1, loc)
            } else {
                self.file_get(et, &e, f, ind + 2, k + 1, loc)
            }
        };
        format!(
            "{p}for (longint {i} = 0; {i} < {count}; {i}++) begin\n{inner}{p}end\n",
            p = pad,
            i = i,
            count = count,
            inner = inner
        )
    }

    /// The file support code, when the design has files.
    pub(super) fn files_sv(&self) -> String {
        if self.files {
            FILES.to_string()
        } else {
            String::new()
        }
    }
}
