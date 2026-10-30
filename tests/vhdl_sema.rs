//! VHDL semantic analysis: designs that must analyse cleanly, and located
//! errors for ones that must not.

use xezim_core::vhdl;

fn ok(src: &str) {
    let errs = vhdl::check_design(&[("work", "t.vhd", src.as_bytes())]);
    assert!(errs.is_empty(), "{}", errs.join("\n"));
}

/// Package STANDARD and a process using its types, attributes and
/// predefined operators (§16.3, §9.2).
#[test]
fn std_only_process() {
    ok(r#"
entity t is end entity;
architecture a of t is
  signal s : integer := 0;
  type state is (idle, run, done);
  subtype small is integer range 0 to 7;
  constant k : time := 10 ns;
begin
  process
    variable v : small := 3;
    variable st : state := idle;
    variable r : real := 1.5;
    variable bv : bit_vector(7 downto 0) := x"A5";
  begin
    report "v=" & integer'image(v) & " r=" & real'image(r * 2.0);
    v := v + 1;
    st := state'succ(st);
    if st = run and v > 2 then
      s <= s + 1 after 1 ns;
    end if;
    for i in bv'range loop
      bv(i) := not bv(i);
    end loop;
    wait for k;
    assert s = 1 report "bad" severity error;
    wait;
  end process;
end architecture;
"#);
}

/// IEEE STD_LOGIC_1164 and NUMERIC_STD (vendored sources) analyse, and a
/// design using them resolves overloaded operators and conversions.
#[test]
fn ieee_numeric_std() {
    ok(r#"
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity t is end entity;
architecture a of t is
  signal clk : std_logic := '0';
  signal cnt : unsigned(7 downto 0) := (others => '0');
begin
  clk <= not clk after 5 ns;
  process (clk)
  begin
    if rising_edge(clk) then
      cnt <= cnt + 1;
      report "cnt=" & integer'image(to_integer(cnt));
    end if;
  end process;
end architecture;
"#);
}

/// STD.TEXTIO and STD.ENV.
#[test]
fn textio_and_env() {
    ok(r#"
use std.textio.all;
use std.env.all;
entity t is end entity;
architecture a of t is
begin
  process
    variable l : line;
  begin
    write(l, string'("hello"));
    write(l, 42);
    writeline(output, l);
    finish;
  end process;
end architecture;
"#);
}

/// `"…" & c & "…"` with a CHARACTER `c` (§9.2.5) and a range attribute as
/// an aggregate choice (§9.3.3.3).
#[test]
fn concat_char_and_range_choice() {
    ok(r#"
entity t is end entity;
architecture a of t is
begin
  process
    variable c : character := 'q';
    variable v : bit_vector(3 downto 0);
  begin
    report "char '" & c & "' read";
    v := (v'range => '1');
    wait;
  end process;
end architecture;
"#);
}

/// Located errors: unknown names and type mismatches.
#[test]
fn errors_are_located() {
    let errs = vhdl::check_design(&[(
        "work",
        "bad.vhd",
        b"entity t is end entity;\narchitecture a of t is\nbegin\n  process\n    variable i : integer;\n  begin\n    i := undefined_thing;\n    i := 'x';\n    wait;\n  end process;\nend architecture;\n",
    )]);
    let all = errs.join("\n");
    assert!(
        all.contains("bad.vhd:7:10: error: VHDL: unknown name 'undefined_thing'"),
        "{}",
        all
    );
    assert!(
        all.contains("bad.vhd:8:10: error: VHDL: no enumeration literal 'x' of the expected type"),
        "{}",
        all
    );
}

/// External corpus (not run by default): analyse each `.vhd` under
/// `$XEZIM_VHDL_CORPUS` on its own and print the first error per file.
#[test]
#[ignore]
fn external_corpus_analyses() {
    let Some(dir) = std::env::var_os("XEZIM_VHDL_CORPUS") else {
        return;
    };
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| vhdl::is_vhdl_path(&p.to_string_lossy()))
        .collect();
    files.sort();
    let (mut ok, mut bad) = (0, 0);
    for p in &files {
        let text = std::fs::read(p).unwrap();
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        let errs = vhdl::check_design(&[("work", &name, &text)]);
        if errs.is_empty() {
            ok += 1;
        } else {
            bad += 1;
            println!("FAIL {}", errs[0].lines().next().unwrap_or(""));
        }
    }
    println!("analysed ok={} failed={}", ok, bad);
}

/// `"abc" < "abd"`: both STRING and BIT_VECTOR fit — ambiguous, as GHDL
/// reports (§12.5).
#[test]
fn ambiguous_string_literal_operator() {
    let errs = vhdl::check_design(&[(
        "work",
        "amb.vhd",
        b"entity t is end entity;\narchitecture a of t is\nbegin\n  process begin\n    report boolean'image(\"abc\" < \"abd\");\n    wait;\n  end process;\nend architecture;\n",
    )]);
    let all = errs.join("\n");
    assert!(
        all.contains("amb.vhd:5:26: error: VHDL: ambiguous call of \"<\""),
        "{}",
        all
    );
}

/// Static expressions that call functions (§9.4.1, §14.4.2): constants of
/// package functions in generate conditions, for-generate ranges and
/// generic actuals, as NEORV32 computes its configuration. The function
/// bodies are in the package body, analysed when first needed.
#[test]
fn static_function_calls() {
    let errs = vhdl::check_design(&[
        (
            "work",
            "p.vhd",
            br#"
package p is
  function sel_f(c : boolean; a, b : natural) return natural;
  function log2_f(n : natural) return natural;
  function ones_f(n : natural) return bit_vector;
end package;
package body p is
  function sel_f(c : boolean; a, b : natural) return natural is
  begin
    if c then return a; else return b; end if;
  end function;
  function log2_f(n : natural) return natural is
    variable r : natural := 0;
  begin
    while 2 ** r < n loop
      r := r + 1;
    end loop;
    return r;
  end function;
  function ones_f(n : natural) return bit_vector is
    variable v : bit_vector(n - 1 downto 0) := (others => '0');
  begin
    for i in integer range 0 to n - 1 loop
      if i mod 2 = 0 then v(i) := '1'; end if;
    end loop;
    return v;
  end function;
end package body;
"#,
        ),
        (
            "work",
            "t.vhd",
            br#"
use work.p.all;
entity leaf is
  generic (w : positive);
  port (x : in bit_vector(w - 1 downto 0));
end entity;
architecture a of leaf is
begin
end architecture;
use work.p.all;
entity t is
  generic (dual : boolean := true; size : natural := 1000);
end entity;
architecture a of t is
  constant n_c : natural := sel_f(dual, 2, 1);
  constant w_c : natural := log2_f(size);
  constant pat_c : bit_vector := ones_f(4);
  signal s : bit_vector(w_c - 1 downto 0);
begin
  two : if n_c = 2 generate
    u : entity work.leaf generic map (w => w_c) port map (x => s);
  end generate;
  per : for i in 0 to n_c - 1 generate
    assert pat_c(i * 2) = '1';
  end generate;
end architecture;
"#,
        ),
    ]);
    assert!(errs.is_empty(), "{}", errs.join("\n"));
}

/// The Synopsys packages in library IEEE (as GHDL `-fsynopsys` and Questa
/// provide them).
#[test]
fn synopsys_packages() {
    ok(r#"
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_misc.all;
entity t is end entity;
architecture a of t is
  signal x, y : std_logic_vector(7 downto 0);
  signal z : std_logic;
begin
  y <= x + 1;
  z <= or_reduce(x) when x > 5 else '0';
end architecture;
"#);
}

/// A generic without a default needs an actual (§6.5.6.2), in GHDL's words.
#[test]
fn missing_generic_actual() {
    let errs = vhdl::check_design(&[(
        "work",
        "g.vhd",
        b"entity c is\n  generic (n : integer);\nend entity;\narchitecture a of c is\nbegin\nend architecture;\nentity t is end entity;\narchitecture a of t is\nbegin\n  u : entity work.c;\nend architecture;\n",
    )]);
    let all = errs.join("\n");
    assert!(
        all.contains("g.vhd:10:3: error: VHDL: no actual for constant interface \"n\""),
        "{}",
        all
    );
}

/// VHDL-2019 §5.6.2, §5.6.4 generic protected types: instances analyse
/// with their generics bound (previously a "not supported yet" error, the
/// last of the VHDL-2019 forms the parser accepted that the analysis did
/// not handle; xezim tests/vhdl/designs19/protgen19 runs one).
#[test]
fn vhdl2019_generic_protected_types() {
    let src = "package p is\n  type pt is protected\n    generic (n : natural);\n    impure function get return natural;\n  end protected;\n  type p3 is new pt generic map (n => 3);\nend package;\npackage body p is\n  type pt is protected body\n    impure function get return natural is\n    begin\n      return n;\n    end function;\n  end protected body;\nend package body;\nuse work.p.all;\nentity e is end entity;\narchitecture a of e is\n  shared variable v : p3;\nbegin\nend architecture;\n";
    let errs = vhdl::check_design_std(&[("work", "t19.vhd", src.as_bytes())], vhdl::VhdlStd::V2019);
    assert!(errs.is_empty(), "{}", errs.join("\n"));
}

/// The VHDL-2019 forms are syntax errors in VHDL-2008.
#[test]
fn vhdl2019_forms_rejected_in_2008() {
    for src in [
        "package p is\n  function f(x : integer) return integer;\nend package;\npackage body p is\n  function f(x : integer) return integer is\n  begin\n    return 1 when x > 0 else 0;\n  end function;\nend package body;\n",
        "entity e is\n  generic (type t is (<>));\nend entity;\n",
        "entity e is end entity;\narchitecture a of e is\nbegin\n  process\n  begin\n    block begin null; end block;\n    wait;\n  end process;\nend architecture;\n",
    ] {
        let errs = vhdl::check_design(&[("work", "t08.vhd", src.as_bytes())]);
        assert!(!errs.is_empty(), "{src}");
    }
}

/// VHDL-2019 §6.5.2 mode views: every element of the record has exactly one
/// mode, the view's subtype is a record type, views apply to ports and
/// procedures' signal parameters, an array view names its array subtype,
/// and the port's subtype is of the view's type. Each is a located error.
#[test]
fn mode_view_errors() {
    let pkg = |view: &str, rest: &str| {
        format!(
            "package p is\n  type r_t is record\n    a, b : bit;\n  end record;\n  type v_t is array (0 to 1) of r_t;\n{view}{rest}end package;\nuse work.p.all;\nentity e is end entity;\narchitecture a of e is\nbegin\nend architecture;\n"
        )
    };
    let good = "  view v of r_t is\n    a : in;\n    b : out;\n  end view;\n";
    for (src, at, what) in [
        (
            pkg("  view v of r_t is\n    a : in;\n  end view;\n", ""),
            "t19.vhd:6:8:",
            "element 'b' has no mode in the view",
        ),
        (
            pkg("  view v of r_t is\n    a, b : in;\n    c : out;\n  end view;\n", ""),
            "t19.vhd:8:5:",
            "'c' is not an element",
        ),
        (
            pkg("  view v of r_t is\n    a, b : in;\n    a : out;\n  end view;\n", ""),
            "t19.vhd:8:5:",
            "has a mode in the view already",
        ),
        (
            pkg("  view w of bit is\n    a : in;\n  end view;\n", ""),
            "t19.vhd:6:13:",
            "must be a record type",
        ),
        (
            pkg(good, "  function f(signal x : view v) return bit;\n"),
            "t19.vhd:10:14:",
            "ports and signal parameters of procedures only",
        ),
        (
            pkg(good, "  procedure q(signal x : view (v));\n"),
            "t19.vhd:10:15:",
            "array mode view needs the subtype",
        ),
        (
            pkg(good, "  procedure q(signal x : view v of v_t);\n"),
            "t19.vhd:10:36:",
            "not of the type of the mode view",
        ),
    ] {
        let errs =
            vhdl::check_design_std(&[("work", "t19.vhd", src.as_bytes())], vhdl::VhdlStd::V2019);
        assert!(
            errs.iter().any(|e| e.starts_with(at) && e.contains(what)),
            "{at} {what}:\n{}\n{src}",
            errs.join("\n")
        );
    }
    let ok = pkg(good, "  procedure q(signal x : view v; signal y : view (v'converse) of v_t);\n");
    let errs = vhdl::check_design_std(&[("work", "t19.vhd", ok.as_bytes())], vhdl::VhdlStd::V2019);
    assert!(errs.is_empty(), "{}", errs.join("\n"));
}

/// VHDL-2019 §6.5.3: the actual of a generic type with a class is of that
/// class, for generic subprograms and entities (a located error at the
/// generic type otherwise).
#[test]
fn generic_type_class_of_actual() {
    let src = |class: &str, actual: &str| {
        format!(
            "entity e is\n  generic (type t is {class});\nend entity;\narchitecture a of e is\nbegin\nend architecture;\nentity top is end entity;\narchitecture a of top is\n  function f generic (type u is {class}) parameter (x : u) return u is\n  begin\n    return x;\n  end function;\n  function g is new f generic map (u => {actual});\nbegin\n  i : entity work.e generic map (t => {actual});\nend architecture;\n"
        )
    };
    for (class, actual, ok) in [
        ("(<>)", "integer", true),
        ("(<>)", "character", true),
        ("(<>)", "real", false),
        ("range <>", "natural", true),
        ("range <>", "bit", false),
        ("range <> . <>", "real", true),
        ("units <>", "time", true),
        ("units <>", "integer", false),
        ("<>", "time", true),
        ("<>", "bit_vector", false),
        ("private", "string", true),
        ("array (natural range <>) of type is private", "bit_vector", true),
        ("array (natural range <>) of type is private", "integer", false),
        ("access type is private", "integer", false),
    ] {
        let s = src(class, actual);
        let errs = vhdl::check_design_std(&[("work", "c19.vhd", s.as_bytes())], vhdl::VhdlStd::V2019);
        if ok {
            assert!(errs.is_empty(), "{class} / {actual}:\n{}", errs.join("\n"));
        } else {
            assert!(
                errs.iter().any(|e| e.starts_with("c19.vhd:2:") && e.contains("the actual of generic type 't'"))
                    && errs.iter().any(|e| e.starts_with("c19.vhd:9:") && e.contains("the actual of generic type 'u'")),
                "{class} / {actual}:\n{}",
                errs.join("\n")
            );
        }
    }
}
