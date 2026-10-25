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
