//! A static array of records whose fields pack is one packed vector.
//! A field assign is one part-select of that vector, not a dynamic-array
//! element write.

use xezim_core::vhdl;

fn lowered(src: &str) -> String {
    vhdl::lower_design(&[("work", "t.vhd", src.as_bytes())])
        .unwrap_or_else(|e| panic!("{}", e.join("\n")))
}

const REC: &str = r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type rec_t is record
    x : std_logic_vector(31 downto 0);
    y : std_logic;
  end record;
  type arr_t is array (0 to 7) of rec_t;
  signal r : arr_t;
  signal clk : std_logic;
begin
  process (clk) is
  begin
    if rising_edge(clk) then
      r(0).x <= not r(0).x;
      r(0).y <= not r(0).y;
      r(0).x(0) <= '1';
    end if;
  end process;
end architecture;
"#;

fn process0(sv: &str) -> &str {
    let start = sv
        .find("function automatic void vh_run0()")
        .expect("process");
    let end = sv[start..].find("\n  endfunction").expect("process end");
    &sv[start..start + end]
}

#[test]
fn static_record_array_field_is_a_part_select() {
    let sv = lowered(REC);
    let p = process0(&sv);
    for needle in ["[928 +: 128]", "[924 +: 4]", "(928) +: 4] = ", "vh_pw"] {
        assert!(p.contains(needle), "missing {needle}");
    }
    assert!(sv.contains("bit [1055:0] vh_s"), "not one 1056-bit vector");
    assert!(!p.contains(".d["), "the process still indexes a dynamic array");
    assert!(!p.contains(".f"), "the process still selects a record field");
}

#[test]
fn loop_index_is_arithmetic() {
    let sv = lowered(
        r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type rec_t is record
    x : std_logic_vector(31 downto 0);
    y : std_logic;
  end record;
  type arr_t is array (0 to 7) of rec_t;
  signal r : arr_t;
  signal clk : std_logic;
begin
  process (clk) is
  begin
    if rising_edge(clk) then
      for i in 0 to 7 loop
        r(i).x <= not r(i).x;
        r(i).y <= not r(i).y;
      end loop;
    end if;
  end process;
end architecture;
"#,
    );
    let p = process0(&sv);
    assert!(p.contains("132 * (7 - ("), "the element offset is not arithmetic");
    assert!(
        p.contains("vh_ix"),
        "a variable index dropped the bounds check"
    );
}

#[test]
fn record_array_past_the_pack_cap_stays_dynamic() {
    // 128 * (128 + 4) = 16896, past MAX_PK_BITS (16384).
    let sv = lowered(
        r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type rec_t is record
    x : std_logic_vector(31 downto 0);
    y : std_logic;
  end record;
  type arr_t is array (0 to 127) of rec_t;
  signal r : arr_t;
  signal clk : std_logic;
begin
  process (clk) is
  begin
    if rising_edge(clk) then
      r(0).x <= not r(0).x;
    end if;
  end process;
end architecture;
"#,
    );
    let p = process0(&sv);
    assert!(
        !sv.contains("bit [16895:0]"),
        "an array past the pack cap was packed"
    );
    assert!(
        p.contains("vh_pww"),
        "an array past the pack cap did not keep the word driver"
    );
}

/// Two processes driving different elements stay per-element drivers.
#[test]
fn two_processes_keep_the_per_element_form() {
    let sv = lowered(
        r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type rec is record
    v : std_logic_vector(7 downto 0);
    b : std_logic;
  end record;
  type rarr is array (0 to 3) of rec;
  signal clk : std_logic := '0';
  signal m : rarr;
begin
  p0 : process (clk) begin
    if rising_edge(clk) then m(0).v <= x"01"; end if;
  end process;
  p1 : process (clk) begin
    if falling_edge(clk) then m(2).v <= x"02"; end if;
  end process;
end architecture;
"#,
    );
    assert!(
        !sv.contains("bit [143:0]"),
        "two drivers were packed into one vector"
    );
    // Zero-delay field writes stay on the word driver from the merged
    // array-element change, not one write of the whole vector.
    assert!(
        process0(&sv).contains("vh_pww"),
        "a second driver did not keep the word driver"
    );
}

/// A delayed part assignment keeps its own waveform.
#[test]
fn delayed_part_assignment_is_not_packed() {
    let sv = lowered(
        r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type rec is record
    v : std_logic_vector(7 downto 0);
    b : std_logic;
  end record;
  type rarr is array (0 to 3) of rec;
  signal dl : rarr;
begin
  process begin
    dl(0).v <= x"A0" after 10 ns;
    dl(1).v <= x"B1" after 5 ns;
    wait;
  end process;
end architecture;
"#,
    );
    assert!(
        !sv.contains("bit [143:0]"),
        "a delayed part assignment was packed into one vector"
    );
    assert!(
        sv.contains("64'sd10000000") && sv.contains("vh_drs_"),
        "the delayed part assignment lost its own transaction"
    );
}

/// An aggregate initial value keeps the record array.
#[test]
fn aggregate_initial_value_is_not_packed() {
    let sv = lowered(
        r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type rec is record
    v : std_logic_vector(7 downto 0);
    b : std_logic;
  end record;
  type rarr is array (2 downto -1) of rec;
  constant rinit : rec := (v => x"3C", b => '1');
  signal ri : rarr := (others => rinit);
begin
  process begin
    wait;
  end process;
end architecture;
"#,
    );
    assert!(
        !sv.contains("bit [143:0]"),
        "an aggregate initial value was packed"
    );
}

const PROCEDURE_DELAYED_FIELDS: &str = r#"
entity t is end;
architecture a of t is
  type rec_t is record
    a : bit;
    b : bit;
  end record;
  type arr_t is array (0 to 1) of rec_t;
  signal r : arr_t;
  procedure put(signal a : out bit; signal b : out bit) is
  begin
    a <= '1' after 2 ns;
    b <= '1' after 1 ns;
  end procedure;
begin
  process begin
    put(r(0).a, r(0).b);
    wait for 3 ns;
    assert r(0).a = '1' and r(0).b = '1'
      report "delayed procedure fields lost a transaction" severity failure;
    report "PASS procedure delayed fields" severity note;
    wait;
  end process;
end architecture;
"#;

/// §14.7.2 / §10.5.2.2: signal formals can hide independently timed field
/// writes; passing scalar fields must retain the per-element drivers.
#[test]
fn procedure_signal_fields_keep_the_per_element_form() {
    let sv = lowered(PROCEDURE_DELAYED_FIELDS);
    assert!(
        !sv.contains("bit [3:0] vh_s"),
        "procedure signal actuals bypassed the packing gate"
    );
    assert!(sv.contains("vh_drs_"), "the delayed transactions were lost");
}

const NESTED_INITIAL_VALUE: &str = r#"
entity t is end;
architecture a of t is
  type rec_t is record
    a : bit;
    b : bit;
  end record;
  type arr_t is array (0 to 1) of rec_t;
  type outer_t is record
    child : arr_t;
  end record;
  constant initial_value : outer_t :=
    (child => (others => (a => '1', b => '0')));
  signal holder : outer_t := initial_value;
  signal r : arr_t;
begin
  process begin
    r(0).a <= '1';
    wait for 1 ns;
    assert holder.child(0).a = '1' and holder.child(0).b = '0'
       and holder.child(1).a = '1' and holder.child(1).b = '0'
      report "nested initialized array lost its record fields" severity failure;
    report "PASS nested initial value" severity note;
    wait;
  end process;
end architecture;
"#;

/// §14.4.2.5: admitting one direct signal must not change the same base
/// type's initialized values when it is stored inside another record.
#[test]
fn nested_record_array_type_reuse_is_not_packed() {
    let sv = lowered(NESTED_INITIAL_VALUE);
    assert!(
        !sv.contains("bit [3:0] vh_s"),
        "a nested use of the admitted base type was packed"
    );
}
