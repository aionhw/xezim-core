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
    assert!(!p.contains("vh_ix"), "the part-select still calls vh_ix");
}

#[test]
fn record_array_past_the_pack_cap_stays_dynamic() {
    // 64 * (128 + 4) = 8448, past MAX_PK_BITS (2048).
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
  type arr_t is array (0 to 63) of rec_t;
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
        p.contains(".d["),
        "an array past the pack cap was packed"
    );
}
