//! A `std_logic_vector` longer than 512 elements is a packed vector, and a
//! whole packed word under an array is copied in one assignment.

use xezim_core::vhdl;

fn lowered(src: &str) -> String {
    vhdl::lower_design(&[("work", "t.vhd", src.as_bytes())])
        .unwrap_or_else(|e| panic!("{}", e.join("\n")))
}

fn slv(left: i64) -> String {
    format!(
        r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  signal clk : std_logic := '0';
  signal q : std_logic_vector({left} downto 0) := (others => '0');
begin
  clk <= not clk after 5 ns;
  process (clk) begin
    if rising_edge(clk) then
      q <= not q;
    end if;
  end process;
end architecture;
"#,
        left = left
    )
}

/// 2048 elements is 8192 bits. The old 2048-bit cap left this as `vh_a_u8`.
#[test]
fn wide_std_logic_vector_is_packed() {
    let sv = lowered(&slv(2047));
    assert!(
        sv.contains("bit [8191:0]"),
        "2048-element std_logic_vector was not packed"
    );
    assert!(
        sv.contains("vh_txw_pk4_2048"),
        "driver queue is not the packed form"
    );
}

/// 513 elements is 2052 bits, one element past the old cap.
#[test]
fn just_past_512_elements_is_packed() {
    let sv = lowered(&slv(512));
    assert!(
        sv.contains("bit [2051:0]"),
        "513-element vector was not packed"
    );
}

/// 4096 elements is the new cap (16384 bits). One more stays a dynamic array.
#[test]
fn cap_is_4096_std_logic_elements() {
    let at = lowered(&slv(4095));
    assert!(
        at.contains("bit [16383:0]"),
        "4096-element vector was not packed"
    );
    let over = lowered(&slv(4096));
    assert!(
        !over.contains("bit [16387:0]"),
        "4097-element vector was packed past the cap"
    );
    assert!(
        over.contains("vh_txw_vh_a_u8"),
        "over-cap vector did not keep the dynamic-array driver"
    );
}

/// An array of records of 32-bit vectors: a driver of every element of a
/// word assigns that word once, not a nibble at a time.
#[test]
fn record_array_word_is_one_assignment() {
    let sv = lowered(
        r#"
library ieee;
use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type f_t is record
    x : std_logic_vector(31 downto 0);
    y : std_logic;
  end record;
  type arr_t is array (0 to 3) of f_t;
  signal clk : std_logic := '0';
  signal r : arr_t := (others => (x => (others => '0'), y => '0'));
begin
  clk <= not clk after 5 ns;
  process (clk) begin
    if rising_edge(clk) then
      for i in 0 to 3 loop
        r(i).x <= not r(i).x;
        r(i).y <= not r(i).y;
      end loop;
    end if;
  end process;
end architecture;
"#,
    );
    assert!(
        sv.contains("bit [127:0]"),
        "the 32-bit field was not packed"
    );
    assert!(
        !sv.contains("+: 4] = vh_dv"),
        "the update still copies the word a nibble at a time:\n{sv}"
    );
    assert!(
        sv.contains(".d[k]") && sv.contains("= vh_dv"),
        "no whole-word copy of the array element"
    );
    assert!(
        sv.contains("vh_pww"),
        "a whole packed element is still stored a nibble at a time"
    );
}
