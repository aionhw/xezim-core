// Runtime support for SystemC designs lowered to SystemVerilog
// (see systemc/mod.rs). Parsed once per design and imported by every
// generated module as `import sc_rt::*;`. Names carry a `scrt_` prefix (or
// are the TLM-2.0 constant names) so they cannot collide with the user's.
package sc_rt;
  timeunit 1ps;
  timeprecision 1ps;

  // ---- kernel control (IEEE 1666-2023 §4.3–§4.5) ------------------------
  // Processes wait for `scrt_started` (the first sc_start); sc_stop sets
  // `scrt_stopped`, which ends a pending sc_start in sc_main.
  bit scrt_started;
  bit scrt_stopped;
  // sc_stop() from a process: the kernel stops (and reports it) at the end
  // of the current delta cycle.
  bit scrt_stop_req;
  // sc_time_stamp() as seen by sc_main while the simulation is paused.
  longint unsigned scrt_tb_now;

  // sc_time::to_string(): the value in the largest unit in which it is an
  // integer, "0 s" for zero (SystemC 2.3, resolution 1 ps).
  function automatic string scrt_time_str(longint unsigned ps);
    if (ps == 0) return "0 s";
    if (ps % 64'd1000000000000 == 0) return $sformatf("%0d s", ps / 64'd1000000000000);
    if (ps % 64'd1000000000 == 0) return $sformatf("%0d ms", ps / 64'd1000000000);
    if (ps % 64'd1000000 == 0) return $sformatf("%0d us", ps / 64'd1000000);
    if (ps % 64'd1000 == 0) return $sformatf("%0d ns", ps / 64'd1000);
    return $sformatf("%0d ps", ps);
  endfunction

  // sc_logic / sc_lv print 'X' and 'Z' in upper case.
  function automatic string scrt_upper(string s);
    return s.toupper();
  endfunction

  function automatic void scrt_stop();
    if (!scrt_stopped) begin
      $write("\nInfo: /OSCI/SystemC: Simulation stopped by user.\n");
      scrt_stopped = 1;
    end
  endfunction

  function automatic void scrt_stop_request();
    scrt_stop_req = 1;
  endfunction

  // §6.4.4: a second process writing an SC_ONE_WRITER signal (E115), in the
  // reference kernel's words; the error ends the simulation.
  function automatic void scrt_e115(string sig, string p1, string k1, string p2, string k2);
    $write("\nError: (E115) sc_signal<T> cannot have more than one driver: \n signal `%s' (sc_signal)\n first driver `%s' (%s)\n second driver `%s' (%s)\nIn file: communication/sc_signal.cpp:67\nIn process: %s @ %s\n",
           sig, p1, k1, p2, k2, p2, scrt_time_str($time));
    $__sc_exit(1);
  endfunction

  // sc_core::sc_module::name(): the instance path without the generated
  // `sc_main.` root.
  function automatic string scrt_name(string path);
    if (path.len() > 8 && path.substr(0, 7) == "sc_main.") return path.substr(8, path.len() - 1);
    return path;
  endfunction

  // sc_object::basename(): the last part of a hierarchical name.
  function automatic string scrt_basename(string path);
    for (int i = path.len() - 1; i >= 0; i--)
      if (path[i] == ".") return path.substr(i + 1, path.len() - 1);
    return path;
  endfunction

  // ---- byte-addressable memory for C++ pointers ----------------------------
  // An object whose address the C++ code takes is "boxed": stored in one of
  // these classes so a scrt_ptr can read and write its bytes (little endian,
  // like the x86 host SystemC runs on).
  virtual class scrt_mem;
    pure virtual function byte unsigned get8(longint unsigned i);
    pure virtual function void set8(longint unsigned i, byte unsigned b);
  endclass

  class scrt_box8 extends scrt_mem;
    bit [7:0] v;
    virtual function byte unsigned get8(longint unsigned i); return v; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); v = b; endfunction
  endclass

  class scrt_box16 extends scrt_mem;
    bit [15:0] v;
    virtual function byte unsigned get8(longint unsigned i); return v[i*8 +: 8]; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); v[i*8 +: 8] = b; endfunction
  endclass

  class scrt_box32 extends scrt_mem;
    bit [31:0] v;
    virtual function byte unsigned get8(longint unsigned i); return v[i*8 +: 8]; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); v[i*8 +: 8] = b; endfunction
  endclass

  class scrt_box64 extends scrt_mem;
    bit [63:0] v;
    virtual function byte unsigned get8(longint unsigned i); return v[i*8 +: 8]; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); v[i*8 +: 8] = b; endfunction
  endclass

  class scrt_arr8 extends scrt_mem;
    bit [7:0] a[];
    function new(int n); a = new[n]; endfunction
    virtual function byte unsigned get8(longint unsigned i); return a[i]; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); a[i] = b; endfunction
  endclass

  class scrt_arr16 extends scrt_mem;
    bit [15:0] a[];
    function new(int n); a = new[n]; endfunction
    virtual function byte unsigned get8(longint unsigned i); return a[i / 2][(i % 2)*8 +: 8]; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); a[i / 2][(i % 2)*8 +: 8] = b; endfunction
  endclass

  class scrt_arr32 extends scrt_mem;
    bit [31:0] a[];
    function new(int n); a = new[n]; endfunction
    virtual function byte unsigned get8(longint unsigned i); return a[i / 4][(i % 4)*8 +: 8]; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); a[i / 4][(i % 4)*8 +: 8] = b; endfunction
  endclass

  class scrt_arr64 extends scrt_mem;
    bit [63:0] a[];
    function new(int n); a = new[n]; endfunction
    virtual function byte unsigned get8(longint unsigned i); return a[i / 8][(i % 8)*8 +: 8]; endfunction
    virtual function void set8(longint unsigned i, byte unsigned b); a[i / 8][(i % 8)*8 +: 8] = b; endfunction
  endclass

  // A C++ data pointer: an object and a byte offset into it.
  class scrt_ptr;
    scrt_mem m;
    longint off;
    static function scrt_ptr mk(scrt_mem m, longint off);
      scrt_ptr p = new;
      p.m = m;
      p.off = off;
      return p;
    endfunction
    function scrt_ptr add(longint n); return mk(m, off + n); endfunction
    function byte unsigned get8(longint i); return m.get8(off + i); endfunction
    function void set8(longint i, byte unsigned b); m.set8(off + i, b); endfunction
    function bit [15:0] get16(longint i); return {get8(i + 1), get8(i)}; endfunction
    function bit [31:0] get32(longint i); return {get8(i + 3), get8(i + 2), get8(i + 1), get8(i)}; endfunction
    function bit [63:0] get64(longint i); return {get32(i + 4), get32(i)}; endfunction
    function void set16(longint i, bit [15:0] v); set8(i, v[7:0]); set8(i + 1, v[15:8]); endfunction
    function void set32(longint i, bit [31:0] v);
      for (int k = 0; k < 4; k++) set8(i + k, v[k*8 +: 8]);
    endfunction
    function void set64(longint i, bit [63:0] v);
      for (int k = 0; k < 8; k++) set8(i + k, v[k*8 +: 8]);
    endfunction
  endclass

  function automatic void scrt_memcpy(scrt_ptr d, scrt_ptr s, longint n);
    byte unsigned tmp[];
    tmp = new[n];
    for (longint i = 0; i < n; i++) tmp[i] = s.get8(i);
    for (longint i = 0; i < n; i++) d.set8(i, tmp[i]);
  endfunction

  function automatic void scrt_memset(scrt_ptr d, byte unsigned v, longint n);
    for (longint i = 0; i < n; i++) d.set8(i, v);
  endfunction

  function automatic int scrt_memcmp(scrt_ptr a, scrt_ptr b, longint n);
    for (longint i = 0; i < n; i++)
      if (a.get8(i) != b.get8(i)) return a.get8(i) < b.get8(i) ? -1 : 1;
    return 0;
  endfunction

  // ---- TLM-2.0 generic payload (IEEE 1666-2023 §14) -----------------------
  localparam int TLM_READ_COMMAND = 0;
  localparam int TLM_WRITE_COMMAND = 1;
  localparam int TLM_IGNORE_COMMAND = 2;

  localparam int TLM_OK_RESPONSE = 1;
  localparam int TLM_INCOMPLETE_RESPONSE = 0;
  localparam int TLM_GENERIC_ERROR_RESPONSE = -1;
  localparam int TLM_ADDRESS_ERROR_RESPONSE = -2;
  localparam int TLM_COMMAND_ERROR_RESPONSE = -3;
  localparam int TLM_BURST_ERROR_RESPONSE = -4;
  localparam int TLM_BYTE_ENABLE_ERROR_RESPONSE = -5;

  localparam int TLM_ACCEPTED = 0;
  localparam int TLM_UPDATED = 1;
  localparam int TLM_COMPLETED = 2;

  localparam int UNINITIALIZED_PHASE = 0;
  localparam int BEGIN_REQ = 1;
  localparam int END_REQ = 2;
  localparam int BEGIN_RESP = 3;
  localparam int END_RESP = 4;

  localparam int TLM_BYTE_DISABLED = 0;
  localparam int TLM_BYTE_ENABLED = 255;

  class scrt_tlm_gp;
    int m_command = TLM_IGNORE_COMMAND;
    longint unsigned m_address;
    scrt_ptr m_data;
    int unsigned m_length;
    int m_response_status = TLM_INCOMPLETE_RESPONSE;
    bit m_dmi;
    scrt_ptr m_byte_enable;
    int unsigned m_byte_enable_length;
    int unsigned m_streaming_width;

    function void set_command(int c); m_command = c; endfunction
    function int get_command(); return m_command; endfunction
    function bit is_read(); return m_command == TLM_READ_COMMAND; endfunction
    function bit is_write(); return m_command == TLM_WRITE_COMMAND; endfunction
    function void set_read(); m_command = TLM_READ_COMMAND; endfunction
    function void set_write(); m_command = TLM_WRITE_COMMAND; endfunction
    function void set_address(longint unsigned a); m_address = a; endfunction
    function longint unsigned get_address(); return m_address; endfunction
    function void set_data_ptr(scrt_ptr p); m_data = p; endfunction
    function scrt_ptr get_data_ptr(); return m_data; endfunction
    function void set_data_length(int unsigned n); m_length = n; endfunction
    function int unsigned get_data_length(); return m_length; endfunction
    function void set_streaming_width(int unsigned n); m_streaming_width = n; endfunction
    function int unsigned get_streaming_width(); return m_streaming_width; endfunction
    function void set_byte_enable_ptr(scrt_ptr p); m_byte_enable = p; endfunction
    function scrt_ptr get_byte_enable_ptr(); return m_byte_enable; endfunction
    function void set_byte_enable_length(int unsigned n); m_byte_enable_length = n; endfunction
    function int unsigned get_byte_enable_length(); return m_byte_enable_length; endfunction
    function void set_dmi_allowed(bit d); m_dmi = d; endfunction
    function bit is_dmi_allowed(); return m_dmi; endfunction
    function void set_response_status(int s); m_response_status = s; endfunction
    function int get_response_status(); return m_response_status; endfunction
    function bit is_response_ok(); return m_response_status > 0; endfunction
    function bit is_response_error(); return m_response_status <= 0; endfunction
    function string get_response_string();
      case (m_response_status)
        TLM_OK_RESPONSE: return "TLM_OK_RESPONSE";
        TLM_INCOMPLETE_RESPONSE: return "TLM_INCOMPLETE_RESPONSE";
        TLM_GENERIC_ERROR_RESPONSE: return "TLM_GENERIC_ERROR_RESPONSE";
        TLM_ADDRESS_ERROR_RESPONSE: return "TLM_ADDRESS_ERROR_RESPONSE";
        TLM_COMMAND_ERROR_RESPONSE: return "TLM_COMMAND_ERROR_RESPONSE";
        TLM_BURST_ERROR_RESPONSE: return "TLM_BURST_ERROR_RESPONSE";
        TLM_BYTE_ENABLE_ERROR_RESPONSE: return "TLM_BYTE_ENABLE_ERROR_RESPONSE";
        default: return "TLM_UNKNOWN_RESPONSE";
      endcase
    endfunction
    // Memory management (§14.5) has nothing to free here.
    function void acquire(); endfunction
    function void release_(); endfunction  // C++ `release()`; `release` is an SV keyword
    function bit has_mm(); return 0; endfunction
    function void reset(); m_command = TLM_IGNORE_COMMAND; m_response_status = TLM_INCOMPLETE_RESPONSE; endfunction
  endclass

  // ---- sockets (§13, §16.1) ------------------------------------------------
  // A target registers its transport methods as an scrt_fw_if object (a
  // class generated inside the target module that calls the module's task);
  // an initiator socket holds the target socket it is bound to.
  virtual class scrt_fw_if;
    virtual task b_transport(scrt_tlm_gp trans, inout longint unsigned delay);
      $display("Error: (E) b_transport: no b_transport registered on the target socket");
      $finish;
    endtask
    virtual function int unsigned transport_dbg(scrt_tlm_gp trans);
      return 0;
    endfunction
    virtual function bit get_direct_mem_ptr(scrt_tlm_gp trans);
      return 0;
    endfunction
  endclass

  class scrt_target_socket;
    scrt_fw_if fw;
  endclass

  class scrt_initiator_socket;
    scrt_target_socket peer;
    string name;
    function new(string n = ""); name = n; endfunction
    function void check();
      if (peer == null || peer.fw == null) begin
        $display("Error: (E) socket '%s' is not bound to a target", name);
        $finish;
      end
    endfunction
    task b_transport(scrt_tlm_gp trans, inout longint unsigned delay);
      check();
      peer.fw.b_transport(trans, delay);
    endtask
    function int unsigned transport_dbg(scrt_tlm_gp trans);
      check();
      return peer.fw.transport_dbg(trans);
    endfunction
    function bit get_direct_mem_ptr(scrt_tlm_gp trans);
      check();
      return peer.fw.get_direct_mem_ptr(trans);
    endfunction
  endclass
endpackage
