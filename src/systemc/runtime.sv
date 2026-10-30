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
  // An unbounded sc_start() returns at sc_stop() or when no events are left
  // (§4.5.7): sc_main waits on this event, which sc_stop triggers and the
  // simulator resumes (instead of ending the run) once only blocked
  // processes remain.
  event scrt_idle_ev;
  // The last sc_start was bounded (it pauses 1 ps before its end time).
  bit scrt_lag;
  // The end_of_simulation callbacks have run (§4.4.4).
  bit scrt_eos_done;

  // sc_main's argv: the program name, then the comma-separated values of
  // the plusarg `+sc_args=a,b,…`.
  typedef string scrt_strq_t[$];
  function automatic scrt_strq_t scrt_args();
    string v;
    string q[$];
    int st = 0;
    q.push_back("sc_main");
    if ($value$plusargs("sc_args=%s", v))
      for (int i = 0; i <= v.len(); i++)
        if (i == v.len() || v[i] == ",") begin
          q.push_back(v.substr(st, i - 1));
          st = i + 1;
        end
    return q;
  endfunction
  function automatic int scrt_argc();
    scrt_strq_t q = scrt_args();
    return q.size();
  endfunction
  // A zero-time wait or notification (§4.2.1.3) takes effect in the next
  // delta cycle, after the update phase: the NBA region, where `->>`
  // triggers follow the signal updates.
  event scrt_delta_ev;
  task automatic scrt_wait(longint unsigned t);
    if (t == 0) begin
      ->> scrt_delta_ev;
      @(scrt_delta_ev);
    end else
      #(t);
  endtask
  // sc_stop() from a process: the kernel stops (and reports it) at the end
  // of the current delta cycle.
  bit scrt_stop_req;
  // sc_time_stamp() as seen by sc_main while the simulation is paused.
  longint unsigned scrt_tb_now;
  // sc_main runs between two sc_start calls (a bounded sc_start pauses
  // 1 ps before its end time): module code it calls sees scrt_tb_now.
  bit scrt_paused;

  function automatic longint unsigned scrt_now();
    return scrt_paused ? scrt_tb_now : $time;
  endfunction

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
    -> scrt_idle_ev;
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

  // ---- C rand()/srand(): glibc's generator, so runs match the C program ---
  // The additive feedback generator glibc's random_r uses (TYPE_3, degree
  // 31, separation 3): 34 values of state, seeded through 16807 * x mod
  // 2^31 - 1 and stepped 310 times; each rand() is the next sum >> 1.
  int scrt_rand_r[34];
  int scrt_rand_k;
  bit scrt_rand_seeded;

  function automatic void scrt_srand(int unsigned seed);
    int t[344];
    longint w;
    if (seed == 0) seed = 1;
    t[0] = seed;
    for (int i = 1; i < 31; i++) begin
      w = (64'sd16807 * t[i - 1]) % 64'sd2147483647;
      if (w < 0) w += 64'sd2147483647;
      t[i] = int'(w);
    end
    for (int i = 31; i < 34; i++) t[i] = t[i - 31];
    for (int i = 34; i < 344; i++) t[i] = t[i - 31] + t[i - 3];
    for (int i = 0; i < 34; i++) scrt_rand_r[i] = t[310 + i];
    scrt_rand_k = 0;
    scrt_rand_seeded = 1;
  endfunction

  function automatic int scrt_rand();
    int v;
    if (!scrt_rand_seeded) scrt_srand(1);
    v = scrt_rand_r[(scrt_rand_k + 3) % 34] + scrt_rand_r[(scrt_rand_k + 31) % 34];
    scrt_rand_r[scrt_rand_k] = v;
    scrt_rand_k = (scrt_rand_k + 1) % 34;
    return int'(int unsigned'(v) >> 1);
  endfunction

  // ---- ports and exports of user interfaces (§5.12, §5.14) ----------------
  // Every port and export object registers here; at the end of elaboration
  // (the first sc_start) one bound to nothing is error E109, as the
  // reference kernel reports it.
  virtual class scrt_port_base;
    string name;
    bit is_export;
    pure virtual function int nbound();
  endclass

  scrt_port_base scrt_ports[$];

  function automatic void scrt_check_bindings();
    foreach (scrt_ports[i])
      if (scrt_ports[i].nbound() == 0) begin
        string k = scrt_ports[i].is_export ? "export" : "port";
        $write("\nError: (E109) complete binding failed: %s not bound: %s '%s' (sc_%s)\nIn file: communication/sc_%s.cpp:%0d\n",
               k, k, scrt_ports[i].name, k, k, scrt_ports[i].is_export ? 137 : 235);
        $__sc_exit(1);
        return;
      end
  endfunction

  // ---- report handler (§8.3) ------------------------------------------------
  // The reference kernel's sc_report_handler: actions chosen per (id,
  // severity), id, then severity rule; suppress/force masks; stop_after
  // limits; counts; verbosity. A user handler (set_handler) is dispatched
  // where the report is made (scrt_handler names it); the default handler
  // is here. SC_THROW ends the run as the uncaught exception does: the
  // handler then sees the report with the catch actions (SC_DISPLAY).
  localparam int unsigned SCRT_DO_NOTHING = 'h01, SCRT_THROW = 'h02, SCRT_LOG = 'h04,
      SCRT_DISPLAY = 'h08, SCRT_CACHE = 'h10, SCRT_INTERRUPT = 'h20, SCRT_STOP = 'h40,
      SCRT_ABORT = 'h80;
  localparam int unsigned SCRT_NO_LIMIT = 32'hffff_ffff;

  class scrt_report;
    int sev;
    int num_id = -1;
    string id;
    string msg;
    string file;
    int line;
    int verb;
    longint unsigned t;
    string proc;
    function string compose();
      string sevs[4] = '{"Info", "Warning", "Error", "Fatal"};
      string sv = sevs[sev];
      string iwef = "IWEF";
      string str = {sv, ": "};
      if (num_id >= 0) str = {str, $sformatf("(%s%0d) ", iwef.substr(sev, sev), num_id)};
      str = {str, id};
      if (msg != "") str = {str, ": ", msg};
      if (sev > 0) begin
        str = {str, $sformatf("\nIn file: %s:%0d", file, line)};
        if (proc != "") str = {str, "\nIn process: ", proc, " @ ", scrt_time_str(t)};
      end
      return str;
    endfunction
  endclass

  class scrt_msg_def;
    int unsigned actions;
    int unsigned sev_actions[4];
    int unsigned limit_mask;
    int unsigned limit;
    int unsigned sev_limit[4];
    int unsigned call_count;
    int unsigned sev_call_count[4];
  endclass

  scrt_msg_def scrt_msgs[string];
  int unsigned scrt_sev_actions[4] = '{'h0c, 'h0c, 'h16, 'h9c};
  int unsigned scrt_sev_limit[4] = '{SCRT_NO_LIMIT, SCRT_NO_LIMIT, SCRT_NO_LIMIT, SCRT_NO_LIMIT};
  int unsigned scrt_sev_count[4];
  int unsigned scrt_suppress_mask;
  int unsigned scrt_force_mask;
  int unsigned scrt_available_actions = 'hff;
  int scrt_verbosity = 200;
  // The handler: 0 the default one, k > 0 the k-th function set_handler names.
  int scrt_handler;
  bit scrt_thrown;

  function automatic scrt_msg_def scrt_md(string id);
    if (!scrt_msgs.exists(id)) scrt_msgs[id] = new;
    return scrt_msgs[id];
  endfunction

  function automatic int unsigned scrt_set_actions(int sev, string id, bit by_sev, bit by_id,
                                                   int unsigned a);
    int unsigned old;
    scrt_msg_def md;
    if (!by_id) begin
      old = scrt_sev_actions[sev];
      scrt_sev_actions[sev] = a;
      return old;
    end
    md = scrt_md(id);
    if (by_sev) begin
      old = md.sev_actions[sev];
      md.sev_actions[sev] = a;
    end else begin
      old = md.actions;
      md.actions = a;
    end
    return old;
  endfunction

  function automatic int scrt_stop_after(int sev, string id, bit by_sev, bit by_id, int lim);
    int old;
    int unsigned mask;
    scrt_msg_def md;
    if (!by_id) begin
      old = scrt_sev_limit[sev];
      scrt_sev_limit[sev] = lim < 0 ? SCRT_NO_LIMIT : lim;
      return old;
    end
    md = scrt_md(id);
    mask = by_sev ? 1 << (sev + 1) : 1;
    old = (md.limit_mask & mask) ? (by_sev ? md.sev_limit[sev] : md.limit) : SCRT_NO_LIMIT;
    if (lim < 0) md.limit_mask &= ~mask;
    else begin
      md.limit_mask |= mask;
      if (by_sev) md.sev_limit[sev] = lim;
      else md.limit = lim;
    end
    return old;
  endfunction

  function automatic int scrt_get_count(int sev, string id, bit by_sev, bit by_id);
    scrt_msg_def md;
    if (!by_id) return scrt_sev_count[sev];
    md = scrt_md(id);
    return by_sev ? md.sev_call_count[sev] : md.call_count;
  endfunction

  function automatic int unsigned scrt_suppress(int unsigned mask);
    int unsigned old = scrt_suppress_mask;
    scrt_suppress_mask = mask;
    return old;
  endfunction

  function automatic int unsigned scrt_force(int unsigned mask);
    int unsigned old = scrt_force_mask;
    scrt_force_mask = mask;
    return old;
  endfunction

  function automatic int unsigned scrt_new_action_id();
    for (int unsigned p = 1; p != 0; p <<= 1)
      if (!(p & scrt_available_actions)) begin
        scrt_available_actions |= p;
        return p;
      end
    return 0;
  endfunction

  function automatic int scrt_set_verbosity(int v);
    int old = scrt_verbosity;
    scrt_verbosity = v;
    return old;
  endfunction

  // A report, or null when an info report is above the verbosity level.
  function automatic scrt_report scrt_report_make(int sev, string id, string msg, int verb,
                                                  string file, int line, string proc);
    scrt_report r;
    if (sev == 0 && verb > scrt_verbosity) return null;
    r = new;
    r.sev = sev;
    r.id = id;
    r.msg = msg;
    r.verb = verb;
    r.file = file;
    r.line = line;
    r.t = scrt_now();
    r.proc = proc;
    return r;
  endfunction

  // The actions for a report (sc_report_handler::execute), counting it.
  function automatic int unsigned scrt_report_actions(scrt_report r);
    scrt_msg_def md = scrt_md(r.id);
    int unsigned a = md.sev_actions[r.sev];
    int unsigned lim, cnt;
    bit have = 0;
    if (a == 0) a = md.actions;
    if (a == 0) a = scrt_sev_actions[r.sev];
    a &= ~scrt_suppress_mask;
    a |= scrt_force_mask;
    if (md.sev_call_count[r.sev] != SCRT_NO_LIMIT) md.sev_call_count[r.sev]++;
    if (md.call_count != SCRT_NO_LIMIT) md.call_count++;
    if (scrt_sev_count[r.sev] != SCRT_NO_LIMIT) scrt_sev_count[r.sev]++;
    if (md.limit_mask & (1 << (r.sev + 1))) begin
      lim = md.sev_limit[r.sev];
      cnt = md.sev_call_count[r.sev];
      have = 1;
    end
    if (!have && (md.limit_mask & 1)) begin
      lim = md.limit;
      cnt = md.call_count;
      have = 1;
    end
    if (!have) begin
      lim = scrt_sev_limit[r.sev];
      cnt = scrt_sev_count[r.sev];
    end
    if (lim != 0 && lim != SCRT_NO_LIMIT && cnt >= lim) a |= SCRT_STOP;
    return a;
  endfunction

  function automatic void scrt_default_handler(scrt_report r, int unsigned a, bit tb);
    if (a & SCRT_DISPLAY) $write("\n%s\n", r.compose());
    if (a & SCRT_STOP) begin
      if (tb) scrt_stop();
      else scrt_stop_request();
    end
    if (a & SCRT_ABORT) scrt_abort(tb);
    if (a & SCRT_THROW) scrt_thrown = 1;
  endfunction

  // sc_abort(): the kernel's info report I99, then abort (status 134).
  function automatic void scrt_abort(bit tb);
    scrt_report r = scrt_report_make(0, "simulation aborted", "", 200, "", 0, "");
    if (r != null) begin
      r.num_id = 99;
      scrt_default_handler(r, scrt_report_actions(r), tb);
    end
    $__sc_exit(134);
  endfunction

  // A report through the default handler; a throw ends the run (status 1)
  // after the catch's display.
  function automatic void scrt_report_default(scrt_report r, bit tb);
    if (r == null) return;
    scrt_default_handler(r, scrt_report_actions(r), tb);
    if (scrt_thrown) begin
      scrt_thrown = 0;
      scrt_default_handler(r, SCRT_DISPLAY, tb);
      $__sc_exit(1);
    end
  endfunction

  // ---- process handles (§5.6) -------------------------------------------------
  // A spawned thread's handle: `finish()` at its end makes it terminated.
  class scrt_proc;
    event done;
    bit term;
    function void finish();
      term = 1;
      -> done;
    endfunction
  endclass

  // sc_spawn_options: nothing to set that has an effect here.
  class scrt_spawn_opts;
  endclass

  // ---- sc_fifo (§6.23) -------------------------------------------------------
  // As the reference kernel: a value written becomes readable, and the space
  // a read frees writable, only in the update phase. `readable` is the count
  // of the last update; `nread`/`nwritten` count this delta's accesses. Each
  // access schedules the update as nonblocking assignments (the update phase
  // is the NBA region): the last one of the delta sets the final count, and
  // the data events trigger after it.
  class scrt_fifo #(type T = int);
    T items[$];
    int size;
    int readable;
    int nread;
    int nwritten;
    event written_ev;
    event read_ev;
    function new(int n = 16); size = n; endfunction
    function void request_update(bit wrote);
      readable <= items.size();
      nread <= 0;
      nwritten <= 0;
      if (wrote) ->> written_ev;
      else ->> read_ev;
    endfunction
    function int num(); return readable - nread; endfunction
    function int num_free(); return size - readable - nwritten; endfunction
    task put(T v);
      while (num_free() == 0) @(read_ev);
      items.push_back(v);
      nwritten++;
      request_update(1);
    endtask
    task get(output T v);
      while (num() == 0) @(written_ev);
      v = items.pop_front();
      nread++;
      request_update(0);
    endtask
    function bit try_put(T v);
      if (num_free() == 0) return 0;
      items.push_back(v);
      nwritten++;
      request_update(1);
      return 1;
    endfunction
    function bit try_get(output T v);
      if (num() == 0) return 0;
      v = items.pop_front();
      nread++;
      request_update(0);
      return 1;
    endfunction
  endclass

  // ---- sc_mutex, sc_semaphore, sc_event_queue (§6.27–§6.29) ----------------
  // As the reference kernel: a mutex belongs to the process that locked it
  // (locking it again returns at once), unlock by another process fails,
  // and releasing notifies the waiters immediately.
  class scrt_mutex;
    process owner;
    event free_ev;
    task lock(output int r);
      if (owner != null && owner == process::self()) begin r = 0; return; end
      while (owner != null) @(free_ev);
      owner = process::self();
      r = 0;
    endtask
    function int trylock();
      if (owner != null && owner == process::self()) return 0;
      if (owner != null) return -1;
      owner = process::self();
      return 0;
    endfunction
    function int unlock();
      if (owner == null || owner != process::self()) return -1;
      owner = null;
      -> free_ev;
      return 0;
    endfunction
  endclass

  class scrt_semaphore;
    int value;
    event free_ev;
    function new(int n = 1); value = n; endfunction
    task wait_(output int r);
      while (value <= 0) @(free_ev);
      value--;
      r = 0;
    endtask
    function int trywait();
      if (value <= 0) return -1;
      value--;
      return 0;
    endfunction
    function int post();
      value++;
      -> free_ev;
      return 0;
    endfunction
    function int get_value(); return value; endfunction
  endclass

  // Every notify() is an event of its own at its time; cancel_all() drops
  // the pending ones.
  class scrt_event_queue;
    event ev;
    int gen;
    function void notify(longint unsigned t);
      int g = gen;
      if (t == 0) begin
        ->> ev;
        return;
      end
      fork
        begin
          #(t);
          if (g == gen) -> ev;
        end
      join_none
    endfunction
    function void cancel_all(); gen++; endfunction
  endclass

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

  // `new T[n]` of a scalar type: an array of n elements of `bytes` bytes.
  function automatic scrt_ptr scrt_new_array(int unsigned bytes, longint n);
    case (bytes)
      1: begin scrt_arr8 a = new(n); return scrt_ptr::mk(a, 0); end
      2: begin scrt_arr16 a = new(n); return scrt_ptr::mk(a, 0); end
      4: begin scrt_arr32 a = new(n); return scrt_ptr::mk(a, 0); end
      default: begin scrt_arr64 a = new(n); return scrt_ptr::mk(a, 0); end
    endcase
  endfunction

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
