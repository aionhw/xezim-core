// Hierarchy, SC_CTHREAD with reset, a template module, a plain-class
// module with SC_HAS_PROCESS and an out-of-class constructor, sc_main.
#include <systemc>
#include <iostream>
#include <vector>
#include "counter.h"
using namespace sc_core;
using namespace sc_dt;

template <int W = 4>
SC_MODULE(shifter) {
    sc_in_clk clk;
    sc_in<bool> rst;
    sc_in<sc_bv<W>> din;
    sc_out<sc_bv<W>> dout;

    void run() {
        sc_bv<W> r = 0;
        dout.write(r);
        wait();
        while (true) {
            sc_bv<W> d = din.read();
            r = (d.range(W - 2, 0), d[W - 1]);
            dout.write(r);
            wait();
        }
    }

    SC_CTOR(shifter) {
        SC_CTHREAD(run, clk.pos());
        reset_signal_is(rst, true);
    }
};

enum class state_t : unsigned { IDLE, LOAD, RUN = 4 };

class fsm : public sc_core::sc_module {
public:
    sc_in<bool> clk;
    sc_vector<sc_in<bool>> req{"req", 4};
    sc_out<unsigned> grant;

    SC_HAS_PROCESS(fsm);
    fsm(sc_module_name nm, unsigned n);
    ~fsm() override = default;

private:
    state_t st = state_t::IDLE;
    unsigned n_;
    void step();
};

fsm::fsm(sc_module_name nm, unsigned n) : sc_module(nm), clk("clk"), grant("grant"), n_(n) {
    SC_METHOD(step);
    sensitive << clk.pos();
    for (unsigned i = 0; i < req.size(); ++i)
        sensitive << req[i];
}

void fsm::step() {
    switch (st) {
    case state_t::IDLE:
        for (unsigned i = 0; i < n_; i++) {
            if (req[i].read()) { grant.write(i); st = state_t::LOAD; break; }
        }
        break;
    case state_t::LOAD:
    case state_t::RUN: {
        unsigned g = grant.read();
        grant.write(g > 0 ? g - 1 : 0u);
        st = static_cast<state_t>(0);
        break;
    }
    default:
        st = state_t::IDLE;
    }
}

SC_MODULE(top) {
    sc_clock clk{"clk", 10, SC_NS};
    sc_signal<bool> rst_n, en;
    sc_signal<sc_uint<WIDTH>> count;
    counter* cnt;
    shifter<8> sh{"sh"};
    std::vector<int> history;

    SC_CTOR(top) {
        cnt = new counter("cnt");
        cnt->clk(clk);
        cnt->rst_n(rst_n);
        cnt->en(en);
        cnt->count(count);
        SC_THREAD(stim);
    }
    ~top() { delete cnt; }

    void stim() {
        rst_n = false;
        wait(20, SC_NS);
        rst_n = true;
        en.write(true);
        for (auto& h : history) { h <<= 1; }
        wait(100, SC_NS);
        sc_stop();
    }
};

int sc_main(int argc, char* argv[]) {
    top t("t");
    sc_trace_file* tf = sc_create_vcd_trace_file("wave");
    sc_trace(tf, t.count, "count");
    sc_start(200, SC_NS);
    sc_close_vcd_trace_file(tf);
    std::cout << "done at " << sc_time_stamp() << std::endl;
    return 0;
}
