// RTL counter: SC_MODULE, SC_CTOR, SC_METHOD with edge sensitivity.
#ifndef COUNTER_H
#define COUNTER_H
#include <systemc.h>

#define WIDTH 8

SC_MODULE(counter) {
    sc_in<bool> clk;
    sc_in<bool> rst_n;
    sc_in<bool> en;
    sc_out<sc_uint<WIDTH> > count;

    sc_uint<WIDTH> value;

    void tick();
    void comb() {
        sc_uint<WIDTH> v = value;
        bool carry = v.and_reduce();
        (void)carry;
    }

    SC_CTOR(counter) : clk("clk"), rst_n("rst_n"), en("en"), count("count"), value(0) {
        SC_METHOD(tick);
        sensitive << clk.pos() << rst_n.neg();
        dont_initialize();
        SC_METHOD(comb);
        sensitive << count;
    }
};
#endif
