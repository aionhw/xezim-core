#pragma once
#define BUS_WIDTH 32
#define REG(name, off) static const unsigned name##_OFFSET = off;
typedef sc_dt::sc_uint<BUS_WIDTH> word_t;
