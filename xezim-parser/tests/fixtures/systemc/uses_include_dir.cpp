#include <bus_defs.h>
#include "bus_defs.h"
#if BUS_WIDTH > 16 && defined(USE_REGS)
REG(CTRL, 0x0)
REG(STATUS, 0x4)
#else
#error regs need a wide bus
#endif
SC_MODULE(regs) {
    sc_in<word_t> wdata;
};
