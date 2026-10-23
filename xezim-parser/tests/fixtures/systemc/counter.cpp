#include "counter.h"
#include "counter.h" // second include is a no-op behind the guard

void counter::tick() {
    if (!rst_n.read()) {
        value = 0;
    } else if (en.read()) {
        value = value + 1;
        if (value == (1 << WIDTH) - 1) {
            SC_REPORT_INFO("counter", "wrap");
        }
    }
    count.write(value);
}
