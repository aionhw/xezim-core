// TLM-2.0 approximately-timed target, a router template with tagged
// sockets, a payload event queue and a spawned lambda.
#include <systemc>
#include <tlm>
#include <tlm_utils/simple_initiator_socket.h>
#include <tlm_utils/simple_target_socket.h>
#include <tlm_utils/peq_with_cb_and_phase.h>
#include <queue>
#include <map>
#include <cstdio>

using namespace sc_core;
using namespace tlm;

template <unsigned int N_TARGETS>
struct Router : sc_module {
    tlm_utils::simple_target_socket<Router> target_socket;
    tlm_utils::simple_initiator_socket_tagged<Router>* initiator_socket[N_TARGETS];

    SC_CTOR(Router) : target_socket("target_socket") {
        target_socket.register_b_transport(this, &Router::b_transport);
        for (unsigned int i = 0; i < N_TARGETS; i++) {
            char txt[20];
            sprintf(txt, "socket_%d", i);
            initiator_socket[i] = new tlm_utils::simple_initiator_socket_tagged<Router>(txt);
        }
    }

    virtual void b_transport(tlm_generic_payload& trans, sc_time& delay) {
        sc_dt::uint64 address = trans.get_address();
        unsigned int target_nr = static_cast<unsigned int>(address >> 8) & (N_TARGETS - 1);
        trans.set_address(address & 0xFF);
        (*initiator_socket[target_nr])->b_transport(trans, delay);
    }
};

class AtTarget : public sc_module, public tlm_fw_transport_if<> {
public:
    tlm_target_socket<32> socket;
    tlm_utils::peq_with_cb_and_phase<AtTarget> m_peq;
    std::map<tlm_generic_payload*, unsigned int> m_pending;
    std::queue<tlm_generic_payload*> m_response_queue;
    sc_event target_done_event;

    SC_HAS_PROCESS(AtTarget);
    explicit AtTarget(sc_module_name name)
        : sc_module(name), socket("socket"), m_peq(this, &AtTarget::peq_cb) {
        socket.bind(*this);
        SC_METHOD(execute_transaction_process);
        sensitive << target_done_event;
        dont_initialize();
        sc_spawn([this]() {
            wait(SC_ZERO_TIME);
            target_done_event.notify(sc_time(1, SC_NS));
        });
    }

    tlm_sync_enum nb_transport_fw(tlm_generic_payload& trans, tlm_phase& phase, sc_time& delay) override {
        m_peq.notify(trans, phase, delay);
        return TLM_ACCEPTED;
    }

    void b_transport(tlm_generic_payload&, sc_time&) override {}
    bool get_direct_mem_ptr(tlm_generic_payload&, tlm_dmi&) override { return false; }
    unsigned int transport_dbg(tlm_generic_payload&) override { return 0; }

    void peq_cb(tlm_generic_payload& trans, const tlm_phase& phase) {
        if (phase == BEGIN_REQ) {
            trans.acquire();
            m_pending[&trans]++;
            m_response_queue.push(&trans);
            target_done_event.notify(10, SC_NS);
        } else if (phase == END_RESP) {
            trans.release();
        }
    }

    void execute_transaction_process() {
        if (m_response_queue.empty()) return;
        tlm_generic_payload* trans = m_response_queue.front();
        m_response_queue.pop();
        tlm_phase bw_phase = BEGIN_RESP;
        sc_time delay = SC_ZERO_TIME;
        tlm_sync_enum status = socket->nb_transport_bw(*trans, bw_phase, delay);
        if (status == TLM_UPDATED || status == TLM_COMPLETED) {
            trans->release();
        }
    }
};
