#pragma once

#include <eosio/chain/webassembly/eos-vm-oc/config.hpp>

#include <boost/asio/local/datagram_protocol.hpp>
#include <eosio/chain/webassembly/eos-vm-oc/ipc_helpers.hpp>

namespace eosio { namespace chain { namespace eosvmoc {

wrapped_fd get_connection_to_compile_monitor(int cache_fd);

struct compile_monitor_trampoline {
    compile_monitor_trampoline();
    ~compile_monitor_trampoline();
    void start();

    pid_t compile_manager_pid = -1;
    int compile_manager_fd = -1;
};
}}}