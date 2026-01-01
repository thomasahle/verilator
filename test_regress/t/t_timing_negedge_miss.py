#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for negedge event scheduling bug
#
# This tests that @(negedge signal) catches edges during startup.
# This pattern is used in UVM BFMs - works in Xcelium, may hang in Verilator.

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_timing_negedge_miss.v"

test.compile(
    timing_loop=True,
    verilator_flags2=['--timing'],
)

test.execute()

test.passes()
