#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test workaround for negedge event scheduling bug

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_timing_negedge_workaround.v"

test.compile(
    timing_loop=True,
    verilator_flags2=['--timing'],
)

test.execute()

test.passes()
