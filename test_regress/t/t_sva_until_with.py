#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test SVA until_with and s_until_with operators

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_sva_until_with.v"

test.compile(
    verilator_flags2=['--timing', '--assert'],
    timing_loop=True,
)

test.execute()

test.passes()
