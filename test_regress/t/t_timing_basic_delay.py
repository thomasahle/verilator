#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test basic timing delays work
import vltest_bootstrap
test.scenarios('simulator')
test.top_filename = "t/t_timing_basic_delay.v"
test.compile(timing_loop=True, verilator_flags2=['--timing'])
test.execute()
test.passes()
