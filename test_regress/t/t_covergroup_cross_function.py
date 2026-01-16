#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test cross coverage function declaration

import vltest_bootstrap

test.scenarios('simulator')
test.compile(timing_loop=True, verilator_flags2=['--timing'])
test.execute()
test.passes()
