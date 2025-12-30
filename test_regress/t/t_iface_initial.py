#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for interface with multiple initial blocks

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_iface_initial.v"

test.compile()

test.execute()

test.passes()
