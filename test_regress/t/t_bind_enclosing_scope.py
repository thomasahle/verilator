#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test bind with signals from enclosing scope
#
# Tests bind statements that reference signals from the enclosing
# module's scope. This pattern is used in JTAG AVIP.

import vltest_bootstrap

test.scenarios('simulator')

test.compile(
    timing_loop=True,
    verilator_flags2=["--timing", "--assert"],
)

test.execute()

test.passes()
