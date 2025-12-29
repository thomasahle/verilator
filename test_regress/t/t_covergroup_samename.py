#!/usr/bin/env python3
# DESCRIPTION: Verilator test
# Test covergroup sample parameter with same name as type
#
# This is a regression test for the case where a covergroup sample
# function parameter has the same name as its type (e.g., Config Config).
# Previously this caused "Expecting a data type" errors because the
# symbol lookup found the parameter variable before the class type.

import vltest_bootstrap

test.scenarios("simulator")
test.compile(verilator_flags2=["--binary", "--timing"], make_main=False)
test.execute()
test.passes()
