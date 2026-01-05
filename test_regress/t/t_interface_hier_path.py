#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test interface port connection via hierarchical path
#
# Tests that interface ports can be connected using hierarchical paths like
# container.inner instead of just direct variable references. This pattern
# is commonly used in UVM VIPs with macro-expanded interface paths.

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_interface_hier_path.v"

test.compile(verilator_flags2=['--timing --binary'])

test.execute()

test.passes()
