#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test $unit-scope wildcard import visibility in interfaces
#
# Tests that package parameters imported via wildcard at $unit scope are
# visible inside interfaces defined in the same file.
# See IEEE 1800-2017 Section 26.3 for $unit scope semantics.

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_unit_import_iface.v"

test.compile(
    verilator_flags2=['--timing', '--assert'],
    timing_loop=True,
)

test.execute()

test.passes()
