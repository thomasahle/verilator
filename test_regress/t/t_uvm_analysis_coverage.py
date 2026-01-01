#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for UVM analysis port with coverage subscriber
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_uvm_analysis_coverage.v"

# Test that UVM analysis ports work correctly with coverage subscribers.
# This tests the clone() function which requires get_type_name() to return
# the correct type name for factory lookup.

test.compile(
    verilator_flags2=['--timing', '-Wno-WIDTHTRUNC', '-Wno-WIDTHEXPAND', '-Wno-IMPLICITSTATIC',
                      '+incdir+../include', '../include/uvm_pkg.sv'],
)

test.execute()

test.passes()
