#!/usr/bin/env python3
# DESCRIPTION: Verilator: UVM config_db wildcard pattern matching test
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_uvm_config_db_wildcard.v"

test.compile(
    verilator_flags2=['--timing', '-Wno-fatal',
                      '+incdir+' + os.environ['VERILATOR_ROOT'] + '/include',
                      os.environ['VERILATOR_ROOT'] + '/include/uvm_pkg.sv'],
)

test.execute()

test.passes()
