#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test $countones in randomization constraints
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_rand_countones.v"

if not test.have_solver:
    test.skip("No solver available")

test.compile(
    verilator_flags2=['--timing', '-Wno-fatal'],
    timing_loop=True,
)

test.execute()

test.passes()
