#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for inline array size constraints (fails_verilator)
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_rand_inline_size.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

# This test documents the current limitation: inline size constraints don't work
# The pattern req.randomize() with { arr.size() == N; } treats size() as state
# not as a constraint variable. This affects SPI AVIP and similar testbenches.
#
# The CONSTRAINTIGN warning indicates this limitation.
# When this feature is implemented, remove fails_verilator and expect_filename.

test.compile(
    verilator_flags2=['--timing'],
    fails=test.vlt_all,
    expect_filename=test.golden_filename,
)

test.passes()
