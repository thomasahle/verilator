#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for inline array size constraints
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_rand_inline_size.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

# Test that inline size constraints work correctly:
#   req.randomize() with { arr.size() == N; }
# This pattern is used in SPI AVIP and similar testbenches.

test.compile(
    verilator_flags2=['--timing'],
)

test.execute()

test.passes()
