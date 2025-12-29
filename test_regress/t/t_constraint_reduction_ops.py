#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_constraint_reduction_ops.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile(
    verilator_flags2=['--timing', '-Wno-fatal'],
)

test.execute()

test.passes()
