#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test inline constraints with parametric class inheritance
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("Requires solver")

test.compile(
    verilator_flags2=['--timing'],
)

test.execute()

test.passes()
