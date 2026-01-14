#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test complex constraints
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile(verilator_flags2=[
    "--timing",
    "-Wno-CONSTRAINTIGN",
    "-Wno-WIDTHEXPAND",
    "-Wno-WIDTHTRUNC",
])

test.execute()

test.passes()
