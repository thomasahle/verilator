#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test process handles and await
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(
    verilator_flags2=[
        '--binary',
        '--timing',
    ],
    timing_loop=True,
)

test.execute()

test.passes()
