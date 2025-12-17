#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test coverpoints with expressions
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Anthropic.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_covergroup_expr.v"

test.compile(
    verilator_flags2=['-Wno-COVERIGN', '-Wno-WIDTHEXPAND', '--timing'],
)

test.execute()

test.passes()
