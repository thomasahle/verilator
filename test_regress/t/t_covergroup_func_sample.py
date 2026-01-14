#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for covergroup with function sample
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2026 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_covergroup_func_sample.v"

test.compile(verilator_flags2=["--binary", "--coverage"])

test.execute()

test.passes()
