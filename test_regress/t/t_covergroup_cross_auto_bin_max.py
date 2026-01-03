#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for option.cross_auto_bin_max
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2026 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_covergroup_cross_auto_bin_max.v"

test.compile(verilator_flags2=['--timing', '-Wno-COVERIGN'])

test.execute()

test.passes()
