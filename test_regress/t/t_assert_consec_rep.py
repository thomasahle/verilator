#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_assert_consec_rep.v"

test.compile(verilator_flags2=["--assert --timing"])

test.execute()

test.passes()
