#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios("vlt")
test.top_filename = "t/t_covergroup_transition.v"

test.compile(verilator_flags2=["--timing"])

test.execute()

test.passes()
