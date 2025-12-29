#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test SVA sequence delay patterns
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2024 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios("simulator")

test.compile(verilator_flags2=["--binary", "--assert"], make_main=False)

test.execute()

test.passes()
