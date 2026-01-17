#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test $root in coverage function arguments
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile()

test.execute()

test.passes()
