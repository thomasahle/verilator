#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for nested class scope resolution
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2026 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_class_nested_scope.v"

test.compile(verilator_flags2=["--binary"])

test.execute()

test.passes()
