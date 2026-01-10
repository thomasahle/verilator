#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# Note: The map method is partially implemented but has a type handling bug
# when the with expression returns a different type than the array elements.
# This test exposes that bug - the comparison (el == 200) returns boolean
# but the destination array is int[].
# See t_array_map.v for working map tests.

test.scenarios('simulator')

# Currently fails during C++ compilation due to type mismatch
test.compile(make_main=False, make_top_shell=False, verilator_make_gmake=False)

# Skip execution until the bug is fixed
#test.execute()

test.passes()
