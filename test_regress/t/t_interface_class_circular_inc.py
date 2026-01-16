#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')
test.top_filename = "t/t_interface_class_circular_inc.v"

# Test with interface file before package to test circular dependency handling
# This order would fail before the fix with:
#   %Error: Reference to 'DriverProxy' before declaration
test.lint(
    v_flags2=[
        "t/t_interface_class_circular_inc/DriverBfm.sv",
        "t/t_interface_class_circular_inc/DriverPkg.sv",
        "-It/t_interface_class_circular_inc"
    ],
    verilator_flags2=["--timing"]
)

test.passes()
