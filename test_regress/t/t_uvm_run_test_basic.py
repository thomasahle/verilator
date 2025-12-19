#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_uvm_run_test_basic.v"

# Use absolute paths resolved at runtime
import os
verilator_root = os.environ.get('VERILATOR_ROOT', os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
include_dir = os.path.join(verilator_root, 'include')

test.compile(verilator_flags2=[
    "--timing",
    "-Wno-WIDTHTRUNC",
    f"+incdir+{include_dir}",
    f"{include_dir}/uvm_pkg.sv",
])

test.execute()

test.passes()
