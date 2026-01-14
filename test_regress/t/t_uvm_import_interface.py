#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import vltest_bootstrap

test.scenarios('vlt')

# Test that interface-level UVM import doesn't cause std package error
# when there's also a module-level package import.
# This tests the fix for std package symbol entry ordering.

test.lint(verilator_flags2=[
    "--timing",
    "-Wno-fatal",  # UVM has some width warnings
    "+incdir+" + test.obj_dir,
    "+incdir+" + os.environ.get('UVM_HOME', os.path.expanduser('~/repos/uvm/src')),
    "+define+UVM_NO_DPI"
])
test.passes()
