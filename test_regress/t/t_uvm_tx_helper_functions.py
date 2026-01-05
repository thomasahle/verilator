#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test transaction helper functions and post-randomize patterns
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_uvm_tx_helper_functions.v"

# Need solver for constraints
if test.have_solver:
    test.compile(verilator_flags2=['--binary --timing -Wno-PKGNODECL -Wno-IMPLICITSTATIC -Wno-CONSTRAINTIGN -Wno-MISINDENT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND +incdir+../include ../include/uvm_pkg.sv'])
    test.execute()
    test.passes()
else:
    test.skip("No constraint solver available")
