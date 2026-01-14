#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test reserved address range constraints using enums
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_constraint_reserved_range.v"

if test.have_solver:
    test.compile(verilator_flags2=['--binary --timing -Wno-WIDTHTRUNC'])
    test.execute()
    test.passes()
else:
    test.skip("No constraint solver available")
