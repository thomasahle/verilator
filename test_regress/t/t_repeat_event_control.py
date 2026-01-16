#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Test repeat event control as intra-assignment timing control
# IEEE 1800-2017 Section 9.4.5.1

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary', '--timing'])

test.execute()

test.passes()
