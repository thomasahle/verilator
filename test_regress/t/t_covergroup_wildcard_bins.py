#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2026 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# Note: wildcard bins with ? syntax not yet fully implemented
# The ? characters are treated as 0 bits instead of wildcards
# Test passes but coverage is 0% - documenting current limitation
test.compile(
    verilator_flags2=["--timing"],
)

test.execute()

test.passes()
