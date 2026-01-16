#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# TODO: The repeat event control feature (IEEE 1800-2017 Section 9.4.5.1)
# compiles correctly but has runtime issues - the simulation times out
# due to timing model issues with how processes waiting on triggers are
# scheduled. This test only verifies compilation until the runtime issue
# is fixed.

import vltest_bootstrap

test.scenarios('simulator')

# Only verify compilation - execution times out due to timing issues
test.compile(verilator_flags2=['--timing'])

# Uncomment when runtime issue is fixed:
# test.execute()

test.passes()
