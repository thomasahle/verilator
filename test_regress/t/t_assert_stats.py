#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test assertion statistics tracking
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--binary', '--assert-stats', '--timing'])

test.execute(check_finished=True)

# Check that assertion summary was printed with proper format
test.file_grep(test.run_log_filename, r'=== Assertion Summary ===')
test.file_grep(test.run_log_filename, r'assert_a.*PASS.*pass: \d+')
test.file_grep(test.run_log_filename, r'assert_never_zero.*PASS.*pass: \d+')
test.file_grep(test.run_log_filename, r'Total:.*assertions.*exercised')

test.passes()
