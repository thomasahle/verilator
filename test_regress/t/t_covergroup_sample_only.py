#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test covergroup with only sample args (no constructor args)
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.compile(verilator_flags2=['--binary --coverage -Wno-WIDTHTRUNC -Wno-UNSIGNED -Wno-CMPCONST'])
test.execute()
test.passes()
