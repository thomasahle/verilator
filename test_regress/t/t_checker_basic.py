#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test checker declaration

import vltest_bootstrap

test.scenarios('simulator')
test.compile(verilator_flags2=['--timing'])
test.execute()
test.passes()
