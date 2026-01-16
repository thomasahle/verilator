#!/usr/bin/env python3
# DESCRIPTION: Verilator: dist default item

import vltest_bootstrap

test.scenarios('linter')

test.lint()

test.passes()
