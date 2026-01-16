#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test config use parameter assignment

import vltest_bootstrap

test.scenarios('linter')

test.lint(verilator_flags2=["--top-module cfg"])

test.passes()
