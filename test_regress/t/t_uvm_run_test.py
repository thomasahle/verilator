#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test UVM run_test() with factory registration
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

# Use absolute paths resolved at runtime
import os
verilator_root = os.environ.get('VERILATOR_ROOT', os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
include_dir = os.path.join(verilator_root, 'include')

test.compile(
    verilator_flags2=[
        '--binary',
        '--timing',
        '-Wno-PKGNODECL',
        '-Wno-IGNOREDRETURN',
        '-Wno-WIDTHTRUNC',
        f'+incdir+{include_dir}',
        f'{include_dir}/uvm_pkg.sv'
    ],
    timing_loop=True
)

test.execute()

test.passes()
