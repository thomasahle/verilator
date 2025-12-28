#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test UVM Register Abstraction Layer
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(
    v_flags2=['+incdir+../include', '../include/uvm_pkg.sv'],
    verilator_flags2=[
        '--binary',
        '--timing',
        '-Wno-PKGNODECL',
        '-Wno-WIDTHEXPAND',
        '-Wno-WIDTHTRUNC',
        '-Wno-CASTCONST',
        '-Wno-IGNOREDRETURN',
        '-Wno-SIDEEFFECT',
    ],
    timing_loop=True,
)

test.execute()

test.passes()
