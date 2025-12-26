#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test UVM sequence mechanism
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("Requires solver")

test.compile(
    v_flags2=['+incdir+../include', '../include/uvm_pkg.sv'],
    verilator_flags2=['--timing', '-Wno-PKGNODECL', '-Wno-IMPLICITSTATIC',
                      '-Wno-CONSTRAINTIGN', '-Wno-MISINDENT', '-Wno-CASEINCOMPLETE',
                      '-Wno-CASTCONST', '-Wno-SYMRSVDWORD', '-Wno-WIDTHEXPAND',
                      '-Wno-WIDTHTRUNC', '-Wno-REALCVT', '-Wno-ZERODLY',
                      '-Wno-ENUMVALUE', '-Wno-UNOPTFLAT'],
    timing_loop=True,
)

test.execute()

test.passes()
