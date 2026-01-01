#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test for UVM callbacks iteration
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=[
    '--timing', '-Wno-PKGNODECL', '-Wno-IMPLICITSTATIC', '-Wno-CONSTRAINTIGN',
    '-Wno-MISINDENT', '-Wno-CASEINCOMPLETE', '-Wno-CASTCONST', '-Wno-SYMRSVDWORD',
    '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC', '-Wno-REALCVT', '-Wno-ZERODLY',
    '-Wno-ENUMVALUE', '-Wno-IGNOREDRETURN', '-Wno-NEWERSTD', '-Wno-SIDEEFFECT',
    '+incdir+../include', '../include/uvm_pkg.sv'
])

test.execute()

test.passes()
