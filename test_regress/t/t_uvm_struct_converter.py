#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test struct-to-class converter pattern for BFM communication
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary --timing -Wno-PKGNODECL -Wno-IMPLICITSTATIC -Wno-CONSTRAINTIGN -Wno-MISINDENT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND +incdir+../include ../include/uvm_pkg.sv'])

test.execute()

test.passes()
