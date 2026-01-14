#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test module - SVA sequence on LHS of implication
#
# Tests SVA implication (|->) with sequence expressions on the LHS
# This pattern is used in AHB AVIP assertions: (expr ##n expr) |-> expr
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_assert_seq_lhs_impl.v"

test.compile(verilator_flags2=['--timing', '--assert'])

test.execute()

test.passes()
