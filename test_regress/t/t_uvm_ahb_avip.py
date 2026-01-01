#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test AHB AVIP from mbits-mirafra
#
# Tests AHB verification IP using UVM BFM pattern

import vltest_bootstrap
import os

test.scenarios('simulator')

# Use absolute paths resolved at runtime
verilator_root = os.environ.get('VERILATOR_ROOT', os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
include_dir = os.path.join(verilator_root, 'include')
avip_dir = os.path.expanduser('~/repos/mbits-mirafra/ahb_avip')

# Use a dummy top file - the real top is in verilator.f
test.top_filename = "t/t_uvm_ahb_avip.v"

test.compile(
    timing_loop=True,
    verilator_flags2=[
        "--timing",
        "--top-module", "tb_top",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
        "-Wno-ENUMVALUE",
        "-Wno-UNUSEDSIGNAL",
        "-Wno-UNUSEDPARAM",
        "-Wno-ASCRANGE",
        "-Wno-CONSTRAINTIGN",
        "-Wno-MISINDENT",
        "-Wno-CASEINCOMPLETE",
        "-Wno-CASTCONST",
        "-Wno-MULTIDRIVEN",
        f"+incdir+{include_dir}",
        "-f", f"{avip_dir}/sim/verilator.f",
    ],
)

test.execute()

test.passes()
