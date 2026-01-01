#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test AXI4-Lite AVIP from mbits-mirafra
#
# Tests AXI4-Lite verification IP using UVM BFM pattern

import vltest_bootstrap
import os

test.scenarios('simulator')

# Use absolute paths resolved at runtime
verilator_root = os.environ.get('VERILATOR_ROOT', os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
include_dir = os.path.join(verilator_root, 'include')
avip_dir = os.path.expanduser('~/repos/mbits-mirafra/axi4Lite_avip')

# Wrapper module that instantiates hdlTop and hvlTop
test.top_filename = "t/t_uvm_axi4lite_avip.v"

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
        "-Wno-STATICVAR",
        "-Wno-REALCVT",
        "-Wno-INITIALDLY",
        "-Wno-COVERIGN",
        f"+incdir+{include_dir}",
        "-f", f"{avip_dir}/sim/verilator.f",
    ],
)

test.execute()

test.passes()
