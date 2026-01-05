#!/bin/bash
# Run AVIP tests with Verilator
# Usage: ./run_avip.sh [avip_name] or ./run_avip.sh all

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERILATOR_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
VERILATOR="$VERILATOR_ROOT/bin/verilator"
MBITS_DIR="$HOME/repos/mbits-mirafra"
UVM_HOME="$VERILATOR_ROOT/include"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Available AVIPs
AVIPS=(apb spi axi4 ahb i3c i2s axi4Lite jtag uart)

# AVIPs known to work
WORKING_AVIPS=(apb spi axi4 ahb i3c i2s)

# AVIPs with known issues (AVIP bugs, not Verilator bugs)
KNOWN_ISSUES=(axi4Lite jtag uart)

# Function to get top module names for an AVIP (hdl_module:hvl_module)
get_top_modules() {
    case "$1" in
        apb|axi4|i3c|jtag|uart) echo "hdl_top:hvl_top" ;;
        spi) echo "SpiHdlTop:SpiHvlTop" ;;
        ahb) echo "HdlTop:HvlTop" ;;
        i2s) echo "hdlTop:hvlTop" ;;
        axi4Lite) echo "Axi4LiteHdlTop:Axi4LiteHvlTop" ;;
        *) echo "hdl_top:hvl_top" ;;  # default
    esac
}

run_avip() {
    local avip=$1
    local avip_dir="$MBITS_DIR/${avip}_avip"
    local sim_dir="$avip_dir/sim"
    local compile_f=""

    if [[ ! -d "$avip_dir" ]]; then
        echo -e "${RED}AVIP directory not found: $avip_dir${NC}"
        return 1
    fi

    # Find compile.f file (handles various naming conventions)
    # Try: apb_compile.f, SpiCompile.f, I2sCompile.f, compile.f
    local compile_f_name=""
    if [[ -f "$sim_dir/${avip}_compile.f" ]]; then
        compile_f_name="${avip}_compile.f"
    else
        # Try CamelCase versions
        for f in "$sim_dir"/*[Cc]ompile.f; do
            if [[ -f "$f" ]]; then
                compile_f_name="$(basename "$f")"
                break
            fi
        done
    fi

    if [[ -z "$compile_f_name" ]]; then
        echo -e "${RED}No compile.f found for $avip${NC}"
        return 1
    fi
    compile_f="$sim_dir/$compile_f_name"

    echo -e "${YELLOW}Running $avip AVIP...${NC}"

    # Build in verilator repo's build/ directory (not in AVIP project)
    local build_dir="$VERILATOR_ROOT/build/verilator/${avip}_avip"
    mkdir -p "$build_dir"
    pushd "$build_dir" > /dev/null

    # Clean old obj_dir
    rm -rf obj_dir

    # Get module names for this AVIP
    local modules="$(get_top_modules "$avip")"
    local hdl_mod="${modules%%:*}"
    local hvl_mod="${modules##*:}"

    # Create wrapper top that instantiates both hdl and hvl tops
    cat > ${avip}_top.sv << EOF
// Wrapper top module that instantiates both HDL and HVL tops
module ${avip}_top;
  ${hdl_mod} u_hdl_top();
  ${hvl_mod} u_hvl_top();
endmodule
EOF

    # Convert relative paths in compile.f to absolute paths
    # The compile.f uses paths like ../../src relative to sim/ directory
    sed "s|^\.\./\.\./|${avip_dir}/|g; s|+incdir+\.\./\.\./|+incdir+${avip_dir}/|g" \
        "$compile_f" > compile.f

    # Compile with Verilator
    echo "  Compiling..."
    "$VERILATOR" --binary --timing -j 4 \
        -DUVM_NO_DPI -DUVM_REGEX_NO_DPI \
        "+incdir+$UVM_HOME" \
        "$UVM_HOME/uvm_pkg.sv" \
        -f compile.f \
        ${avip}_top.sv \
        -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND -Wno-CASEINCOMPLETE \
        -Wno-ZERODLY -Wno-TIMESCALEMOD -Wno-PINDUP \
        -Wno-ENUMVALUE -Wno-CASTCONST \
        -Wno-fatal --top ${avip}_top \
        2>&1 | tee compile.log
    if [[ ${PIPESTATUS[0]} -ne 0 ]]; then
        echo -e "${RED}  COMPILE FAILED${NC}"
        popd > /dev/null
        return 1
    fi

    # Run the test
    echo "  Running..."
    timeout 120 obj_dir/V${avip}_top 2>&1 | tee run.log
    if [[ ${PIPESTATUS[0]} -ne 0 ]]; then
        echo -e "${RED}  RUN FAILED${NC}"
        popd > /dev/null
        return 1
    fi

    # Check for UVM_ERROR or UVM_FATAL in output
    if grep -q "UVM_ERROR\|UVM_FATAL" run.log; then
        echo -e "${RED}  TEST FAILED (UVM errors/fatals found)${NC}"
        popd > /dev/null
        return 1
    fi

    echo -e "${GREEN}  PASSED${NC}"
    popd > /dev/null
    return 0
}

run_all() {
    local passed=0
    local failed=0
    local skipped=0

    for avip in "${WORKING_AVIPS[@]}"; do
        if run_avip "$avip"; then
            ((passed++))
        else
            ((failed++))
        fi
        echo ""
    done

    echo "=========================================="
    echo "Known Issue AVIPs (skipped):"
    for avip in "${KNOWN_ISSUES[@]}"; do
        echo "  - $avip"
        ((skipped++))
    done

    echo ""
    echo "=========================================="
    echo -e "Results: ${GREEN}$passed passed${NC}, ${RED}$failed failed${NC}, ${YELLOW}$skipped skipped${NC}"
    echo "=========================================="

    return $failed
}

# Main
if [[ $# -eq 0 || "$1" == "all" ]]; then
    run_all
else
    run_avip "$1"
fi
