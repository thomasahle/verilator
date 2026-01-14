// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

void Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg::__VnoInFunc_self(VlProcessRef vlProcess, Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, VlClassRef<Vt_randomize_inline_var_ctl_std__03a__03aprocess> &self__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg::__VnoInFunc_self\n"); );
    // Body
    VlClassRef<Vt_randomize_inline_var_ctl_std__03a__03aprocess> p;
    p = VL_NEW(Vt_randomize_inline_var_ctl_std__03a__03aprocess, vlSymsp);
    self__Vfuncrtn = p;
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg::__VnoInFunc_killQueue(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, VlQueue<VlClassRef<Vt_randomize_inline_var_ctl_std__03a__03aprocess>> &processQueue) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg::__VnoInFunc_killQueue\n"); );
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_set_status(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ s) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_set_status\n"); );
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_status(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &status__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_status\n"); );
    // Body
    status__Vfuncrtn = 1U;
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_kill(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_kill\n"); );
    // Body
    this->__VnoInFunc_set_status(vlSymsp, 4U);
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_suspend(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_suspend\n"); );
    // Body
    VL_WRITEF_NX("[%0t] %%Error: verilated_std.sv:168: Assertion failed in %Nstd.process.suspend: std::process::suspend() not supported\n",0,
                 64,VL_TIME_UNITED_Q(1),-12,vlSymsp->name());
    VL_STOP_MT("/Users/ahle/repos/verilator/include/verilated_std.sv", 168, "");
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_resume(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_resume\n"); );
    // Body
    this->__VnoInFunc_set_status(vlSymsp, 1U);
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_get_randstate(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, std::string &get_randstate__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_get_randstate\n"); );
    // Body
    std::string s;
    s = VL_CVT_PACK_STR_NI(
// $c expression at /Users/ahle/repos/verilator/include/verilated_std.sv:230:26
0
    );

// $c statement at /Users/ahle/repos/verilator/include/verilated_std.sv:232:7
    s = this->__PVT__m_process->randstate();
    get_randstate__Vfuncrtn = s;
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_set_randstate(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, std::string s) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::__VnoInFunc_set_randstate\n"); );
    // Body

// $c statement at /Users/ahle/repos/verilator/include/verilated_std.sv:237:7
    this->__PVT__m_process->randstate(s);
}

Vt_randomize_inline_var_ctl_std__03a__03aprocess::Vt_randomize_inline_var_ctl_std__03a__03aprocess(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess::_ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl_std__03a__03aprocess>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_randomize_inline_var_ctl_std__03a__03aprocess::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_randomize_inline_var_ctl_std__03a__03aprocess::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03aprocess::to_string_middle\n"); );
    // Body
    std::string out;
    out += "m_process:" + VL_TO_STRING(__PVT__m_process);
    return (out);
}
