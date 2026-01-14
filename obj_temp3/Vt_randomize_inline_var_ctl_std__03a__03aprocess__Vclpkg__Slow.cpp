// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

void Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg___ctor_var_reset(Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg* vlSelf);

void Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg::ctor(Vt_randomize_inline_var_ctl__Syms* symsp, const char* namep) {
    vlSymsp = symsp;
    vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));
    // Reset structure values
    Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg___ctor_var_reset(this);
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

void Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg::dtor() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
