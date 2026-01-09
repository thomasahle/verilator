// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

void Vt_randomize_inline_var_ctl___024root___ctor_var_reset(Vt_randomize_inline_var_ctl___024root* vlSelf);

Vt_randomize_inline_var_ctl___024root::Vt_randomize_inline_var_ctl___024root(Vt_randomize_inline_var_ctl__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    Vt_randomize_inline_var_ctl___024root___ctor_var_reset(this);
}

void Vt_randomize_inline_var_ctl___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vt_randomize_inline_var_ctl___024root::~Vt_randomize_inline_var_ctl___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
