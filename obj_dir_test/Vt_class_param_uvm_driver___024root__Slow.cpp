// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_class_param_uvm_driver.h for the primary calling header

#include "Vt_class_param_uvm_driver__pch.h"

void Vt_class_param_uvm_driver___024root___ctor_var_reset(Vt_class_param_uvm_driver___024root* vlSelf);

Vt_class_param_uvm_driver___024root::Vt_class_param_uvm_driver___024root(Vt_class_param_uvm_driver__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    Vt_class_param_uvm_driver___024root___ctor_var_reset(this);
}

void Vt_class_param_uvm_driver___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vt_class_param_uvm_driver___024root::~Vt_class_param_uvm_driver___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
