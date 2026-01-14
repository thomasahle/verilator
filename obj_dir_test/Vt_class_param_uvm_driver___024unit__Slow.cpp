// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_class_param_uvm_driver.h for the primary calling header

#include "Vt_class_param_uvm_driver__pch.h"

void Vt_class_param_uvm_driver___024unit___ctor_var_reset(Vt_class_param_uvm_driver___024unit* vlSelf);

void Vt_class_param_uvm_driver___024unit::ctor(Vt_class_param_uvm_driver__Syms* symsp, const char* namep) {
    vlSymsp = symsp;
    vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));
    // Reset structure values
    Vt_class_param_uvm_driver___024unit___ctor_var_reset(this);
}

void Vt_class_param_uvm_driver___024unit::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

void Vt_class_param_uvm_driver___024unit::dtor() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
