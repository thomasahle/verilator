// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_class_param_uvm_driver.h for the primary calling header

#ifndef VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024UNIT_H_
#define VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024UNIT_H_  // guard

#include "verilated.h"


class Vt_class_param_uvm_driver__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_class_param_uvm_driver___024unit final {
  public:

    // INTERNAL VARIABLES
    Vt_class_param_uvm_driver__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_class_param_uvm_driver___024unit() = default;
    ~Vt_class_param_uvm_driver___024unit() = default;
    void ctor(Vt_class_param_uvm_driver__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(Vt_class_param_uvm_driver___024unit);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
