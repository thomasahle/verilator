// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_class_param_uvm_driver.h for the primary calling header

#ifndef VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024ROOT_H_
#define VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024ROOT_H_  // guard

#include "verilated.h"
class Vt_class_param_uvm_driver___024unit;
class Vt_class_param_uvm_driver___024unit__03a__03amy_driver;
class Vt_class_param_uvm_driver___024unit__03a__03amy_driver__Vclpkg;
class Vt_class_param_uvm_driver___024unit__03a__03amy_tx;
class Vt_class_param_uvm_driver___024unit__03a__03amy_tx__Vclpkg;
class Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1__Vclpkg;
class Vt_class_param_uvm_driver___024unit__03a__03auvm_seq_item_pull_port__pi1__Vclpkg;
class Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item__Vclpkg;


class Vt_class_param_uvm_driver__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_class_param_uvm_driver___024root final {
  public:
    // CELLS
    Vt_class_param_uvm_driver___024unit* __PVT____024unit;
    Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item__Vclpkg* __024unit__03a__03auvm_sequence_item__Vclpkg;
    Vt_class_param_uvm_driver___024unit__03a__03amy_tx__Vclpkg* __024unit__03a__03amy_tx__Vclpkg;
    Vt_class_param_uvm_driver___024unit__03a__03amy_driver__Vclpkg* __024unit__03a__03amy_driver__Vclpkg;
    Vt_class_param_uvm_driver___024unit__03a__03auvm_seq_item_pull_port__pi1__Vclpkg* __024unit__03a__03auvm_seq_item_pull_port__pi1__Vclpkg;
    Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1__Vclpkg* __024unit__03a__03auvm_driver__Tz1_TBz1__Vclpkg;

    // INTERNAL VARIABLES
    Vt_class_param_uvm_driver__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_class_param_uvm_driver___024root(Vt_class_param_uvm_driver__Syms* symsp, const char* namep);
    ~Vt_class_param_uvm_driver___024root();
    VL_UNCOPYABLE(Vt_class_param_uvm_driver___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
