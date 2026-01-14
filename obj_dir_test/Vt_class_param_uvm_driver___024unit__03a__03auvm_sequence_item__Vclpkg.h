// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_class_param_uvm_driver.h for the primary calling header

#ifndef VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024UNIT__03A__03AUVM_SEQUENCE_ITEM__VCLPKG_H_
#define VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024UNIT__03A__03AUVM_SEQUENCE_ITEM__VCLPKG_H_  // guard

#include "verilated.h"


class Vt_class_param_uvm_driver__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    Vt_class_param_uvm_driver__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item__Vclpkg() = default;
    ~Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item__Vclpkg() = default;
    void ctor(Vt_class_param_uvm_driver__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class Vt_class_param_uvm_driver__Syms;

class Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__id;
  private:
    void _ctor_var_reset(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp);
  public:
    Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item();
};

std::string VL_TO_STRING(const VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item>& obj);

#endif  // guard
