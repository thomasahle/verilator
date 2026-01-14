// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_class_param_uvm_driver.h for the primary calling header

#ifndef VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024UNIT__03A__03AMY_TX__VCLPKG_H_
#define VERILATED_VT_CLASS_PARAM_UVM_DRIVER___024UNIT__03A__03AMY_TX__VCLPKG_H_  // guard

#include "verilated.h"
class Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item;


class Vt_class_param_uvm_driver__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_class_param_uvm_driver___024unit__03a__03amy_tx__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    Vt_class_param_uvm_driver__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_class_param_uvm_driver___024unit__03a__03amy_tx__Vclpkg() = default;
    ~Vt_class_param_uvm_driver___024unit__03a__03amy_tx__Vclpkg() = default;
    void ctor(Vt_class_param_uvm_driver__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(Vt_class_param_uvm_driver___024unit__03a__03amy_tx__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item__Vclpkg.h"

class Vt_class_param_uvm_driver__Syms;

class Vt_class_param_uvm_driver___024unit__03a__03amy_tx : public Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__data;
  private:
    void _ctor_var_reset(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp);
  public:
    Vt_class_param_uvm_driver___024unit__03a__03amy_tx(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~Vt_class_param_uvm_driver___024unit__03a__03amy_tx();
};

std::string VL_TO_STRING(const VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03amy_tx>& obj);

#endif  // guard
