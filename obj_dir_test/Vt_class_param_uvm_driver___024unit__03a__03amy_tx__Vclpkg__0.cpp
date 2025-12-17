// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_class_param_uvm_driver.h for the primary calling header

#include "Vt_class_param_uvm_driver__pch.h"

Vt_class_param_uvm_driver___024unit__03a__03amy_tx::Vt_class_param_uvm_driver___024unit__03a__03amy_tx(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp)
    : Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item(vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_tx::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void Vt_class_param_uvm_driver___024unit__03a__03amy_tx::_ctor_var_reset(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_tx::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__data = 0;
}

Vt_class_param_uvm_driver___024unit__03a__03amy_tx::~Vt_class_param_uvm_driver___024unit__03a__03amy_tx() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_tx::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03amy_tx>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_tx::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03amy_tx::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_tx::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03amy_tx::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_tx::to_string_middle\n"); );
    // Body
    std::string out;
    out += "data:" + VL_TO_STRING(__PVT__data);
    out += ", "+ Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::to_string_middle();
    return (out);
}
