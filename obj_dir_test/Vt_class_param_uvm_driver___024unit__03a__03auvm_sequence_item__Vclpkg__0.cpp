// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_class_param_uvm_driver.h for the primary calling header

#include "Vt_class_param_uvm_driver__pch.h"

Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::_ctor_var_reset(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__id = 0;
}

Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::~Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03auvm_sequence_item::to_string_middle\n"); );
    // Body
    std::string out;
    out += "id:" + VL_TO_STRING(__PVT__id);
    return (out);
}
