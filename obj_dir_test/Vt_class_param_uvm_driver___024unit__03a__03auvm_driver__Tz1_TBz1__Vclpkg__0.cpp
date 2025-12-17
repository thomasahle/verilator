// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_class_param_uvm_driver.h for the primary calling header

#include "Vt_class_param_uvm_driver__pch.h"

void Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::__VnoInFunc_set_req(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp, VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03amy_tx> r) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::__VnoInFunc_set_req\n"); );
    // Body
    this->__PVT__req = r;
}

void Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::__VnoInFunc_get_req(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp, VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03amy_tx> &get_req__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::__VnoInFunc_get_req\n"); );
    // Body
    get_req__Vfuncrtn = this->__PVT__req;
}

Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::_ctor_var_reset(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::~Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1() {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::to_string_middle\n"); );
    // Body
    std::string out;
    out += "req:" + VL_TO_STRING(__PVT__req);
    out += ", rsp:" + VL_TO_STRING(__PVT__rsp);
    out += ", seq_item_port:" + VL_TO_STRING(__PVT__seq_item_port);
    return (out);
}
