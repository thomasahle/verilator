// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_class_param_uvm_driver.h for the primary calling header

#include "Vt_class_param_uvm_driver__pch.h"

Vt_class_param_uvm_driver___024unit__03a__03amy_driver::Vt_class_param_uvm_driver___024unit__03a__03amy_driver(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp)
    : Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1(vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_driver::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__local_req = VL_NEW(Vt_class_param_uvm_driver___024unit__03a__03amy_tx, vlSymsp);
    this->__PVT__local_rsp = VL_NEW(Vt_class_param_uvm_driver___024unit__03a__03amy_tx, vlSymsp);
    VL_NULL_CHECK(this->__PVT__local_req, "test_regress/t/t_class_param_uvm_driver.v", 57)->__PVT__data = 0x0000002aU;
    VL_NULL_CHECK(this->__PVT__local_rsp, "test_regress/t/t_class_param_uvm_driver.v", 58)->__PVT__data = 0x00000063U;
}

void Vt_class_param_uvm_driver___024unit__03a__03amy_driver::__VnoInFunc_check(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp, IData/*31:0*/ &check__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_driver::__VnoInFunc_check\n"); );
    // Body
    check__Vfuncrtn = (VL_NULL_CHECK(this->__PVT__local_req, "test_regress/t/t_class_param_uvm_driver.v", 63)
                       ->__PVT__data + VL_NULL_CHECK(this->__PVT__local_rsp, "test_regress/t/t_class_param_uvm_driver.v", 63)
                       ->__PVT__data);
}

void Vt_class_param_uvm_driver___024unit__03a__03amy_driver::_ctor_var_reset(Vt_class_param_uvm_driver__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_driver::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

Vt_class_param_uvm_driver___024unit__03a__03amy_driver::~Vt_class_param_uvm_driver___024unit__03a__03amy_driver() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_driver::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03amy_driver>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_driver::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03amy_driver::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_driver::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_class_param_uvm_driver___024unit__03a__03amy_driver::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_class_param_uvm_driver___024unit__03a__03amy_driver::to_string_middle\n"); );
    // Body
    std::string out;
    out += "local_req:" + VL_TO_STRING(__PVT__local_req);
    out += ", local_rsp:" + VL_TO_STRING(__PVT__local_rsp);
    out += ", axi_write_seq_item_port:" + VL_TO_STRING(__PVT__axi_write_seq_item_port);
    out += ", "+ Vt_class_param_uvm_driver___024unit__03a__03auvm_driver__Tz1_TBz1::to_string_middle();
    return (out);
}
