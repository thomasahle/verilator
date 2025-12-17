// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_class_param_uvm_driver.h for the primary calling header

#include "Vt_class_param_uvm_driver__pch.h"

VL_ATTR_COLD void Vt_class_param_uvm_driver___024root___eval_static(Vt_class_param_uvm_driver___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_class_param_uvm_driver___024root___eval_static\n"); );
    Vt_class_param_uvm_driver__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void Vt_class_param_uvm_driver___024root___eval_initial__TOP(Vt_class_param_uvm_driver___024root* vlSelf);

VL_ATTR_COLD void Vt_class_param_uvm_driver___024root___eval_initial(Vt_class_param_uvm_driver___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_class_param_uvm_driver___024root___eval_initial\n"); );
    Vt_class_param_uvm_driver__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    Vt_class_param_uvm_driver___024root___eval_initial__TOP(vlSelf);
}

VL_ATTR_COLD void Vt_class_param_uvm_driver___024root___eval_initial__TOP(Vt_class_param_uvm_driver___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_class_param_uvm_driver___024root___eval_initial__TOP\n"); );
    Vt_class_param_uvm_driver__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    VlClassRef<Vt_class_param_uvm_driver___024unit__03a__03amy_driver> t__DOT__unnamedblk1__DOT__drv;
    IData/*31:0*/ __Vtask_check__1__Vfuncout;
    __Vtask_check__1__Vfuncout = 0;
    // Body
    t__DOT__unnamedblk1__DOT__drv = VL_NEW(Vt_class_param_uvm_driver___024unit__03a__03amy_driver, vlSymsp);
    if (VL_UNLIKELY(((0x0000008dU != ([&]() {
                            VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__drv, "test_regress/t/t_class_param_uvm_driver.v", 71)
                                      ->__VnoInFunc_check(vlSymsp, __Vtask_check__1__Vfuncout);
                        }(), __Vtask_check__1__Vfuncout))))) {
        VL_STOP_MT("test_regress/t/t_class_param_uvm_driver.v", 71, "");
    }
    if (VL_UNLIKELY(((0U != VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__drv, "test_regress/t/t_class_param_uvm_driver.v", 72)
                                          ->__PVT__local_req, "test_regress/t/t_class_param_uvm_driver.v", 72)
                      ->__PVT__id)))) {
        VL_STOP_MT("test_regress/t/t_class_param_uvm_driver.v", 72, "");
    }
    VL_WRITEF_NX("*-* All Finished *-*\n",0);
    VL_FINISH_MT("test_regress/t/t_class_param_uvm_driver.v", 74, "");
}

VL_ATTR_COLD void Vt_class_param_uvm_driver___024root___eval_final(Vt_class_param_uvm_driver___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_class_param_uvm_driver___024root___eval_final\n"); );
    Vt_class_param_uvm_driver__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void Vt_class_param_uvm_driver___024root___eval_settle(Vt_class_param_uvm_driver___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_class_param_uvm_driver___024root___eval_settle\n"); );
    Vt_class_param_uvm_driver__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void Vt_class_param_uvm_driver___024root___ctor_var_reset(Vt_class_param_uvm_driver___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_class_param_uvm_driver___024root___ctor_var_reset\n"); );
    Vt_class_param_uvm_driver__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}
