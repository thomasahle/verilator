// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

VL_ATTR_COLD void Vt_randomize_inline_var_ctl___024root___eval_static(Vt_randomize_inline_var_ctl___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_randomize_inline_var_ctl___024root___eval_static\n"); );
    Vt_randomize_inline_var_ctl__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void Vt_randomize_inline_var_ctl___024root___eval_initial__TOP(Vt_randomize_inline_var_ctl___024root* vlSelf);

VL_ATTR_COLD void Vt_randomize_inline_var_ctl___024root___eval_initial(Vt_randomize_inline_var_ctl___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_randomize_inline_var_ctl___024root___eval_initial\n"); );
    Vt_randomize_inline_var_ctl__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    Vt_randomize_inline_var_ctl___024root___eval_initial__TOP(vlSelf);
}

VL_ATTR_COLD void Vt_randomize_inline_var_ctl___024root___eval_initial__TOP(Vt_randomize_inline_var_ctl___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_randomize_inline_var_ctl___024root___eval_initial__TOP\n"); );
    Vt_randomize_inline_var_ctl__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aBoo> t__DOT__unnamedblk1__DOT__boo;
    VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aBar> t__DOT__unnamedblk1__DOT__bar;
    VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aQux> t__DOT__unnamedblk1__DOT__qux;
    CData/*2:0*/ t__DOT__unnamedblk1__DOT__ok;
    t__DOT__unnamedblk1__DOT__ok = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__i = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__0;
    t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__0.atDefault() = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__i = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__1;
    t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__1.atDefault() = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__i = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT____Vmode_hecea158d__4;
    t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT____Vmode_hecea158d__4.atDefault() = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT__unnamedblk2_6__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT__unnamedblk2_6__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__i = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__5;
    t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__5.atDefault() = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__6;
    t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__6.atDefault() = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_8__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_8__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_9__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_9__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__i = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__7;
    t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__7.atDefault() = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__8;
    t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__8.atDefault() = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_11__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_11__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_12__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_12__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__i = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__9;
    t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__9.atDefault() = 0;
    VlQueue<CData/*0:0*/> t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__10;
    t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__10.atDefault() = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_14__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_14__DOT__i = 0;
    IData/*31:0*/ t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_15__DOT__i;
    t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_15__DOT__i = 0;
    IData/*31:0*/ __Vtask_randomize__3__Vfuncout;
    __Vtask_randomize__3__Vfuncout = 0;
    IData/*31:0*/ __Vtask___Vrandwith_h65e6f958__0__4__Vfuncout;
    __Vtask___Vrandwith_h65e6f958__0__4__Vfuncout = 0;
    IData/*31:0*/ __Vtask_randomize__5__Vfuncout;
    __Vtask_randomize__5__Vfuncout = 0;
    IData/*31:0*/ __Vtask_randomize__6__Vfuncout;
    __Vtask_randomize__6__Vfuncout = 0;
    IData/*31:0*/ __Vtask_randomize__7__Vfuncout;
    __Vtask_randomize__7__Vfuncout = 0;
    IData/*31:0*/ __Vtask_randomize__8__Vfuncout;
    __Vtask_randomize__8__Vfuncout = 0;
    // Body
    t__DOT__unnamedblk1__DOT__boo = VL_NEW(Vt_randomize_inline_var_ctl___024unit__03a__03aBoo, vlSymsp);
    t__DOT__unnamedblk1__DOT__bar = t__DOT__unnamedblk1__DOT__boo;
    t__DOT__unnamedblk1__DOT__qux = VL_NEW(Vt_randomize_inline_var_ctl___024unit__03a__03aQux, vlSymsp);
    t__DOT__unnamedblk1__DOT__ok = 0U;
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 80)->__VnoInFunc_test(vlSymsp);
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 82)->__PVT__zero = 0x000003e8U;
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 83)->__PVT__one = 0x000007d0U;
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 84)->__PVT__two = 0x00000bb8U;
    vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three = 0x00000fa0U;
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__boo, "test_regress/t/t_randomize_inline_var_ctl.v", 86)->__PVT__five = 0x000f423fU;
    t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__i)) {
        t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__0 
            = VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 88)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i 
                < VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 88)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 88)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i);
        }
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 88)->__PVT____Vrandmode.atWrite(1U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 88)->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__3__Vfuncout);
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 88)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__unnamedblk3__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__0;
        if (VL_UNLIKELY(((0x000f423fU != VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__boo, "test_regress/t/t_randomize_inline_var_ctl.v", 89)
                          ->__PVT__five)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 89, "");
        }
        t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__i 
            = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk2__DOT__i);
    }
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 92)->__PVT__zero = 0x000003e8U;
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 93)->__PVT__one = 0x000007d0U;
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 94)->__PVT__two = 0x00000bb8U;
    vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three = 0x00000fa0U;
    VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__boo, "test_regress/t/t_randomize_inline_var_ctl.v", 96)->__PVT__five = 0x000f423fU;
    t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__i)) {
        t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__1 
            = VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 98)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i 
                < VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 98)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 98)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i);
        }
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 98)->__PVT____Vrandmode.atWrite(1U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 98)->__VnoInFunc___Vrandwith_h65e6f958__0(vlSymsp, __Vtask___Vrandwith_h65e6f958__0__4__Vfuncout);
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 98)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__unnamedblk5__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__1;
        if (VL_UNLIKELY(((0x000003e8U != VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 99)
                          ->__PVT__zero)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 99, "");
        }
        if (VL_UNLIKELY(((0x000007d0U != VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 100)
                          ->__PVT__one)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 100, "");
        }
        if (VL_UNLIKELY(((1U & (~ (VL_LTS_III(32, 0x00000bb8U, VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 101)
                                              ->__PVT__two) 
                                   && VL_GTS_III(32, 0x00000fa0U, VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 101)
                                                 ->__PVT__two))))))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 101, "");
        }
        if (VL_UNLIKELY(((0x00000fa0U != vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 102, "");
        }
        if (VL_UNLIKELY(((0x000f423fU != VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__boo, "test_regress/t/t_randomize_inline_var_ctl.v", 103)
                          ->__PVT__five)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 103, "");
        }
        t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__i 
            = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk4__DOT__i);
    }
    VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 106)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 106)
                  ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 106)->__PVT__zero = 0x00001388U;
    VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 107)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 107)
                  ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 107)->__PVT__one = 0x00001770U;
    VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 108)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 108)
                  ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 108)->__PVT__two = 0x00001b58U;
    vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three = 0x00001f40U;
    VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 110)
                  ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 110)->__PVT__four = 0x00002328U;
    t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__i)) {
        t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT____Vmode_hecea158d__4 
            = VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 112)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT__unnamedblk2_6__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT__unnamedblk2_6__DOT__i 
                < VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 112)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 112)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT__unnamedblk2_6__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT__unnamedblk2_6__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT__unnamedblk2_6__DOT__i);
        }
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 112)->__PVT____Vrandmode.atWrite(0U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 112)->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__5__Vfuncout);
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 112)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__unnamedblk2_5__DOT____Vmode_hecea158d__4;
        if (VL_UNLIKELY(((0x00001388U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 113)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 113)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 113)
                          ->__PVT__zero)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 113, "");
        }
        if (VL_UNLIKELY(((0x00001770U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 114)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 114)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 114)
                          ->__PVT__one)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 114, "");
        }
        if (VL_UNLIKELY(((0x00001b58U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 115)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 115)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 115)
                          ->__PVT__two)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 115, "");
        }
        if (VL_UNLIKELY(((0x00001f40U != vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 116, "");
        }
        if (VL_UNLIKELY(((0x00002328U != VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 117)
                                                       ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 117)
                          ->__PVT__four)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 117, "");
        }
        t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__i 
            = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk6__DOT__i);
    }
    t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__i)) {
        t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__5 
            = VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
                            ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_8__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_8__DOT__i 
                < VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
                          ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 120)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_8__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_8__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_8__DOT__i);
        }
        t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__6 
            = VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_9__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_9__DOT__i 
                < VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_9__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_9__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT__unnamedblk2_9__DOT__i);
        }
        VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
                      ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 120)->__PVT____Vrandmode.atWrite(1U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)->__PVT____Vrandmode.atWrite(0U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__6__Vfuncout);
        VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)
                      ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 120)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__5;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 120)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__unnamedblk2_7__DOT____Vmode_hecea158d__6;
        if ((0x00001388U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 121)
                                                        ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 121)
                                          ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 121)
             ->__PVT__zero)) {
            t__DOT__unnamedblk1__DOT__ok = (1U | (IData)(t__DOT__unnamedblk1__DOT__ok));
        }
        if ((0x00001770U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 122)
                                                        ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 122)
                                          ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 122)
             ->__PVT__one)) {
            t__DOT__unnamedblk1__DOT__ok = (2U | (IData)(t__DOT__unnamedblk1__DOT__ok));
        }
        if (VL_UNLIKELY(((0x00001b58U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 123)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 123)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 123)
                          ->__PVT__two)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 123, "");
        }
        if (VL_UNLIKELY(((0x00001f40U != vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 124, "");
        }
        if (VL_UNLIKELY(((0x00002328U != VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 125)
                                                       ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 125)
                          ->__PVT__four)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 125, "");
        }
        t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__i 
            = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk7__DOT__i);
    }
    if (VL_UNLIKELY(((1U & (~ (IData)(t__DOT__unnamedblk1__DOT__ok)))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 127, "");
    }
    if (VL_UNLIKELY(((1U & (~ ((IData)(t__DOT__unnamedblk1__DOT__ok) 
                               >> 1U)))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 128, "");
    }
    t__DOT__unnamedblk1__DOT__ok = 0U;
    VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 130)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 130)
                  ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 130)->__PVT__zero = 0x00002710U;
    VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 131)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 131)
                  ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 131)->__PVT__one = 0x00004e20U;
    t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__i)) {
        t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__7 
            = VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
                            ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_11__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_11__DOT__i 
                < VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
                          ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 133)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_11__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_11__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_11__DOT__i);
        }
        t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__8 
            = VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_12__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_12__DOT__i 
                < VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_12__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_12__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT__unnamedblk2_12__DOT__i);
        }
        VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
                      ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 133)->__PVT____Vrandmode.atWrite(0U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)->__PVT____Vrandmode.atWrite(0U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__7__Vfuncout);
        VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)
                      ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 133)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__7;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 133)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__unnamedblk2_10__DOT____Vmode_hecea158d__8;
        if (VL_UNLIKELY(((0x00002710U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 134)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 134)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 134)
                          ->__PVT__zero)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 134, "");
        }
        if (VL_UNLIKELY(((0x00004e20U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 135)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 135)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 135)
                          ->__PVT__one)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 135, "");
        }
        if (VL_UNLIKELY(((0x00001b58U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 136)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 136)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 136)
                          ->__PVT__two)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 136, "");
        }
        if (VL_UNLIKELY(((0x00001f40U != vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 137, "");
        }
        if ((0x00002328U != VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 138)
                                          ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 138)
             ->__PVT__four)) {
            t__DOT__unnamedblk1__DOT__ok = (1U | (IData)(t__DOT__unnamedblk1__DOT__ok));
        }
        t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__i 
            = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk8__DOT__i);
    }
    if (VL_UNLIKELY(((1U & (~ (IData)(t__DOT__unnamedblk1__DOT__ok)))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 140, "");
    }
    t__DOT__unnamedblk1__DOT__ok = 0U;
    VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 142)
                  ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 142)->__PVT__four = 0x00007530U;
    t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__i)) {
        t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__9 
            = VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                            ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_14__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_14__DOT__i 
                < VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                                ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                          ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_14__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_14__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_14__DOT__i);
        }
        t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__10 
            = VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
            ->__PVT____Vrandmode;
        t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_15__DOT__i = 0U;
        while ((t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_15__DOT__i 
                < VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                ->__PVT____Vrandmode.size())) {
            VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode.atWrite(t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_15__DOT__i) = 0U;
            t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_15__DOT__i 
                = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT__unnamedblk2_15__DOT__i);
        }
        VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                      ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode.atWrite(1U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode.atWrite(0U) = 1U;
        VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                      ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode.atWrite(0U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode.atWrite(0U) = 1U;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__8__Vfuncout);
        VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)
                      ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__9;
        VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 144)->__PVT____Vrandmode 
            = t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__unnamedblk2_13__DOT____Vmode_hecea158d__10;
        if ((0x00002710U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 145)
                                                        ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 145)
                                          ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 145)
             ->__PVT__zero)) {
            t__DOT__unnamedblk1__DOT__ok = (1U | (IData)(t__DOT__unnamedblk1__DOT__ok));
        }
        if ((0x00004e20U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 146)
                                                        ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 146)
                                          ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 146)
             ->__PVT__one)) {
            t__DOT__unnamedblk1__DOT__ok = (2U | (IData)(t__DOT__unnamedblk1__DOT__ok));
        }
        if (VL_UNLIKELY(((0x00001b58U != VL_NULL_CHECK(VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 147)
                                                                     ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 147)
                                                       ->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 147)
                          ->__PVT__two)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 147, "");
        }
        if (VL_UNLIKELY(((0x00001f40U != vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 148, "");
        }
        if ((0x00007530U != VL_NULL_CHECK(VL_NULL_CHECK(t__DOT__unnamedblk1__DOT__qux, "test_regress/t/t_randomize_inline_var_ctl.v", 149)
                                          ->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 149)
             ->__PVT__four)) {
            t__DOT__unnamedblk1__DOT__ok = (4U | (IData)(t__DOT__unnamedblk1__DOT__ok));
        }
        t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__i 
            = ((IData)(1U) + t__DOT__unnamedblk1__DOT__unnamedblk9__DOT__i);
    }
    if (VL_UNLIKELY(((7U != (IData)(t__DOT__unnamedblk1__DOT__ok))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 151, "");
    }
    VL_WRITEF_NX("*-* All Finished *-*\n",0);
    VL_FINISH_MT("test_regress/t/t_randomize_inline_var_ctl.v", 154, "");
}

VL_ATTR_COLD void Vt_randomize_inline_var_ctl___024root___eval_final(Vt_randomize_inline_var_ctl___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_randomize_inline_var_ctl___024root___eval_final\n"); );
    Vt_randomize_inline_var_ctl__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void Vt_randomize_inline_var_ctl___024root___eval_settle(Vt_randomize_inline_var_ctl___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_randomize_inline_var_ctl___024root___eval_settle\n"); );
    Vt_randomize_inline_var_ctl__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void Vt_randomize_inline_var_ctl___024root___ctor_var_reset(Vt_randomize_inline_var_ctl___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vt_randomize_inline_var_ctl___024root___ctor_var_reset\n"); );
    Vt_randomize_inline_var_ctl__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}
