// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

void Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc_test(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc_test\n"); );
    // Locals
    IData/*31:0*/ __Vtask_randomize__0__Vfuncout;
    __Vtask_randomize__0__Vfuncout = 0;
    IData/*31:0*/ __Vtask_randomize__1__Vfuncout;
    __Vtask_randomize__1__Vfuncout = 0;
    // Body
    IData/*31:0*/ unnamedblk1__DOT__i;
    unnamedblk1__DOT__i = 0;
    VlQueue<CData/*0:0*/> unnamedblk1__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__2;
    unnamedblk1__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__2.atDefault() = 0;
    IData/*31:0*/ unnamedblk1__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i;
    unnamedblk1__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i = 0;
    IData/*31:0*/ unnamedblk2__DOT__i;
    unnamedblk2__DOT__i = 0;
    VlQueue<CData/*0:0*/> unnamedblk2__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__3;
    unnamedblk2__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__3.atDefault() = 0;
    IData/*31:0*/ unnamedblk2__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i;
    unnamedblk2__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i = 0;
    CData/*1:0*/ ok;
    ok = 0;
    ok = 0U;
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__zero = 0x00000064U;
    this->__PVT__one = 0x000000c8U;
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two = 0x0000012cU;
    vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three = 0x00000190U;
    unnamedblk1__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, unnamedblk1__DOT__i)) {
        unnamedblk1__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__2 
            = Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode;
        unnamedblk1__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i = 0U;
        while ((unnamedblk1__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i 
                < Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.size())) {
            Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(unnamedblk1__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i) = 0U;
            unnamedblk1__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i 
                = ((IData)(1U) + unnamedblk1__DOT__unnamedblk2_1__DOT__unnamedblk2_2__DOT__i);
        }
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(2U) = 1U;
        this->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__0__Vfuncout);
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode 
            = unnamedblk1__DOT__unnamedblk2_1__DOT____Vmode_hecea158d__2;
        if (VL_UNLIKELY(((0x00000064U != Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__zero)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 24, "");
        }
        if ((0x000000c8U != this->__PVT__one)) {
            ok = (1U | (IData)(ok));
        }
        if (VL_UNLIKELY(((0x0000012cU != Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 26, "");
        }
        if (VL_UNLIKELY(((0x00000190U != vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 27, "");
        }
        unnamedblk1__DOT__i = ((IData)(1U) + unnamedblk1__DOT__i);
    }
    if (VL_UNLIKELY(((1U & (~ (IData)(ok)))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 29, "");
    }
    ok = 0U;
    if (VL_UNLIKELY(((1U != Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(0U))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 32, "");
    }
    if (VL_UNLIKELY(((1U != Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(2U))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 33, "");
    }
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__zero = 0x000001f4U;
    this->__PVT__one = 0x00000258U;
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two = 0x000002bcU;
    vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three = 0x00000320U;
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(2U) = 0U;
    unnamedblk2__DOT__i = 0U;
    while (VL_GTS_III(32, 0x00000014U, unnamedblk2__DOT__i)) {
        unnamedblk2__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__3 
            = Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode;
        unnamedblk2__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i = 0U;
        while ((unnamedblk2__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i 
                < Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.size())) {
            Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(unnamedblk2__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i) = 0U;
            unnamedblk2__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i 
                = ((IData)(1U) + unnamedblk2__DOT__unnamedblk2_3__DOT__unnamedblk2_4__DOT__i);
        }
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(2U) = 1U;
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(1U) = 1U;
        this->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__1__Vfuncout);
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode 
            = unnamedblk2__DOT__unnamedblk2_3__DOT____Vmode_hecea158d__3;
        if (VL_UNLIKELY(((0x000001f4U != Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__zero)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 41, "");
        }
        if ((0x00000258U != this->__PVT__one)) {
            ok = (1U | (IData)(ok));
        }
        if ((0x000002bcU != Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two)) {
            ok = (2U | (IData)(ok));
        }
        if (VL_UNLIKELY(((0x00000320U != vlSymsp->TOP____024unit__03a__03aBar__Vclpkg.three)))) {
            VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 44, "");
        }
        unnamedblk2__DOT__i = ((IData)(1U) + unnamedblk2__DOT__i);
    }
    if (VL_UNLIKELY(((0U != Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(2U))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 46, "");
    }
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(2U) = 1U;
    if (VL_UNLIKELY(((3U != (IData)(ok))))) {
        VL_STOP_MT("test_regress/t/t_randomize_inline_var_ctl.v", 48, "");
    }
}

Vt_randomize_inline_var_ctl___024unit__03a__03aBar::Vt_randomize_inline_var_ctl___024unit__03a__03aBar(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp)
    : Vt_randomize_inline_var_ctl___024unit__03a__03aFoo(vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    IData/*31:0*/ unnamedblk2_5__DOT__i;
    unnamedblk2_5__DOT__i = 0;
    ;
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.resize(3U);
    unnamedblk2_5__DOT__i = 0U;
    while ((unnamedblk2_5__DOT__i < Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.size())) {
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(unnamedblk2_5__DOT__i) = 1U;
        unnamedblk2_5__DOT__i = ((IData)(1U) + unnamedblk2_5__DOT__i);
    }
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(1U) = 0U;
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc_randomize(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__3__Vfuncout;
    __Vfunc___VBasicRand__3__Vfuncout = 0;
    // Body
    randomize__Vfuncrtn = 1U;
    randomize__Vfuncrtn = (1U & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__3__Vfuncout);
            }(), __Vfunc___VBasicRand__3__Vfuncout));
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc___VBasicRand(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
    if (Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.at(0U)) {
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__zero 
            = VL_RANDOM_RNG_I(__Vm_rng);
    }
    if (Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.at(1U)) {
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two 
            = VL_RANDOM_RNG_I(__Vm_rng);
    }
    if (Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.at(2U)) {
        this->__PVT__one = VL_RANDOM_RNG_I(__Vm_rng);
    }
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc___Vrandwith_h65e6f958__0(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__Vrandwith_h65e6f958__0__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__VnoInFunc___Vrandwith_h65e6f958__0\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__4__Vfuncout;
    __Vfunc___VBasicRand__4__Vfuncout = 0;
    std::string __Vtemp_1;
    std::string __Vtemp_2;
    std::string __Vtemp_3;
    std::string __Vtemp_4;
    // Body
    VlRandomizer randomizer;
    randomizer.set_randmode(Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode);
    __Vtemp_1 = (Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.at(1U)
                  ? std::string("two") : VL_SFORMATF_N_NX("#x%x",0,
                                                          32,
                                                          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two) );
    __Vtemp_2 = (Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.at(1U)
                  ? std::string("two") : VL_SFORMATF_N_NX("#x%x",0,
                                                          32,
                                                          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two) );
    __Vtemp_3 = VL_SFORMATF_N_NX("(__Vbv (bvsgt %@ #x00000bb8))",0,
                                 -1,&(__Vtemp_1)) ;
    __Vtemp_4 = VL_SFORMATF_N_NX("(__Vbv (bvslt %@ #x00000fa0))",0,
                                 -1,&(__Vtemp_2)) ;
    randomizer.hard(VL_SFORMATF_N_NX("(bvand %@ %@)",0,
                                     -1,&(__Vtemp_3),
                                     -1,&(__Vtemp_4)) );
    randomizer.write_var(Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two, 0x0000000000000020ULL, 
                         "two", 0ULL, 1ULL);
    randomizer.write_var(Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT__two, 0x0000000000000020ULL, 
                         "two", 0ULL, 1ULL);
    __Vrandwith_h65e6f958__0__Vfuncrtn = (([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__4__Vfuncout);
            }(), __Vfunc___VBasicRand__4__Vfuncout) 
                                          & randomizer.next(__Vm_rng));
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBar::_ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__one = 0;
}

Vt_randomize_inline_var_ctl___024unit__03a__03aBar::~Vt_randomize_inline_var_ctl___024unit__03a__03aBar() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aBar>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aBar::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aBar::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBar::to_string_middle\n"); );
    // Body
    std::string out;
    out += "one:" + VL_TO_STRING(__PVT__one);
    out += ", "+ Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::to_string_middle();
    return (out);
}
