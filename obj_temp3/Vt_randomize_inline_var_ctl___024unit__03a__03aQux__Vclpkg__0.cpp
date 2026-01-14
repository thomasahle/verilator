// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

Vt_randomize_inline_var_ctl___024unit__03a__03aQux::Vt_randomize_inline_var_ctl___024unit__03a__03aQux(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aQux::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    IData/*31:0*/ unnamedblk2_1__DOT__i;
    unnamedblk2_1__DOT__i = 0;
    this->__PVT__baz = VL_NEW(Vt_randomize_inline_var_ctl___024unit__03a__03aBaz, vlSymsp);
    this->__PVT____Vrandmode.resize(1U);
    unnamedblk2_1__DOT__i = 0U;
    while ((unnamedblk2_1__DOT__i < this->__PVT____Vrandmode.size())) {
        this->__PVT____Vrandmode.atWrite(unnamedblk2_1__DOT__i) = 1U;
        unnamedblk2_1__DOT__i = ((IData)(1U) + unnamedblk2_1__DOT__i);
    }
    this->__PVT____Vrandmode.atWrite(0U) = 0U;
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aQux::__VnoInFunc_randomize(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aQux::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__1__Vfuncout;
    __Vfunc___VBasicRand__1__Vfuncout = 0;
    // Body
    randomize__Vfuncrtn = 1U;
    randomize__Vfuncrtn = (1U & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__1__Vfuncout);
            }(), __Vfunc___VBasicRand__1__Vfuncout));
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aQux::__VnoInFunc___VBasicRand(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aQux::__VnoInFunc___VBasicRand\n"); );
    // Locals
    IData/*31:0*/ __Vtask___VBasicRand__2__Vfuncout;
    __Vtask___VBasicRand__2__Vfuncout = 0;
    // Body
    __VBasicRand__Vfuncrtn = 1U;
    if (this->__PVT____Vrandmode.at(0U)) {
        if ((VlNull{} != this->__PVT__baz)) {
            __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                      & ([&]() {
                        VL_NULL_CHECK(this->__PVT__baz, "test_regress/t/t_randomize_inline_var_ctl.v", 61)
                                         ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__2__Vfuncout);
                    }(), __Vtask___VBasicRand__2__Vfuncout));
        }
    }
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aQux::_ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aQux::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT____Vrandmode.atDefault() = VL_SCOPED_RAND_RESET_I(1, 8497149922059429473ULL, 14368739129856475828ull);
}

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aQux>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aQux::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aQux::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aQux::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aQux::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aQux::to_string_middle\n"); );
    // Body
    std::string out;
    out += "baz:" + VL_TO_STRING(__PVT__baz);
    out += ", __Vrandmode:" + VL_TO_STRING(__PVT____Vrandmode);
    return (out);
}
