// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::Vt_randomize_inline_var_ctl___024unit__03a__03aBaz(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    IData/*31:0*/ unnamedblk2_1__DOT__i;
    unnamedblk2_1__DOT__i = 0;
    this->__PVT__bar = VL_NEW(Vt_randomize_inline_var_ctl___024unit__03a__03aBar, vlSymsp);
    this->__PVT____Vrandmode.resize(2U);
    unnamedblk2_1__DOT__i = 0U;
    while ((unnamedblk2_1__DOT__i < this->__PVT____Vrandmode.size())) {
        this->__PVT____Vrandmode.atWrite(unnamedblk2_1__DOT__i) = 1U;
        unnamedblk2_1__DOT__i = ((IData)(1U) + unnamedblk2_1__DOT__i);
    }
    this->__PVT____Vrandmode.atWrite(0U) = 0U;
    this->__PVT____Vrandmode.atWrite(1U) = 0U;
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::__VnoInFunc_randomize(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__1__Vfuncout;
    __Vfunc___VBasicRand__1__Vfuncout = 0;
    // Body
    randomize__Vfuncrtn = 1U;
    randomize__Vfuncrtn = (1U & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__1__Vfuncout);
            }(), __Vfunc___VBasicRand__1__Vfuncout));
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::__VnoInFunc___VBasicRand(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::__VnoInFunc___VBasicRand\n"); );
    // Locals
    IData/*31:0*/ __Vtask___VBasicRand__2__Vfuncout;
    __Vtask___VBasicRand__2__Vfuncout = 0;
    // Body
    __VBasicRand__Vfuncrtn = 1U;
    if (this->__PVT____Vrandmode.at(0U)) {
        this->__PVT__four = VL_RANDOM_RNG_I(__Vm_rng);
    }
    if (this->__PVT____Vrandmode.at(1U)) {
        if ((VlNull{} != this->__PVT__bar)) {
            __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                      & ([&]() {
                        VL_NULL_CHECK(this->__PVT__bar, "test_regress/t/t_randomize_inline_var_ctl.v", 52)
                                         ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__2__Vfuncout);
                    }(), __Vtask___VBasicRand__2__Vfuncout));
        }
    }
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::_ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__four = 0;
    __PVT____Vrandmode.atDefault() = VL_SCOPED_RAND_RESET_I(1, 9187153985622998249ULL, 14368739129856475828ull);
}

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aBaz>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBaz::to_string_middle\n"); );
    // Body
    std::string out;
    out += "four:" + VL_TO_STRING(__PVT__four);
    out += ", bar:" + VL_TO_STRING(__PVT__bar);
    out += ", __Vrandmode:" + VL_TO_STRING(__PVT____Vrandmode);
    return (out);
}
