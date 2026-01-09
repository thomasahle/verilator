// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::Vt_randomize_inline_var_ctl___024unit__03a__03aBoo(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp)
    : Vt_randomize_inline_var_ctl___024unit__03a__03aBar(vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    IData/*31:0*/ unnamedblk2_1__DOT__i;
    unnamedblk2_1__DOT__i = 0;
    ;
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.resize(4U);
    unnamedblk2_1__DOT__i = 0U;
    while ((unnamedblk2_1__DOT__i < Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.size())) {
        Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(unnamedblk2_1__DOT__i) = 1U;
        unnamedblk2_1__DOT__i = ((IData)(1U) + unnamedblk2_1__DOT__i);
    }
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.atWrite(1U) = 0U;
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::__VnoInFunc_randomize(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__1__Vfuncout;
    __Vfunc___VBasicRand__1__Vfuncout = 0;
    // Body
    randomize__Vfuncrtn = 1U;
    randomize__Vfuncrtn = (1U & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__1__Vfuncout);
            }(), __Vfunc___VBasicRand__1__Vfuncout));
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::__VnoInFunc___VBasicRand(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::__VnoInFunc___VBasicRand\n"); );
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
        Vt_randomize_inline_var_ctl___024unit__03a__03aBar::__PVT__one 
            = VL_RANDOM_RNG_I(__Vm_rng);
    }
    if (Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__PVT____Vrandmode.at(3U)) {
        this->__PVT__five = VL_RANDOM_RNG_I(__Vm_rng);
    }
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::_ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__five = 0;
}

Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::~Vt_randomize_inline_var_ctl___024unit__03a__03aBoo() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aBoo>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aBoo::to_string_middle\n"); );
    // Body
    std::string out;
    out += "five:" + VL_TO_STRING(__PVT__five);
    out += ", "+ Vt_randomize_inline_var_ctl___024unit__03a__03aBar::to_string_middle();
    return (out);
}
