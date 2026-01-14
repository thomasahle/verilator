// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::Vt_randomize_inline_var_ctl___024unit__03a__03aFoo(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    IData/*31:0*/ unnamedblk2_1__DOT__i;
    unnamedblk2_1__DOT__i = 0;
    this->__PVT____Vrandmode.resize(2U);
    unnamedblk2_1__DOT__i = 0U;
    while ((unnamedblk2_1__DOT__i < this->__PVT____Vrandmode.size())) {
        this->__PVT____Vrandmode.atWrite(unnamedblk2_1__DOT__i) = 1U;
        unnamedblk2_1__DOT__i = ((IData)(1U) + unnamedblk2_1__DOT__i);
    }
    this->__PVT____Vrandmode.atWrite(1U) = 0U;
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__VnoInFunc_randomize(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__0__Vfuncout;
    __Vfunc___VBasicRand__0__Vfuncout = 0;
    // Body
    randomize__Vfuncrtn = 1U;
    randomize__Vfuncrtn = (1U & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__0__Vfuncout);
            }(), __Vfunc___VBasicRand__0__Vfuncout));
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__VnoInFunc___VBasicRand(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
    if (this->__PVT____Vrandmode.at(0U)) {
        this->__PVT__zero = VL_RANDOM_RNG_I(__Vm_rng);
    }
    if (this->__PVT____Vrandmode.at(1U)) {
        this->__PVT__two = VL_RANDOM_RNG_I(__Vm_rng);
    }
}

void Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::_ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__zero = 0;
    __PVT__two = 0;
    __PVT____Vrandmode.atDefault() = VL_SCOPED_RAND_RESET_I(1, 14012272330885125806ULL, 14368739129856475828ull);
}

Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::~Vt_randomize_inline_var_ctl___024unit__03a__03aFoo() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aFoo>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl___024unit__03a__03aFoo::to_string_middle\n"); );
    // Body
    std::string out;
    out += "zero:" + VL_TO_STRING(__PVT__zero);
    out += ", two:" + VL_TO_STRING(__PVT__two);
    out += ", __Vrandmode:" + VL_TO_STRING(__PVT____Vrandmode);
    return (out);
}
