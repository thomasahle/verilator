// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#include "Vt_randomize_inline_var_ctl__pch.h"

Vt_randomize_inline_var_ctl_std__03a__03asemaphore::Vt_randomize_inline_var_ctl_std__03a__03asemaphore(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    this->__PVT__m_keyCount = keyCount;
}

void Vt_randomize_inline_var_ctl_std__03a__03asemaphore::__VnoInFunc_put(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::__VnoInFunc_put\n"); );
    // Body
    this->__PVT__m_keyCount = (this->__PVT__m_keyCount 
                               + keyCount);
}

void Vt_randomize_inline_var_ctl_std__03a__03asemaphore::__VnoInFunc_get(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::__VnoInFunc_get\n"); );
}

void Vt_randomize_inline_var_ctl_std__03a__03asemaphore::__VnoInFunc_try_get(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount, IData/*31:0*/ &try_get__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::__VnoInFunc_try_get\n"); );
    // Body
    {
        if (VL_GTES_III(32, this->__PVT__m_keyCount, keyCount)) {
            this->__PVT__m_keyCount = (this->__PVT__m_keyCount 
                                       - keyCount);
            try_get__Vfuncrtn = 1U;
            goto __Vlabel0;
        }
        try_get__Vfuncrtn = 0U;
        __Vlabel0: ;
    }
}

void Vt_randomize_inline_var_ctl_std__03a__03asemaphore::_ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__m_keyCount = 0;
}

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl_std__03a__03asemaphore>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string Vt_randomize_inline_var_ctl_std__03a__03asemaphore::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string Vt_randomize_inline_var_ctl_std__03a__03asemaphore::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vt_randomize_inline_var_ctl_std__03a__03asemaphore::to_string_middle\n"); );
    // Body
    std::string out;
    out += "m_keyCount:" + VL_TO_STRING(__PVT__m_keyCount);
    return (out);
}
