// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#ifndef VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL_STD__03A__03ASEMAPHORE__VCLPKG_H_
#define VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL_STD__03A__03ASEMAPHORE__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_random.h"


class Vt_randomize_inline_var_ctl__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_randomize_inline_var_ctl_std__03a__03asemaphore__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    Vt_randomize_inline_var_ctl__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_randomize_inline_var_ctl_std__03a__03asemaphore__Vclpkg() = default;
    ~Vt_randomize_inline_var_ctl_std__03a__03asemaphore__Vclpkg() = default;
    void ctor(Vt_randomize_inline_var_ctl__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(Vt_randomize_inline_var_ctl_std__03a__03asemaphore__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class Vt_randomize_inline_var_ctl__Syms;

class Vt_randomize_inline_var_ctl_std__03a__03asemaphore : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_keyCount;
    void __VnoInFunc_get(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount);
    void __VnoInFunc_put(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount);
    void __VnoInFunc_try_get(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount, IData/*31:0*/ &try_get__Vfuncrtn);
  private:
    void _ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp);
  public:
    Vt_randomize_inline_var_ctl_std__03a__03asemaphore(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ keyCount);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~Vt_randomize_inline_var_ctl_std__03a__03asemaphore() {}
};

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl_std__03a__03asemaphore>& obj);

#endif  // guard
