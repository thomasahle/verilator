// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#ifndef VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024UNIT__03A__03ABAR__VCLPKG_H_
#define VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024UNIT__03A__03ABAR__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_random.h"
class Vt_randomize_inline_var_ctl___024unit__03a__03aFoo;


class Vt_randomize_inline_var_ctl__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_randomize_inline_var_ctl___024unit__03a__03aBar__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ three;

    // INTERNAL VARIABLES
    Vt_randomize_inline_var_ctl__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_randomize_inline_var_ctl___024unit__03a__03aBar__Vclpkg() = default;
    ~Vt_randomize_inline_var_ctl___024unit__03a__03aBar__Vclpkg() = default;
    void ctor(Vt_randomize_inline_var_ctl__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(Vt_randomize_inline_var_ctl___024unit__03a__03aBar__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "Vt_randomize_inline_var_ctl___024unit__03a__03aFoo__Vclpkg.h"

class Vt_randomize_inline_var_ctl__Syms;

class Vt_randomize_inline_var_ctl___024unit__03a__03aBar : public Vt_randomize_inline_var_ctl___024unit__03a__03aFoo {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__one;
    virtual void __VnoInFunc___VBasicRand(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    void __VnoInFunc___Vrandwith_h65e6f958__0(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__Vrandwith_h65e6f958__0__Vfuncrtn);
    virtual void __VnoInFunc_randomize(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    void __VnoInFunc_test(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp);
  public:
    Vt_randomize_inline_var_ctl___024unit__03a__03aBar(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~Vt_randomize_inline_var_ctl___024unit__03a__03aBar();
};

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aBar>& obj);

#endif  // guard
