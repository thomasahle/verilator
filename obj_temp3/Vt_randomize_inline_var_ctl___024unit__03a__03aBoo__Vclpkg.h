// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#ifndef VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024UNIT__03A__03ABOO__VCLPKG_H_
#define VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024UNIT__03A__03ABOO__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_random.h"
class Vt_randomize_inline_var_ctl___024unit__03a__03aBar;


class Vt_randomize_inline_var_ctl__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_randomize_inline_var_ctl___024unit__03a__03aBoo__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    Vt_randomize_inline_var_ctl__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_randomize_inline_var_ctl___024unit__03a__03aBoo__Vclpkg() = default;
    ~Vt_randomize_inline_var_ctl___024unit__03a__03aBoo__Vclpkg() = default;
    void ctor(Vt_randomize_inline_var_ctl__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(Vt_randomize_inline_var_ctl___024unit__03a__03aBoo__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "Vt_randomize_inline_var_ctl___024unit__03a__03aBar__Vclpkg.h"

class Vt_randomize_inline_var_ctl__Syms;

class Vt_randomize_inline_var_ctl___024unit__03a__03aBoo : public Vt_randomize_inline_var_ctl___024unit__03a__03aBar {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__five;
    virtual void __VnoInFunc___VBasicRand(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc_randomize(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp);
  public:
    Vt_randomize_inline_var_ctl___024unit__03a__03aBoo(Vt_randomize_inline_var_ctl__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~Vt_randomize_inline_var_ctl___024unit__03a__03aBoo();
};

std::string VL_TO_STRING(const VlClassRef<Vt_randomize_inline_var_ctl___024unit__03a__03aBoo>& obj);

#endif  // guard
