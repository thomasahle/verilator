// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#ifndef VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024UNIT_H_
#define VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024UNIT_H_  // guard

#include "verilated.h"
#include "verilated_random.h"


class Vt_randomize_inline_var_ctl__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_randomize_inline_var_ctl___024unit final {
  public:

    // INTERNAL VARIABLES
    Vt_randomize_inline_var_ctl__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_randomize_inline_var_ctl___024unit() = default;
    ~Vt_randomize_inline_var_ctl___024unit() = default;
    void ctor(Vt_randomize_inline_var_ctl__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(Vt_randomize_inline_var_ctl___024unit);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
