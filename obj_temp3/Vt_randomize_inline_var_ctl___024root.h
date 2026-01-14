// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vt_randomize_inline_var_ctl.h for the primary calling header

#ifndef VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024ROOT_H_
#define VERILATED_VT_RANDOMIZE_INLINE_VAR_CTL___024ROOT_H_  // guard

#include "verilated.h"
#include "verilated_random.h"
class Vt_randomize_inline_var_ctl___024unit;
class Vt_randomize_inline_var_ctl___024unit__03a__03aBar;
class Vt_randomize_inline_var_ctl___024unit__03a__03aBar__Vclpkg;
class Vt_randomize_inline_var_ctl___024unit__03a__03aBaz;
class Vt_randomize_inline_var_ctl___024unit__03a__03aBaz__Vclpkg;
class Vt_randomize_inline_var_ctl___024unit__03a__03aBoo;
class Vt_randomize_inline_var_ctl___024unit__03a__03aBoo__Vclpkg;
class Vt_randomize_inline_var_ctl___024unit__03a__03aFoo__Vclpkg;
class Vt_randomize_inline_var_ctl___024unit__03a__03aQux;
class Vt_randomize_inline_var_ctl___024unit__03a__03aQux__Vclpkg;
class Vt_randomize_inline_var_ctl_std;
class Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg;
class Vt_randomize_inline_var_ctl_std__03a__03asemaphore__Vclpkg;


class Vt_randomize_inline_var_ctl__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vt_randomize_inline_var_ctl___024root final {
  public:
    // CELLS
    Vt_randomize_inline_var_ctl_std* __PVT__std;
    Vt_randomize_inline_var_ctl___024unit* __PVT____024unit;
    Vt_randomize_inline_var_ctl_std__03a__03asemaphore__Vclpkg* std__03a__03asemaphore__Vclpkg;
    Vt_randomize_inline_var_ctl_std__03a__03aprocess__Vclpkg* std__03a__03aprocess__Vclpkg;
    Vt_randomize_inline_var_ctl___024unit__03a__03aFoo__Vclpkg* __024unit__03a__03aFoo__Vclpkg;
    Vt_randomize_inline_var_ctl___024unit__03a__03aBar__Vclpkg* __024unit__03a__03aBar__Vclpkg;
    Vt_randomize_inline_var_ctl___024unit__03a__03aBaz__Vclpkg* __024unit__03a__03aBaz__Vclpkg;
    Vt_randomize_inline_var_ctl___024unit__03a__03aQux__Vclpkg* __024unit__03a__03aQux__Vclpkg;
    Vt_randomize_inline_var_ctl___024unit__03a__03aBoo__Vclpkg* __024unit__03a__03aBoo__Vclpkg;

    // INTERNAL VARIABLES
    Vt_randomize_inline_var_ctl__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    Vt_randomize_inline_var_ctl___024root(Vt_randomize_inline_var_ctl__Syms* symsp, const char* namep);
    ~Vt_randomize_inline_var_ctl___024root();
    VL_UNCOPYABLE(Vt_randomize_inline_var_ctl___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
