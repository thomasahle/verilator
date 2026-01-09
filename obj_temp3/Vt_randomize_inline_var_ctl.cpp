// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vt_randomize_inline_var_ctl__pch.h"

//============================================================
// Constructors

Vt_randomize_inline_var_ctl::Vt_randomize_inline_var_ctl(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vt_randomize_inline_var_ctl__Syms(contextp(), _vcname__, this)}
    , __PVT__std{vlSymsp->TOP.__PVT__std}
    , __PVT____024unit{vlSymsp->TOP.__PVT____024unit}
    , std__03a__03asemaphore__Vclpkg{vlSymsp->TOP.std__03a__03asemaphore__Vclpkg}
    , std__03a__03aprocess__Vclpkg{vlSymsp->TOP.std__03a__03aprocess__Vclpkg}
    , __024unit__03a__03aFoo__Vclpkg{vlSymsp->TOP.__024unit__03a__03aFoo__Vclpkg}
    , __024unit__03a__03aBar__Vclpkg{vlSymsp->TOP.__024unit__03a__03aBar__Vclpkg}
    , __024unit__03a__03aBaz__Vclpkg{vlSymsp->TOP.__024unit__03a__03aBaz__Vclpkg}
    , __024unit__03a__03aQux__Vclpkg{vlSymsp->TOP.__024unit__03a__03aQux__Vclpkg}
    , __024unit__03a__03aBoo__Vclpkg{vlSymsp->TOP.__024unit__03a__03aBoo__Vclpkg}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

Vt_randomize_inline_var_ctl::Vt_randomize_inline_var_ctl(const char* _vcname__)
    : Vt_randomize_inline_var_ctl(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

Vt_randomize_inline_var_ctl::~Vt_randomize_inline_var_ctl() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void Vt_randomize_inline_var_ctl___024root___eval_debug_assertions(Vt_randomize_inline_var_ctl___024root* vlSelf);
#endif  // VL_DEBUG
void Vt_randomize_inline_var_ctl___024root___eval_static(Vt_randomize_inline_var_ctl___024root* vlSelf);
void Vt_randomize_inline_var_ctl___024root___eval_initial(Vt_randomize_inline_var_ctl___024root* vlSelf);
void Vt_randomize_inline_var_ctl___024root___eval_settle(Vt_randomize_inline_var_ctl___024root* vlSelf);
void Vt_randomize_inline_var_ctl___024root___eval(Vt_randomize_inline_var_ctl___024root* vlSelf);

void Vt_randomize_inline_var_ctl::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vt_randomize_inline_var_ctl::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    Vt_randomize_inline_var_ctl___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        vlSymsp->__Vm_didInit = true;
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        Vt_randomize_inline_var_ctl___024root___eval_static(&(vlSymsp->TOP));
        Vt_randomize_inline_var_ctl___024root___eval_initial(&(vlSymsp->TOP));
        Vt_randomize_inline_var_ctl___024root___eval_settle(&(vlSymsp->TOP));
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    Vt_randomize_inline_var_ctl___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool Vt_randomize_inline_var_ctl::eventsPending() { return false; }

uint64_t Vt_randomize_inline_var_ctl::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* Vt_randomize_inline_var_ctl::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void Vt_randomize_inline_var_ctl___024root___eval_final(Vt_randomize_inline_var_ctl___024root* vlSelf);

VL_ATTR_COLD void Vt_randomize_inline_var_ctl::final() {
    Vt_randomize_inline_var_ctl___024root___eval_final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* Vt_randomize_inline_var_ctl::hierName() const { return vlSymsp->name(); }
const char* Vt_randomize_inline_var_ctl::modelName() const { return "Vt_randomize_inline_var_ctl"; }
unsigned Vt_randomize_inline_var_ctl::threads() const { return 1; }
void Vt_randomize_inline_var_ctl::prepareClone() const { contextp()->prepareClone(); }
void Vt_randomize_inline_var_ctl::atClone() const {
    contextp()->threadPoolpOnClone();
}
