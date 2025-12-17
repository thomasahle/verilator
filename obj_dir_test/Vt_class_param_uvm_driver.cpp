// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vt_class_param_uvm_driver__pch.h"

//============================================================
// Constructors

Vt_class_param_uvm_driver::Vt_class_param_uvm_driver(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vt_class_param_uvm_driver__Syms(contextp(), _vcname__, this)}
    , __PVT____024unit{vlSymsp->TOP.__PVT____024unit}
    , __024unit__03a__03auvm_sequence_item__Vclpkg{vlSymsp->TOP.__024unit__03a__03auvm_sequence_item__Vclpkg}
    , __024unit__03a__03amy_tx__Vclpkg{vlSymsp->TOP.__024unit__03a__03amy_tx__Vclpkg}
    , __024unit__03a__03amy_driver__Vclpkg{vlSymsp->TOP.__024unit__03a__03amy_driver__Vclpkg}
    , __024unit__03a__03auvm_seq_item_pull_port__pi1__Vclpkg{vlSymsp->TOP.__024unit__03a__03auvm_seq_item_pull_port__pi1__Vclpkg}
    , __024unit__03a__03auvm_driver__Tz1_TBz1__Vclpkg{vlSymsp->TOP.__024unit__03a__03auvm_driver__Tz1_TBz1__Vclpkg}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

Vt_class_param_uvm_driver::Vt_class_param_uvm_driver(const char* _vcname__)
    : Vt_class_param_uvm_driver(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

Vt_class_param_uvm_driver::~Vt_class_param_uvm_driver() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void Vt_class_param_uvm_driver___024root___eval_debug_assertions(Vt_class_param_uvm_driver___024root* vlSelf);
#endif  // VL_DEBUG
void Vt_class_param_uvm_driver___024root___eval_static(Vt_class_param_uvm_driver___024root* vlSelf);
void Vt_class_param_uvm_driver___024root___eval_initial(Vt_class_param_uvm_driver___024root* vlSelf);
void Vt_class_param_uvm_driver___024root___eval_settle(Vt_class_param_uvm_driver___024root* vlSelf);
void Vt_class_param_uvm_driver___024root___eval(Vt_class_param_uvm_driver___024root* vlSelf);

void Vt_class_param_uvm_driver::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vt_class_param_uvm_driver::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    Vt_class_param_uvm_driver___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        vlSymsp->__Vm_didInit = true;
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        Vt_class_param_uvm_driver___024root___eval_static(&(vlSymsp->TOP));
        Vt_class_param_uvm_driver___024root___eval_initial(&(vlSymsp->TOP));
        Vt_class_param_uvm_driver___024root___eval_settle(&(vlSymsp->TOP));
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    Vt_class_param_uvm_driver___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool Vt_class_param_uvm_driver::eventsPending() { return false; }

uint64_t Vt_class_param_uvm_driver::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* Vt_class_param_uvm_driver::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void Vt_class_param_uvm_driver___024root___eval_final(Vt_class_param_uvm_driver___024root* vlSelf);

VL_ATTR_COLD void Vt_class_param_uvm_driver::final() {
    Vt_class_param_uvm_driver___024root___eval_final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* Vt_class_param_uvm_driver::hierName() const { return vlSymsp->name(); }
const char* Vt_class_param_uvm_driver::modelName() const { return "Vt_class_param_uvm_driver"; }
unsigned Vt_class_param_uvm_driver::threads() const { return 1; }
void Vt_class_param_uvm_driver::prepareClone() const { contextp()->prepareClone(); }
void Vt_class_param_uvm_driver::atClone() const {
    contextp()->threadPoolpOnClone();
}
