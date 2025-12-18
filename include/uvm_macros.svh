// DESCRIPTION: Verilator: UVM macros stub for simulation compatibility
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief UVM macros stub for Verilator
///
/// This file provides stub implementations of common UVM macros to allow
/// UVM-based testbenches to compile with Verilator. The macros translate
/// UVM logging calls to $display and other standard SystemVerilog constructs.
///
/// Include this file where you would normally include "uvm_macros.svh"
///
//*************************************************************************

`ifndef UVM_MACROS_SVH
`define UVM_MACROS_SVH

// UVM verbosity levels - use values from uvm_pkg
// These are duplicated here for use in macros before uvm_pkg is imported
`ifndef UVM_NONE
  `define UVM_NONE   0
  `define UVM_LOW    100
  `define UVM_MEDIUM 200
  `define UVM_HIGH   300
  `define UVM_FULL   400
  `define UVM_DEBUG  500
`endif

//----------------------------------------------------------------------
// Messaging macros
//----------------------------------------------------------------------

// uvm_info - informational message
`define uvm_info(ID, MSG, VERBOSITY) \
  begin \
    if (VERBOSITY <= uvm_global_verbosity) \
      $display("[UVM_INFO] %s(%0d) @ %0t: %s [%s]", `__FILE__, `__LINE__, $time, MSG, ID); \
  end

// uvm_warning - warning message
`define uvm_warning(ID, MSG) \
  begin \
    $display("[UVM_WARNING] %s(%0d) @ %0t: %s [%s]", `__FILE__, `__LINE__, $time, MSG, ID); \
  end

// uvm_error - error message (non-fatal)
`define uvm_error(ID, MSG) \
  begin \
    $display("[UVM_ERROR] %s(%0d) @ %0t: %s [%s]", `__FILE__, `__LINE__, $time, MSG, ID); \
  end

// uvm_fatal - fatal error message (terminates simulation)
`define uvm_fatal(ID, MSG) \
  begin \
    $display("[UVM_FATAL] %s(%0d) @ %0t: %s [%s]", `__FILE__, `__LINE__, $time, MSG, ID); \
    $fatal(1, "UVM_FATAL"); \
  end

//----------------------------------------------------------------------
// Object utility macros
//----------------------------------------------------------------------

// uvm_object_utils - register object with factory (stub for Verilator)
// Provides a type_id class with create() method to mimic UVM factory
// Also provides factory registration capability
`define uvm_object_utils(TYPE) \
  typedef TYPE __verilator_uvm_type_``TYPE; \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction \
  typedef class type_id; \
  class type_id extends uvm_object_wrapper; \
    static type_id m_inst; \
    static function TYPE create(string name = `"TYPE`", uvm_component parent = null); \
      TYPE obj = new(name); \
      return obj; \
    endfunction \
    static function void register(); \
      if (m_inst == null) begin \
        m_inst = new(); \
        uvm_factory::register(m_inst); \
      end \
    endfunction \
    virtual function uvm_object create_object(string name = ""); \
      TYPE obj = new(name); \
      return obj; \
    endfunction \
    virtual function uvm_component create_component(string name = "", uvm_component parent = null); \
      return null; \
    endfunction \
    virtual function string get_type_name(); \
      return `"TYPE`"; \
    endfunction \
  endclass

// uvm_object_utils_begin/end - for field automation (stub)
`define uvm_object_utils_begin(TYPE) \
  typedef TYPE __verilator_uvm_type_``TYPE; \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction

`define uvm_object_utils_end

// uvm_object_param_utils - parameterized object registration (stub)
`define uvm_object_param_utils(TYPE) \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction

`define uvm_object_param_utils_begin(TYPE) \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction

//----------------------------------------------------------------------
// Component utility macros
//----------------------------------------------------------------------

// uvm_component_utils - register component with factory (stub for Verilator)
// Provides a type_id class with create() method to mimic UVM factory
// Also provides factory registration capability
`define uvm_component_utils(TYPE) \
  typedef TYPE __verilator_uvm_type_``TYPE; \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction \
  typedef class type_id; \
  class type_id extends uvm_object_wrapper; \
    static type_id m_inst; \
    static function TYPE create(string name = `"TYPE`", uvm_component parent = null); \
      TYPE obj = new(name, parent); \
      return obj; \
    endfunction \
    static function void register(); \
      if (m_inst == null) begin \
        m_inst = new(); \
        uvm_factory::register(m_inst); \
      end \
    endfunction \
    virtual function uvm_object create_object(string name = ""); \
      return null; \
    endfunction \
    virtual function uvm_component create_component(string name = "", uvm_component parent = null); \
      TYPE obj = new(name, parent); \
      return obj; \
    endfunction \
    virtual function string get_type_name(); \
      return `"TYPE`"; \
    endfunction \
  endclass

// uvm_component_utils_begin/end - for field automation (stub)
`define uvm_component_utils_begin(TYPE) \
  typedef TYPE __verilator_uvm_type_``TYPE; \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction

`define uvm_component_utils_end

// uvm_component_param_utils - parameterized component registration (stub)
`define uvm_component_param_utils(TYPE) \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction

`define uvm_component_param_utils_begin(TYPE) \
  static function string __verilator_get_type_name(); return `"TYPE`"; endfunction

//----------------------------------------------------------------------
// Field macros (stubs - typically used with object_utils_begin/end)
//----------------------------------------------------------------------

`define uvm_field_int(FIELD, FLAG)
`define uvm_field_string(FIELD, FLAG)
`define uvm_field_object(FIELD, FLAG)
`define uvm_field_array_int(FIELD, FLAG)
`define uvm_field_array_object(FIELD, FLAG)
`define uvm_field_queue_int(FIELD, FLAG)
`define uvm_field_queue_object(FIELD, FLAG)
`define uvm_field_aa_int_string(FIELD, FLAG)
`define uvm_field_aa_object_string(FIELD, FLAG)
`define uvm_field_enum(TYPE, FIELD, FLAG)
`define uvm_field_real(FIELD, FLAG)
`define uvm_field_event(FIELD, FLAG)
`define uvm_field_sarray_int(FIELD, FLAG)

//----------------------------------------------------------------------
// Sequence macros
//----------------------------------------------------------------------

// uvm_do - execute a sequence item (stub)
`define uvm_do(SEQ_OR_ITEM) \
  begin \
    SEQ_OR_ITEM = new(); \
    if (!SEQ_OR_ITEM.randomize()) \
      `uvm_warning("RANDFL", "Randomization failed for sequence item"); \
  end

// uvm_do_with - execute with inline constraints (stub)
`define uvm_do_with(SEQ_OR_ITEM, CONSTRAINTS) \
  begin \
    SEQ_OR_ITEM = new(); \
    if (!SEQ_OR_ITEM.randomize() with CONSTRAINTS) \
      `uvm_warning("RANDFL", "Randomization failed for sequence item"); \
  end

// uvm_create - create a sequence item (stub)
`define uvm_create(SEQ_OR_ITEM) \
  SEQ_OR_ITEM = new()

// uvm_send - send a pre-created item (stub - no-op)
`define uvm_send(SEQ_OR_ITEM)

// uvm_rand_send - randomize and send (stub)
`define uvm_rand_send(SEQ_OR_ITEM) \
  begin \
    if (!SEQ_OR_ITEM.randomize()) \
      `uvm_warning("RANDFL", "Randomization failed for sequence item"); \
  end

// uvm_rand_send_with - randomize with constraints and send (stub)
`define uvm_rand_send_with(SEQ_OR_ITEM, CONSTRAINTS) \
  begin \
    if (!SEQ_OR_ITEM.randomize() with CONSTRAINTS) \
      `uvm_warning("RANDFL", "Randomization failed for sequence item"); \
  end

//----------------------------------------------------------------------
// Declarative macros (stubs)
//----------------------------------------------------------------------

// uvm_declare_p_sequencer - declare sequencer handle
`define uvm_declare_p_sequencer(SEQUENCER) \
  SEQUENCER p_sequencer;

//----------------------------------------------------------------------
// Analysis macros
//----------------------------------------------------------------------

// uvm_analysis_imp_decl - declare analysis implementation
`define uvm_analysis_imp_decl(SFX) \
  class uvm_analysis_imp``SFX #(type T=int, type IMP=int) extends uvm_object; \
    local IMP m_imp; \
    function new(string name, IMP imp); \
      m_imp = imp; \
    endfunction \
    function void write(T t); \
      m_imp.write``SFX(t); \
    endfunction \
  endclass

//----------------------------------------------------------------------
// TLM macros (stubs)
//----------------------------------------------------------------------

`define uvm_blocking_put_imp_decl(SFX)
`define uvm_nonblocking_put_imp_decl(SFX)
`define uvm_put_imp_decl(SFX)
`define uvm_blocking_get_imp_decl(SFX)
`define uvm_nonblocking_get_imp_decl(SFX)
`define uvm_get_imp_decl(SFX)
`define uvm_blocking_peek_imp_decl(SFX)
`define uvm_nonblocking_peek_imp_decl(SFX)
`define uvm_peek_imp_decl(SFX)
`define uvm_blocking_get_peek_imp_decl(SFX)
`define uvm_nonblocking_get_peek_imp_decl(SFX)
`define uvm_get_peek_imp_decl(SFX)
`define uvm_blocking_transport_imp_decl(SFX)
`define uvm_nonblocking_transport_imp_decl(SFX)
`define uvm_transport_imp_decl(SFX)

//----------------------------------------------------------------------
// Register macros (stubs for UVM RAL)
//----------------------------------------------------------------------

`define uvm_reg_field_utils_begin(TYPE)
`define uvm_reg_field_utils_end

//----------------------------------------------------------------------
// Callback macros (stubs)
//----------------------------------------------------------------------

`define uvm_register_cb(T, CB)
`define uvm_set_super_type(T, ST)
`define uvm_do_callbacks(T, CB, METHOD)
`define uvm_do_obj_callbacks(T, CB, OBJ, METHOD)

//----------------------------------------------------------------------
// Miscellaneous macros
//----------------------------------------------------------------------

// UVM field flags (used with field macros)
`define UVM_ALL_ON     'hFFFF
`define UVM_DEFAULT    'h0001
`define UVM_COPY       'h0002
`define UVM_NOCOPY     'h0004
`define UVM_COMPARE    'h0008
`define UVM_NOCOMPARE  'h0010
`define UVM_PRINT      'h0020
`define UVM_NOPRINT    'h0040
`define UVM_RECORD     'h0080
`define UVM_NORECORD   'h0100
`define UVM_PACK       'h0200
`define UVM_NOPACK     'h0400
`define UVM_PHYSICAL   'h0800
`define UVM_ABSTRACT   'h1000
`define UVM_READONLY   'h2000
`define UVM_NODEFPRINT 'h4000

// UVM radix for printing
`define UVM_BIN        'h01000000
`define UVM_DEC        'h02000000
`define UVM_UNSIGNED   'h03000000
`define UVM_OCT        'h04000000
`define UVM_HEX        'h05000000
`define UVM_STRING     'h06000000
`define UVM_TIME       'h07000000
`define UVM_ENUM       'h08000000
`define UVM_REAL       'h09000000
`define UVM_REAL_DEC   'h0A000000
`define UVM_REAL_EXP   'h0B000000
`define UVM_NORADIX    0

`endif // UVM_MACROS_SVH
