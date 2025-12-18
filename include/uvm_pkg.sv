// DESCRIPTION: Verilator: UVM package stub for simulation compatibility
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
/// \brief UVM package stub for Verilator
///
/// This file provides stub implementations of common UVM classes to allow
/// UVM-based testbenches to compile with Verilator. The classes provide
/// minimal functionality to allow compilation and basic simulation.
///
/// Import this package where you would normally import uvm_pkg
///
//*************************************************************************

// verilator lint_off DECLFILENAME
// verilator lint_off UNUSEDSIGNAL
// verilator lint_off UNUSEDPARAM

package uvm_pkg;

  // Re-export verbosity enum
  typedef enum int {
    UVM_NONE   = 0,
    UVM_LOW    = 100,
    UVM_MEDIUM = 200,
    UVM_HIGH   = 300,
    UVM_FULL   = 400,
    UVM_DEBUG  = 500
  } uvm_verbosity;

  // Global verbosity setting (can be changed at runtime)
  int uvm_global_verbosity = UVM_MEDIUM;

  // Active/passive enum for agents
  typedef enum bit {
    UVM_PASSIVE = 0,
    UVM_ACTIVE  = 1
  } uvm_active_passive_enum;

  // Sequencer arbitration modes
  typedef enum int {
    UVM_SEQ_ARB_FIFO,
    UVM_SEQ_ARB_WEIGHTED,
    UVM_SEQ_ARB_RANDOM,
    UVM_SEQ_ARB_STRICT_FIFO,
    UVM_SEQ_ARB_STRICT_RANDOM,
    UVM_SEQ_ARB_USER
  } uvm_sequencer_arb_mode;

  // Object/component status
  typedef enum int {
    UVM_CREATED,
    UVM_POST_NEW,
    UVM_PRE_BUILD,
    UVM_BUILD,
    UVM_POST_BUILD,
    UVM_PRE_CONNECT,
    UVM_CONNECT,
    UVM_POST_CONNECT,
    UVM_END_OF_ELABORATION,
    UVM_PRE_RUN,
    UVM_RUN,
    UVM_POST_RUN,
    UVM_PRE_SHUTDOWN,
    UVM_SHUTDOWN,
    UVM_POST_SHUTDOWN,
    UVM_EXTRACT,
    UVM_CHECK,
    UVM_REPORT,
    UVM_FINAL
  } uvm_phase_state;

  // Objection type
  typedef enum int {
    UVM_RAISED,
    UVM_DROPPED,
    UVM_ALL_DROPPED
  } uvm_objection_event;

  // Packer/unpacker policy
  typedef enum int {
    UVM_PACK,
    UVM_UNPACK
  } uvm_packer_policy;

  //----------------------------------------------------------------------
  // Forward declarations
  //----------------------------------------------------------------------
  typedef class uvm_object;
  typedef class uvm_component;
  typedef class uvm_sequence_item;
  typedef class uvm_phase;
  typedef class uvm_objection;
  typedef class uvm_object_wrapper;
  typedef class uvm_factory;

  //----------------------------------------------------------------------
  // uvm_void - base class for all UVM classes
  //----------------------------------------------------------------------
  virtual class uvm_void;
  endclass

  //----------------------------------------------------------------------
  // uvm_object_wrapper - base class for factory type wrappers
  // Each registered type has a wrapper that can create instances
  //----------------------------------------------------------------------
  virtual class uvm_object_wrapper;
    pure virtual function uvm_object create_object(string name = "");
    pure virtual function uvm_component create_component(string name = "", uvm_component parent = null);
    pure virtual function string get_type_name();
  endclass

  //----------------------------------------------------------------------
  // uvm_factory - singleton factory for creating objects by type name
  //----------------------------------------------------------------------
  class uvm_factory;
    // Registry mapping type names to wrappers
    protected static uvm_object_wrapper m_type_registry[string];
    // Singleton instance
    protected static uvm_factory m_inst;

    // Get singleton instance
    static function uvm_factory get();
      if (m_inst == null)
        m_inst = new();
      return m_inst;
    endfunction

    // Register a type wrapper
    static function void register(uvm_object_wrapper wrapper);
      string type_name = wrapper.get_type_name();
      m_type_registry[type_name] = wrapper;
    endfunction

    // Check if a type is registered
    static function bit is_type_registered(string type_name);
      return m_type_registry.exists(type_name);
    endfunction

    // Create an object by type name
    static function uvm_object create_object_by_name(string type_name, string parent_inst_path = "",
                                                      string name = "");
      if (m_type_registry.exists(type_name))
        return m_type_registry[type_name].create_object(name);
      else begin
        $display("[UVM_WARNING] Factory: Type '%s' not registered", type_name);
        return null;
      end
    endfunction

    // Create a component by type name
    static function uvm_component create_component_by_name(string type_name, string parent_inst_path = "",
                                                            string name = "", uvm_component parent = null);
      if (m_type_registry.exists(type_name))
        return m_type_registry[type_name].create_component(name, parent);
      else begin
        $display("[UVM_WARNING] Factory: Type '%s' not registered", type_name);
        return null;
      end
    endfunction

    // Print all registered types
    static function void print_all_types();
      $display("UVM Factory Registered Types:");
      foreach (m_type_registry[name])
        $display("  %s", name);
    endfunction

    // Get number of registered types
    static function int get_num_types();
      return m_type_registry.size();
    endfunction
  endclass

  // Global factory instance accessor
  function uvm_factory uvm_factory_get();
    return uvm_factory::get();
  endfunction

  //----------------------------------------------------------------------
  // uvm_object - base class for data objects
  //----------------------------------------------------------------------
  class uvm_object extends uvm_void;
    protected string m_name;

    function new(string name = "");
      m_name = name;
    endfunction

    virtual function string get_name();
      return m_name;
    endfunction

    virtual function void set_name(string name);
      m_name = name;
    endfunction

    virtual function string get_type_name();
      return "uvm_object";
    endfunction

    virtual function string get_full_name();
      return m_name;
    endfunction

    virtual function uvm_object clone();
      return null;  // Stub - derived classes should override
    endfunction

    virtual function void copy(uvm_object rhs);
      // Stub - derived classes should override
    endfunction

    virtual function bit compare(uvm_object rhs, uvm_comparer comparer = null);
      return 1;  // Stub
    endfunction

    virtual function void print(uvm_printer printer = null);
      if (printer == null) begin
        $display("%s", sprint());
      end else begin
        $display("%s", sprint(printer));
      end
    endfunction

    virtual function string convert2string();
      return $sformatf("{%s}", get_name());
    endfunction

    virtual function string sprint(uvm_printer printer = null);
      string result;
      if (printer == null) begin
        printer = new("default_printer");
      end
      printer.m_string = "";
      result = $sformatf("--------------------------------------\n");
      result = {result, $sformatf("Name: %s  Type: %s\n", get_name(), get_type_name())};
      result = {result, "--------------------------------------\n"};
      do_print(printer);
      result = {result, printer.emit()};
      return result;
    endfunction

    virtual function void do_copy(uvm_object rhs);
      // Override in derived classes
    endfunction

    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      return 1;
    endfunction

    virtual function void do_print(uvm_printer printer);
      // Override in derived classes
    endfunction

    virtual function string do_convert2string();
      return "";
    endfunction

    virtual function void do_pack(uvm_packer packer);
      // Override in derived classes
    endfunction

    virtual function void do_unpack(uvm_packer packer);
      // Override in derived classes
    endfunction

    virtual function void do_record(uvm_recorder recorder);
      // Override in derived classes
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_comparer - comparison utility (stub)
  //----------------------------------------------------------------------
  class uvm_comparer extends uvm_object;
    int unsigned show_max = 1;
    int unsigned verbosity = UVM_LOW;
    string miscompares = "";
    int unsigned physical = 1;
    int unsigned abstract_ = 1;
    bit check_type = 1;
    int unsigned sev = 0;
    int unsigned result = 0;

    function new(string name = "uvm_comparer");
      super.new(name);
    endfunction

    virtual function void print_msg(string msg);
      miscompares = {miscompares, msg, "\n"};
    endfunction
  endclass

  // Radix enum for printer (must be declared before uvm_printer)
  typedef enum int {
    UVM_NORADIX = 0,
    UVM_BIN     = 'h01000000,
    UVM_DEC     = 'h02000000,
    UVM_UNSIGNED = 'h03000000,
    UVM_OCT     = 'h04000000,
    UVM_HEX     = 'h05000000,
    UVM_STRING  = 'h06000000,
    UVM_TIME    = 'h07000000,
    UVM_ENUM    = 'h08000000
  } uvm_radix_enum;

  typedef logic [4095:0] uvm_bitstream_t;

  //----------------------------------------------------------------------
  // uvm_printer - print utility (stub)
  //----------------------------------------------------------------------
  class uvm_printer extends uvm_object;
    int unsigned knobs_depth = -1;
    string knobs_separator = ".";
    string m_string = "";  // Accumulated output for sprint

    function new(string name = "uvm_printer");
      super.new(name);
    endfunction

    virtual function void print_field(string name, uvm_bitstream_t value, int size,
                                       uvm_radix_enum radix = UVM_NORADIX, byte scope_separator = ".",
                                       string type_name = "");
      string line;
      case (radix)
        UVM_BIN:      line = $sformatf("  %-20s: 'b%0b\n", name, value);
        UVM_DEC:      line = $sformatf("  %-20s: %0d\n", name, value);
        UVM_UNSIGNED: line = $sformatf("  %-20s: %0d\n", name, value);
        UVM_OCT:      line = $sformatf("  %-20s: 'o%0o\n", name, value);
        UVM_HEX:      line = $sformatf("  %-20s: 'h%0h\n", name, value);
        default:      line = $sformatf("  %-20s: 'h%0h\n", name, value);
      endcase
      m_string = {m_string, line};
    endfunction

    virtual function void print_field_int(string name, uvm_bitstream_t value, int size,
                                           uvm_radix_enum radix = UVM_DEC, byte scope_separator = ".",
                                           string type_name = "");
      print_field(name, value, size, radix, scope_separator, type_name);
    endfunction

    virtual function void print_string(string name, string value, byte scope_separator = ".");
      string line;
      line = $sformatf("  %-20s: \"%s\"\n", name, value);
      m_string = {m_string, line};
    endfunction

    virtual function void print_object(string name, uvm_object value, byte scope_separator = ".");
      string line;
      if (value != null)
        line = $sformatf("  %-20s: %s (%s)\n", name, value.get_name(), value.get_type_name());
      else
        line = $sformatf("  %-20s: null\n", name);
      m_string = {m_string, line};
    endfunction

    virtual function void print_generic(string name, string type_name, int size, string value,
                                         byte scope_separator = ".");
      string line;
      line = $sformatf("  %-20s: %s\n", name, value);
      m_string = {m_string, line};
    endfunction

    virtual function void print_array_header(string name, int size, string arraytype = "array",
                                              byte scope_separator = ".");
      string line;
      line = $sformatf("  %-20s: %s[%0d]\n", name, arraytype, size);
      m_string = {m_string, line};
    endfunction

    virtual function void print_array_footer(int size = 0);
      // No-op for simple printer
    endfunction

    // Get the accumulated string and reset
    virtual function string emit();
      string result = m_string;
      m_string = "";
      return result;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_table_printer - table format printer
  //----------------------------------------------------------------------
  class uvm_table_printer extends uvm_printer;
    function new(string name = "uvm_table_printer");
      super.new(name);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_tree_printer - tree format printer
  //----------------------------------------------------------------------
  class uvm_tree_printer extends uvm_printer;
    function new(string name = "uvm_tree_printer");
      super.new(name);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_line_printer - line format printer
  //----------------------------------------------------------------------
  class uvm_line_printer extends uvm_printer;
    function new(string name = "uvm_line_printer");
      super.new(name);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_packer - pack/unpack utility (stub)
  //----------------------------------------------------------------------
  class uvm_packer extends uvm_object;
    bit big_endian = 0;
    bit use_metadata = 0;

    function new(string name = "uvm_packer");
      super.new(name);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_recorder - recording utility (stub)
  //----------------------------------------------------------------------
  class uvm_recorder extends uvm_object;
    function new(string name = "uvm_recorder");
      super.new(name);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_objection - objection mechanism with tracking
  //----------------------------------------------------------------------
  class uvm_objection extends uvm_object;
    // Track objection counts per object (keyed by object name/id)
    protected int m_objection_count[string];
    // Total objection count
    protected int m_total_count;
    // Drain time settings per object
    protected time m_drain_time[string];

    function new(string name = "uvm_objection");
      super.new(name);
      m_total_count = 0;
    endfunction

    // Get key for an object (handles null)
    protected function string get_obj_key(uvm_object obj);
      if (obj == null)
        return "__null__";
      else
        return obj.get_full_name();
    endfunction

    virtual function void raise_objection(uvm_object obj = null, string description = "", int count = 1);
      string key = get_obj_key(obj);
      if (m_objection_count.exists(key))
        m_objection_count[key] += count;
      else
        m_objection_count[key] = count;
      m_total_count += count;
    endfunction

    virtual function void drop_objection(uvm_object obj = null, string description = "", int count = 1);
      string key = get_obj_key(obj);
      if (m_objection_count.exists(key)) begin
        m_objection_count[key] -= count;
        if (m_objection_count[key] <= 0)
          m_objection_count.delete(key);
      end
      m_total_count -= count;
      if (m_total_count < 0)
        m_total_count = 0;
    endfunction

    virtual function void set_drain_time(uvm_object obj, time drain);
      string key = get_obj_key(obj);
      m_drain_time[key] = drain;
    endfunction

    // Get total objection count
    virtual function int get_objection_count(uvm_object obj = null);
      if (obj == null)
        return m_total_count;
      else begin
        string key = get_obj_key(obj);
        if (m_objection_count.exists(key))
          return m_objection_count[key];
        else
          return 0;
      end
    endfunction

    // Get total count across all objects
    virtual function int get_objection_total();
      return m_total_count;
    endfunction

    // Check if all objections have been dropped
    virtual function bit all_dropped();
      return (m_total_count == 0);
    endfunction

    // Clear all objections (for phase transitions)
    virtual function void clear();
      m_objection_count.delete();
      m_total_count = 0;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_phase - phase base class with objection tracking
  //----------------------------------------------------------------------
  class uvm_phase extends uvm_object;
    // Each phase has its own objection tracker
    protected uvm_objection m_phase_objection;

    function new(string name = "uvm_phase");
      super.new(name);
      m_phase_objection = new({name, "_objection"});
    endfunction

    virtual function void raise_objection(uvm_object obj, string description = "", int count = 1);
      m_phase_objection.raise_objection(obj, description, count);
    endfunction

    virtual function void drop_objection(uvm_object obj, string description = "", int count = 1);
      m_phase_objection.drop_objection(obj, description, count);
    endfunction

    // Get the phase's objection object
    virtual function uvm_objection get_objection();
      return m_phase_objection;
    endfunction

    // Check if phase can end (all objections dropped)
    virtual function bit phase_done();
      return m_phase_objection.all_dropped();
    endfunction

    // Get current objection count
    virtual function int get_objection_count(uvm_object obj = null);
      return m_phase_objection.get_objection_count(obj);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_component - base class for structural components
  //----------------------------------------------------------------------
  class uvm_component extends uvm_object;
    protected uvm_component m_parent;
    protected uvm_component m_children[string];

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
      if (parent != null) begin
        parent.m_children[name] = this;
      end
    endfunction

    virtual function uvm_component get_parent();
      return m_parent;
    endfunction

    virtual function string get_full_name();
      if (m_parent == null || m_parent.get_name() == "")
        return get_name();
      else
        return {m_parent.get_full_name(), ".", get_name()};
    endfunction

    virtual function int get_num_children();
      return m_children.size();
    endfunction

    virtual function uvm_component get_child(string name);
      if (m_children.exists(name))
        return m_children[name];
      return null;
    endfunction

    virtual function void get_children(ref uvm_component children[$]);
      foreach (m_children[name])
        children.push_back(m_children[name]);
    endfunction

    // Phase methods - override in derived classes
    virtual function void build_phase(uvm_phase phase);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
    endfunction

    virtual function void start_of_simulation_phase(uvm_phase phase);
    endfunction

    virtual task run_phase(uvm_phase phase);
    endtask

    virtual function void extract_phase(uvm_phase phase);
    endfunction

    virtual function void check_phase(uvm_phase phase);
    endfunction

    virtual function void report_phase(uvm_phase phase);
    endfunction

    virtual function void final_phase(uvm_phase phase);
    endfunction

    // Legacy phase methods
    virtual function void build();
      // Legacy - calls build_phase with null
    endfunction

    virtual function void connect();
      // Legacy
    endfunction

    virtual task run();
      // Legacy
    endtask

    // Utility methods
    virtual function void print_topology(uvm_printer printer = null);
      $display("Topology for %s:", get_full_name());
      foreach (m_children[name]) begin
        $display("  %s", m_children[name].get_full_name());
      end
    endfunction

    // Raise/drop objection shortcuts
    virtual function void raise_objection(uvm_phase phase = null, string description = "", int count = 1);
      // Stub
    endfunction

    virtual function void drop_objection(uvm_phase phase = null, string description = "", int count = 1);
      // Stub
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_sequence_item - base class for sequence items
  //----------------------------------------------------------------------
  class uvm_sequence_item extends uvm_object;
    protected int m_sequence_id = -1;
    protected int m_transaction_id = -1;
    protected bit m_use_sequence_info = 0;

    function new(string name = "uvm_sequence_item");
      super.new(name);
    endfunction

    virtual function int get_sequence_id();
      return m_sequence_id;
    endfunction

    virtual function void set_sequence_id(int id);
      m_sequence_id = id;
    endfunction

    virtual function int get_transaction_id();
      return m_transaction_id;
    endfunction

    virtual function void set_transaction_id(int id);
      m_transaction_id = id;
    endfunction

    virtual function void set_item_context(uvm_sequence_base parent_seq, uvm_sequencer_base sequencer = null);
      // Stub
    endfunction
  endclass

  // Forward declaration
  typedef class uvm_sequence_base;
  typedef class uvm_sequencer_base;

  //----------------------------------------------------------------------
  // uvm_sequence_base - base class for sequences
  //----------------------------------------------------------------------
  class uvm_sequence_base extends uvm_sequence_item;
    protected uvm_sequencer_base m_sequencer;
    protected uvm_sequence_base m_parent_sequence;

    function new(string name = "uvm_sequence_base");
      super.new(name);
    endfunction

    virtual function uvm_sequencer_base get_sequencer();
      return m_sequencer;
    endfunction

    virtual function void set_sequencer(uvm_sequencer_base sequencer);
      m_sequencer = sequencer;
    endfunction

    virtual function uvm_sequence_base get_parent_sequence();
      return m_parent_sequence;
    endfunction

    virtual function void set_parent_sequence(uvm_sequence_base parent);
      m_parent_sequence = parent;
    endfunction

    virtual task pre_start();
      // Override in derived classes
    endtask

    virtual task pre_body();
      // Override in derived classes
    endtask

    virtual task body();
      // Override in derived classes
    endtask

    virtual task post_body();
      // Override in derived classes
    endtask

    virtual task post_start();
      // Override in derived classes
    endtask

    virtual task start(uvm_sequencer_base sequencer, uvm_sequence_base parent_sequence = null,
                       int this_priority = -1, bit call_pre_post = 1);
      m_sequencer = sequencer;
      m_parent_sequence = parent_sequence;
      if (call_pre_post) pre_start();
      if (call_pre_post) pre_body();
      body();
      if (call_pre_post) post_body();
      if (call_pre_post) post_start();
    endtask

    virtual function void set_item_context(uvm_sequence_base parent_seq, uvm_sequencer_base sequencer = null);
      m_parent_sequence = parent_seq;
      if (sequencer != null)
        m_sequencer = sequencer;
    endfunction

    // Item methods for sequence execution
    virtual task start_item(uvm_sequence_item item, int set_priority = -1, uvm_sequencer_base sequencer = null);
      // Stub - in real UVM this does arbitration
    endtask

    virtual task finish_item(uvm_sequence_item item, int set_priority = -1);
      // Stub - in real UVM this sends to driver
    endtask

    virtual function void raise_objection(uvm_phase phase = null, string description = "", int count = 1);
      // Stub
    endfunction

    virtual function void drop_objection(uvm_phase phase = null, string description = "", int count = 1);
      // Stub
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_sequence - parameterized sequence base class
  //----------------------------------------------------------------------
  class uvm_sequence #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_sequence_base;
    REQ req;
    RSP rsp;

    function new(string name = "uvm_sequence");
      super.new(name);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_sequencer_base - base sequencer
  //----------------------------------------------------------------------
  class uvm_sequencer_base extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void set_arbitration(uvm_sequencer_arb_mode val);
      // Stub
    endfunction

    virtual task wait_for_grant(uvm_sequence_base sequence_ptr, int item_priority = -1, bit lock_request = 0);
      // Stub - immediate grant
    endtask

    virtual function void send_request(uvm_sequence_base sequence_ptr, uvm_sequence_item t, bit rerandomize = 0);
      // Stub
    endfunction

    virtual task wait_for_item_done(uvm_sequence_base sequence_ptr, int transaction_id);
      // Stub - immediate completion
    endtask
  endclass

  //----------------------------------------------------------------------
  // uvm_sequencer_param_base - parameterized sequencer base
  //----------------------------------------------------------------------
  class uvm_sequencer_param_base #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_sequencer_base;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_sequencer - full sequencer implementation
  //----------------------------------------------------------------------
  class uvm_sequencer #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_sequencer_param_base #(REQ, RSP);
    protected REQ m_req_fifo[$];
    protected RSP m_rsp_fifo[$];

    // seq_item_export for driver connection (alias to this sequencer)
    uvm_sequencer #(REQ, RSP) seq_item_export;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      seq_item_export = this;
    endfunction

    // Public method to send a request item (used by sequences via start_item/finish_item)
    virtual function void send_request(REQ t);
      m_req_fifo.push_back(t);
    endfunction

    // Get number of pending requests
    virtual function int num_pending_reqs();
      return m_req_fifo.size();
    endfunction

    virtual task get_next_item(output REQ t);
      wait (m_req_fifo.size() > 0);
      t = m_req_fifo.pop_front();
    endtask

    virtual task try_next_item(output REQ t);
      if (m_req_fifo.size() > 0)
        t = m_req_fifo.pop_front();
      else
        t = null;
    endtask

    virtual function void item_done(RSP item = null);
      // Stub
    endfunction

    virtual task get(output REQ t);
      get_next_item(t);
    endtask

    virtual task peek(output REQ t);
      wait (m_req_fifo.size() > 0);
      t = m_req_fifo[0];
    endtask

    virtual task put(RSP t);
      m_rsp_fifo.push_back(t);
    endtask
  endclass

  //----------------------------------------------------------------------
  // uvm_driver - driver base class
  //----------------------------------------------------------------------
  class uvm_driver #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_component;
    uvm_seq_item_pull_port #(REQ, RSP) seq_item_port;
    uvm_analysis_port #(RSP) rsp_port;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      seq_item_port = new("seq_item_port", this);
      rsp_port = new("rsp_port", this);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_monitor - monitor base class
  //----------------------------------------------------------------------
  class uvm_monitor extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_agent - agent base class
  //----------------------------------------------------------------------
  class uvm_agent extends uvm_component;
    uvm_active_passive_enum is_active = UVM_ACTIVE;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
      return is_active;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_env - environment base class
  //----------------------------------------------------------------------
  class uvm_env extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_test - test base class
  //----------------------------------------------------------------------
  class uvm_test extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_subscriber - subscriber for analysis ports
  //----------------------------------------------------------------------
  virtual class uvm_subscriber #(type T = uvm_sequence_item) extends uvm_component;
    uvm_analysis_imp #(T, uvm_subscriber #(T)) analysis_export;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      analysis_export = new("analysis_export", this);
    endfunction

    pure virtual function void write(T t);
  endclass

  //----------------------------------------------------------------------
  // uvm_scoreboard - scoreboard base class
  //----------------------------------------------------------------------
  class uvm_scoreboard extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Analysis port base class for type-independent storage
  //----------------------------------------------------------------------
  virtual class uvm_analysis_imp_base extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction

    pure virtual function void write_object(uvm_object t);
  endclass

  //----------------------------------------------------------------------
  // Analysis ports
  //----------------------------------------------------------------------
  class uvm_analysis_port #(type T = uvm_object) extends uvm_object;
    protected uvm_component m_parent;
    protected uvm_analysis_imp_base m_subscribers[$];

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
    endfunction

    // Connect to any analysis imp (type-erased)
    virtual function void connect(uvm_analysis_imp_base imp);
      m_subscribers.push_back(imp);
    endfunction

    virtual function void write(T t);
      foreach (m_subscribers[i])
        m_subscribers[i].write_object(t);
    endfunction
  endclass

  class uvm_analysis_imp #(type T = uvm_object, type IMP = uvm_component) extends uvm_analysis_imp_base;
    protected IMP m_imp;

    function new(string name = "", IMP imp = null);
      super.new(name);
      m_imp = imp;
    endfunction

    virtual function void write(T t);
      // Call the write() method on the implementing class
      if (m_imp != null)
        m_imp.write(t);
    endfunction

    virtual function void write_object(uvm_object t);
      T item;
      if ($cast(item, t))
        write(item);
    endfunction
  endclass

  class uvm_analysis_export #(type T = uvm_object) extends uvm_object;
    protected uvm_analysis_imp_base m_imp;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
    endfunction

    virtual function void connect(uvm_analysis_imp_base imp);
      m_imp = imp;
    endfunction

    virtual function void write(T t);
      if (m_imp != null)
        m_imp.write_object(t);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // TLM ports
  //----------------------------------------------------------------------
  class uvm_seq_item_pull_port #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_object;
    protected uvm_component m_parent;
    protected uvm_sequencer #(REQ, RSP) m_sequencer;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
    endfunction

    virtual function void connect(uvm_sequencer #(REQ, RSP) sequencer);
      m_sequencer = sequencer;
    endfunction

    virtual task get_next_item(output REQ t);
      if (m_sequencer != null)
        m_sequencer.get_next_item(t);
    endtask

    virtual task try_next_item(output REQ t);
      if (m_sequencer != null)
        m_sequencer.try_next_item(t);
      else
        t = null;
    endtask

    virtual function void item_done(RSP item = null);
      if (m_sequencer != null)
        m_sequencer.item_done(item);
    endfunction

    virtual task get(output REQ t);
      get_next_item(t);
    endtask

    virtual task peek(output REQ t);
      if (m_sequencer != null)
        m_sequencer.peek(t);
    endtask

    virtual task put(RSP t);
      if (m_sequencer != null)
        m_sequencer.put(t);
    endtask
  endclass

  //----------------------------------------------------------------------
  // uvm_tlm_fifo - TLM FIFO
  //----------------------------------------------------------------------
  class uvm_tlm_fifo #(type T = uvm_sequence_item) extends uvm_component;
    protected T m_fifo[$];
    protected int m_size;

    function new(string name = "", uvm_component parent = null, int size = 1);
      super.new(name, parent);
      m_size = size;
    endfunction

    virtual task put(T t);
      if (m_size > 0) begin
        wait (m_fifo.size() < m_size);
      end
      m_fifo.push_back(t);
    endtask

    virtual function bit try_put(T t);
      if (m_size == 0 || m_fifo.size() < m_size) begin
        m_fifo.push_back(t);
        return 1;
      end
      return 0;
    endfunction

    virtual task get(output T t);
      wait (m_fifo.size() > 0);
      t = m_fifo.pop_front();
    endtask

    virtual function bit try_get(output T t);
      if (m_fifo.size() > 0) begin
        t = m_fifo.pop_front();
        return 1;
      end
      return 0;
    endfunction

    virtual task peek(output T t);
      wait (m_fifo.size() > 0);
      t = m_fifo[0];
    endtask

    virtual function bit try_peek(output T t);
      if (m_fifo.size() > 0) begin
        t = m_fifo[0];
        return 1;
      end
      return 0;
    endfunction

    virtual function int used();
      return m_fifo.size();
    endfunction

    virtual function bit is_empty();
      return m_fifo.size() == 0;
    endfunction

    virtual function bit is_full();
      return m_size > 0 && m_fifo.size() >= m_size;
    endfunction

    virtual function void flush();
      m_fifo.delete();
    endfunction

    virtual function int size();
      return m_size;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_tlm_analysis_fifo - TLM analysis FIFO
  //----------------------------------------------------------------------
  class uvm_tlm_analysis_fifo #(type T = uvm_sequence_item) extends uvm_component;
    protected T m_fifo[$];
    uvm_analysis_imp #(T, uvm_tlm_analysis_fifo #(T)) analysis_export;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      analysis_export = new("analysis_export", this);
    endfunction

    virtual function void write(T t);
      m_fifo.push_back(t);
    endfunction

    virtual task get(output T t);
      wait (m_fifo.size() > 0);
      t = m_fifo.pop_front();
    endtask

    virtual function bit try_get(output T t);
      if (m_fifo.size() > 0) begin
        t = m_fifo.pop_front();
        return 1;
      end
      return 0;
    endfunction

    virtual task peek(output T t);
      wait (m_fifo.size() > 0);
      t = m_fifo[0];
    endtask

    virtual function bit try_peek(output T t);
      if (m_fifo.size() > 0) begin
        t = m_fifo[0];
        return 1;
      end
      return 0;
    endfunction

    virtual function int used();
      return m_fifo.size();
    endfunction

    virtual function bit is_empty();
      return m_fifo.size() == 0;
    endfunction

    virtual function bit is_full();
      return 0;  // Unbounded FIFO
    endfunction

    virtual function void flush();
      m_fifo.delete();
    endfunction

    virtual function int size();
      return m_fifo.size();
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_config_db - configuration database
  // Functional implementation using associative arrays for storage
  //----------------------------------------------------------------------
  class uvm_config_db #(type T = int);
    // Storage for configuration values - keyed by "{context}:{inst_name}:{field_name}"
    static T m_config_db[string];
    // Track wildcard patterns separately for matching
    static string m_wildcard_keys[$];

    // Build a key from context and field info
    static function string build_key(uvm_component cntxt, string inst_name, string field_name);
      string context_path;
      if (cntxt != null)
        context_path = cntxt.get_full_name();
      else
        context_path = "";
      return {context_path, ":", inst_name, ":", field_name};
    endfunction

    // Check if a pattern matches a path (simple wildcard matching)
    static function bit match_pattern(string pattern, string path);
      // Handle common wildcard patterns
      if (pattern == "*" || pattern == "")
        return 1;
      // Check for "*" at end (e.g., "env*" matches "env.agent")
      if (pattern[pattern.len()-1] == "*") begin
        string prefix = pattern.substr(0, pattern.len()-2);
        if (path.len() >= prefix.len() && path.substr(0, prefix.len()-1) == prefix)
          return 1;
      end
      // Check for exact match
      if (pattern == path)
        return 1;
      // Check if pattern is contained in path
      foreach (path[i]) begin
        if (i + pattern.len() <= path.len()) begin
          if (path.substr(i, i + pattern.len() - 1) == pattern)
            return 1;
        end
      end
      return 0;
    endfunction

    static function void set(uvm_component cntxt, string inst_name, string field_name, T value);
      string key = build_key(cntxt, inst_name, field_name);
      m_config_db[key] = value;
      // Track if this has wildcards for later matching
      if (inst_name == "*" || inst_name.len() == 0 ||
          (inst_name.len() > 0 && inst_name[inst_name.len()-1] == "*")) begin
        // Check if already in wildcard list
        bit found = 0;
        foreach (m_wildcard_keys[i]) begin
          if (m_wildcard_keys[i] == key) begin
            found = 1;
            break;
          end
        end
        if (!found)
          m_wildcard_keys.push_back(key);
      end
    endfunction

    static function bit get(uvm_component cntxt, string inst_name, string field_name, inout T value);
      string key = build_key(cntxt, inst_name, field_name);
      string lookup_path;

      // First try exact match
      if (m_config_db.exists(key)) begin
        value = m_config_db[key];
        return 1;
      end

      // Build the full lookup path for wildcard matching
      if (cntxt != null)
        lookup_path = {cntxt.get_full_name(), ".", inst_name};
      else
        lookup_path = inst_name;

      // Try wildcard matches - check all wildcard keys
      foreach (m_wildcard_keys[i]) begin
        string wkey = m_wildcard_keys[i];
        // Extract the pattern from the key (format: context:inst_pattern:field_name)
        // We need to check if this key's field_name matches and inst_pattern matches lookup_path
        int colon1 = -1, colon2 = -1;
        foreach (wkey[j]) begin
          if (wkey[j] == ":") begin
            if (colon1 < 0) colon1 = j;
            else if (colon2 < 0) colon2 = j;
          end
        end
        if (colon1 >= 0 && colon2 > colon1) begin
          string key_context = wkey.substr(0, colon1-1);
          string key_inst = wkey.substr(colon1+1, colon2-1);
          string key_field = wkey.substr(colon2+1, wkey.len()-1);
          // Check if field name matches and pattern matches
          if (key_field == field_name) begin
            // Check context match (null context or "*" matches anything)
            bit context_ok = (key_context == "" || key_context == "*");
            if (!context_ok && cntxt != null) begin
              context_ok = match_pattern(key_context, cntxt.get_full_name());
            end
            if (context_ok && match_pattern(key_inst, lookup_path)) begin
              value = m_config_db[wkey];
              return 1;
            end
          end
        end
      end

      // Not found
      return 0;
    endfunction

    static function bit exists(uvm_component cntxt, string inst_name, string field_name);
      string key = build_key(cntxt, inst_name, field_name);
      if (m_config_db.exists(key))
        return 1;
      // For wildcard checking, we need to scan the wildcard keys
      foreach (m_wildcard_keys[i]) begin
        string wkey = m_wildcard_keys[i];
        int colon1 = -1, colon2 = -1;
        foreach (wkey[j]) begin
          if (wkey[j] == ":") begin
            if (colon1 < 0) colon1 = j;
            else if (colon2 < 0) colon2 = j;
          end
        end
        if (colon2 > colon1 && colon1 >= 0) begin
          string key_field = wkey.substr(colon2+1, wkey.len()-1);
          if (key_field == field_name)
            return 1;
        end
      end
      return 0;
    endfunction

    static function void wait_modified(uvm_component cntxt, string inst_name, string field_name);
      // Stub - immediate return (no event-based waiting in simple implementation)
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_resource_db - resource database (stub)
  //----------------------------------------------------------------------
  class uvm_resource_db #(type T = int);
    static function void set(string scope, string name, T val, uvm_object accessor = null);
      // Stub
    endfunction

    static function bit read_by_name(string scope, string name, inout T val, input uvm_object accessor = null);
      return 0;
    endfunction

    static function bit read_by_type(string scope, inout T val, input uvm_object accessor = null);
      return 0;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_root - the implicit top of the UVM hierarchy
  //----------------------------------------------------------------------
  class uvm_root extends uvm_component;
    protected static uvm_root m_inst;
    protected uvm_component m_test_top;

    function new(string name = "__top__");
      super.new(name, null);
    endfunction

    static function uvm_root get();
      if (m_inst == null) begin
        m_inst = new("__top__");
      end
      return m_inst;
    endfunction

    virtual function void print_topology(uvm_printer printer = null);
      print_topology_recursive(this, 0);
    endfunction

    protected function void print_topology_recursive(uvm_component comp, int level);
      string indent;
      uvm_component children[$];
      for (int i = 0; i < level; i++) indent = {indent, "  "};
      $display("%s%s (%s)", indent, comp.get_full_name() == "" ? "__top__" : comp.get_full_name(),
               comp.get_type_name());
      comp.get_children(children);
      foreach (children[i])
        print_topology_recursive(children[i], level + 1);
    endfunction

    virtual function string get_type_name();
      return "uvm_root";
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Global functions and variables
  //----------------------------------------------------------------------

  // Global top component (simulation root) - use get() to access
  uvm_root uvm_top;

  // Test done objection
  uvm_objection uvm_test_done;

  // Initialize globals at package load time
  function automatic void __uvm_pkg_init();
    if (uvm_top == null) begin
      uvm_top = uvm_root::get();
    end
    if (uvm_test_done == null) begin
      uvm_test_done = new("uvm_test_done");
    end
  endfunction

  // Run test function - creates test from factory and runs UVM phases
  task run_test(string test_name = "");
    uvm_component test_inst;
    uvm_phase build_ph, connect_ph, elab_ph, start_ph, run_ph, extract_ph, check_ph, report_ph, final_ph;

    // Ensure globals are initialized
    __uvm_pkg_init();

    $display("[UVM_INFO] @ %0t: run_test: Starting test '%s' [UVM]", $time, test_name);

    // Create phase objects
    build_ph = new("build");
    connect_ph = new("connect");
    elab_ph = new("end_of_elaboration");
    start_ph = new("start_of_simulation");
    run_ph = new("run");
    extract_ph = new("extract");
    check_ph = new("check");
    report_ph = new("report");
    final_ph = new("final");

    // Try to create test from factory
    if (test_name != "" && uvm_factory::is_type_registered(test_name)) begin
      $display("[UVM_INFO] @ %0t: run_test: Creating test '%s' from factory [UVM]", $time, test_name);
      test_inst = uvm_factory::create_component_by_name(test_name, "", test_name, uvm_top);
    end else if (test_name != "") begin
      $display("[UVM_WARNING] @ %0t: run_test: Test '%s' not found in factory [UVM]", $time, test_name);
      $display("[UVM_INFO] @ %0t: run_test: Registered types: %0d [UVM]", $time, uvm_factory::get_num_types());
      uvm_factory::print_all_types();
      $display("[UVM_INFO] @ %0t: run_test: Hint - Call <test_class>::type_id::register() before run_test() [UVM]", $time);
      // Fall through to waiting mode
    end

    if (test_inst != null) begin
      // Run UVM phases
      $display("[UVM_INFO] @ %0t: run_test: Starting build_phase [UVM]", $time);
      __run_build_phase(test_inst, build_ph);

      $display("[UVM_INFO] @ %0t: run_test: Starting connect_phase [UVM]", $time);
      __run_connect_phase(test_inst, connect_ph);

      $display("[UVM_INFO] @ %0t: run_test: Starting end_of_elaboration_phase [UVM]", $time);
      __run_elab_phase(test_inst, elab_ph);

      $display("[UVM_INFO] @ %0t: run_test: Starting start_of_simulation_phase [UVM]", $time);
      __run_start_phase(test_inst, start_ph);

      $display("[UVM_INFO] @ %0t: run_test: Starting run_phase [UVM]", $time);
      __run_run_phase(test_inst, run_ph);

      // Wait for all objections to be dropped
      $display("[UVM_INFO] @ %0t: run_test: Waiting for objections to drop [UVM]", $time);
      while (!run_ph.phase_done()) begin
        #10;
      end
      // Additional drain time
      #100;

      $display("[UVM_INFO] @ %0t: run_test: Starting extract_phase [UVM]", $time);
      __run_extract_phase(test_inst, extract_ph);

      $display("[UVM_INFO] @ %0t: run_test: Starting check_phase [UVM]", $time);
      __run_check_phase(test_inst, check_ph);

      $display("[UVM_INFO] @ %0t: run_test: Starting report_phase [UVM]", $time);
      __run_report_phase(test_inst, report_ph);

      $display("[UVM_INFO] @ %0t: run_test: Starting final_phase [UVM]", $time);
      __run_final_phase(test_inst, final_ph);

      $display("[UVM_INFO] @ %0t: run_test: Test complete [UVM]", $time);
      $finish;
    end else begin
      // No test created - wait for external finish
      $display("[UVM_INFO] @ %0t: run_test: No test instantiated, waiting for simulation... [UVM]", $time);
      forever begin
        #1000;
      end
    end
  endtask

  // Phase execution helpers - iteratively run phases on component hierarchy
  // Uses a work queue to avoid recursion which Verilator doesn't fully support

  function void __collect_components(uvm_component root, ref uvm_component list[$]);
    // Collect all components in tree order (root first)
    uvm_component queue[$];
    uvm_component comp;
    uvm_component children[$];

    queue.push_back(root);
    while (queue.size() > 0) begin
      comp = queue.pop_front();
      list.push_back(comp);
      comp.get_children(children);
      foreach (children[i])
        queue.push_back(children[i]);
      children.delete();
    end
  endfunction

  function void __run_build_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Build phase runs top-down
    foreach (comps[i])
      comps[i].build_phase(phase);
  endfunction

  function void __run_connect_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Connect phase runs bottom-up
    for (int i = comps.size()-1; i >= 0; i--)
      comps[i].connect_phase(phase);
  endfunction

  function void __run_elab_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Bottom-up
    for (int i = comps.size()-1; i >= 0; i--)
      comps[i].end_of_elaboration_phase(phase);
  endfunction

  function void __run_start_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Bottom-up
    for (int i = comps.size()-1; i >= 0; i--)
      comps[i].start_of_simulation_phase(phase);
  endfunction

  task __run_run_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Run phase launches all run_phase tasks in parallel
    foreach (comps[i]) begin
      automatic int idx = i;
      fork
        comps[idx].run_phase(phase);
      join_none
    end
  endtask

  function void __run_extract_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Bottom-up
    for (int i = comps.size()-1; i >= 0; i--)
      comps[i].extract_phase(phase);
  endfunction

  function void __run_check_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Bottom-up
    for (int i = comps.size()-1; i >= 0; i--)
      comps[i].check_phase(phase);
  endfunction

  function void __run_report_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Bottom-up
    for (int i = comps.size()-1; i >= 0; i--)
      comps[i].report_phase(phase);
  endfunction

  function void __run_final_phase(uvm_component root, uvm_phase phase);
    uvm_component comps[$];
    __collect_components(root, comps);
    // Bottom-up
    for (int i = comps.size()-1; i >= 0; i--)
      comps[i].final_phase(phase);
  endfunction

  // Factory function wrappers (use uvm_factory class)
  function uvm_object create_object_by_name(string type_name, string parent_inst_path = "",
                                             string name = "");
    return uvm_factory::create_object_by_name(type_name, parent_inst_path, name);
  endfunction

  function uvm_component create_component_by_name(string type_name, string parent_inst_path = "",
                                                   string name = "", uvm_component parent = null);
    return uvm_factory::create_component_by_name(type_name, parent_inst_path, name, parent);
  endfunction

  // Report functions
  function void uvm_report_info(string id, string message, int verbosity = UVM_MEDIUM,
                                 string filename = "", int line = 0);
    if (verbosity <= UVM_MEDIUM)
      $display("[UVM_INFO] @ %0t: %s [%s]", $time, message, id);
  endfunction

  function void uvm_report_warning(string id, string message, int verbosity = UVM_MEDIUM,
                                    string filename = "", int line = 0);
    $display("[UVM_WARNING] @ %0t: %s [%s]", $time, message, id);
  endfunction

  function void uvm_report_error(string id, string message, int verbosity = UVM_LOW,
                                  string filename = "", int line = 0);
    $display("[UVM_ERROR] @ %0t: %s [%s]", $time, message, id);
  endfunction

  function void uvm_report_fatal(string id, string message, int verbosity = UVM_NONE,
                                  string filename = "", int line = 0);
    $display("[UVM_FATAL] @ %0t: %s [%s]", $time, message, id);
    $fatal(1, "UVM Fatal");
  endfunction

endpackage : uvm_pkg
