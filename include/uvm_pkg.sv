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

  // Message severity levels
  typedef enum int {
    UVM_INFO    = 0,
    UVM_WARNING = 1,
    UVM_ERROR   = 2,
    UVM_FATAL   = 3
  } uvm_severity;

  // File handle type
  typedef int UVM_FILE;

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
  // UVM Register Abstraction Layer (RAL) types
  //----------------------------------------------------------------------

  // Register access type
  typedef enum {
    UVM_READ,
    UVM_WRITE,
    UVM_BURST_READ,
    UVM_BURST_WRITE
  } uvm_access_e;

  // Register status
  typedef enum {
    UVM_IS_OK,
    UVM_NOT_OK,
    UVM_HAS_X
  } uvm_status_e;

  // Register path type
  typedef enum {
    UVM_FRONTDOOR,
    UVM_BACKDOOR,
    UVM_PREDICT,
    UVM_DEFAULT_PATH
  } uvm_path_e;

  // Register bus operation struct
  typedef struct {
    uvm_access_e kind;
    logic [63:0] addr;
    logic [63:0] data;
    int n_bits;
    uvm_status_e status;
    logic [63:0] byte_en;
  } uvm_reg_bus_op;

  // Register data and address types
  typedef logic [63:0] uvm_reg_data_t;
  typedef logic [63:0] uvm_reg_addr_t;

  // Prediction type
  typedef enum {
    UVM_PREDICT_DIRECT,
    UVM_PREDICT_READ,
    UVM_PREDICT_WRITE
  } uvm_predict_e;

  // Hierarchy type
  typedef enum {
    UVM_HIER,
    UVM_FLAT
  } uvm_hier_e;

  // Endianness type
  typedef enum {
    UVM_LITTLE_ENDIAN,
    UVM_BIG_ENDIAN,
    UVM_LITTLE_FIFO,
    UVM_BIG_FIFO
  } uvm_endianness_e;

  // Add to access type (RW variant)
  localparam uvm_access_e UVM_RW = UVM_WRITE;  // For RAL field access

  //----------------------------------------------------------------------
  // Forward declarations
  //----------------------------------------------------------------------
  typedef class uvm_object;
  typedef class uvm_component;
  typedef class uvm_sequence_item;
  typedef class uvm_sequence_base;
  typedef class uvm_sequencer_base;
  typedef class uvm_phase;
  typedef class uvm_objection;
  typedef class uvm_object_wrapper;
  typedef class uvm_factory;
  typedef class uvm_comparer;
  typedef class uvm_printer;
  typedef class uvm_packer;
  typedef class uvm_recorder;
  typedef class uvm_analysis_imp_base;
  typedef class uvm_event;
  typedef class uvm_barrier;
  typedef class uvm_reg_adapter;

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

    // Type overrides: type_name -> override_type_name
    static local uvm_object_wrapper m_type_overrides[string];
    // Instance overrides: inst_path.type_name -> override_type_name
    static local uvm_object_wrapper m_inst_overrides[string];

    // Set type override - all instances of original_type use override_type
    static function void set_type_override_by_type(uvm_object_wrapper original_type,
                                                    uvm_object_wrapper override_type,
                                                    bit replace = 1);
      string type_name = original_type.get_type_name();
      if (replace || !m_type_overrides.exists(type_name))
        m_type_overrides[type_name] = override_type;
    endfunction

    // Set instance override - specific instance path uses override_type
    static function void set_inst_override_by_type(string inst_path,
                                                    uvm_object_wrapper original_type,
                                                    uvm_object_wrapper override_type);
      string key = {inst_path, ".", original_type.get_type_name()};
      m_inst_overrides[key] = override_type;
    endfunction

    // Set type override by name
    static function void set_type_override(string original_type_name,
                                            string override_type_name,
                                            bit replace = 1);
      if (m_type_registry.exists(override_type_name)) begin
        if (replace || !m_type_overrides.exists(original_type_name))
          m_type_overrides[original_type_name] = m_type_registry[override_type_name];
      end
    endfunction

    // Set instance override by name
    static function void set_inst_override(string original_type_name,
                                            string override_type_name,
                                            string inst_path);
      if (m_type_registry.exists(override_type_name)) begin
        string key = {inst_path, ".", original_type_name};
        m_inst_overrides[key] = m_type_registry[override_type_name];
      end
    endfunction

    // Get override for a type (checks instance then type overrides)
    static function uvm_object_wrapper get_override(string type_name, string inst_path = "");
      string key;
      // Check instance override first
      if (inst_path != "") begin
        key = {inst_path, ".", type_name};
        if (m_inst_overrides.exists(key))
          return m_inst_overrides[key];
      end
      // Check type override
      if (m_type_overrides.exists(type_name))
        return m_type_overrides[type_name];
      // Return original type
      if (m_type_registry.exists(type_name))
        return m_type_registry[type_name];
      return null;
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

  // Global factory override functions
  function void set_inst_override_by_type(string inst_path,
                                          uvm_object_wrapper original_type,
                                          uvm_object_wrapper override_type);
    uvm_factory::set_inst_override_by_type(inst_path, original_type, override_type);
  endfunction

  function void set_type_override_by_type(uvm_object_wrapper original_type,
                                          uvm_object_wrapper override_type,
                                          bit replace = 1);
    uvm_factory::set_type_override_by_type(original_type, override_type, replace);
  endfunction

  // Deferred registration helper for uvm_*_utils macros
  // Called by static initializer to ensure registration happens before run_test()
  // The type_id parameter forces the type_id class to be elaborated and its
  // get() function called, which triggers registration
  function bit __verilator_deferred_register(string type_name, uvm_object_wrapper type_id);
    // Registration already happened in type_id::get() call
    return 1;
  endfunction

  //----------------------------------------------------------------------
  // uvm_report_server - centralized message reporting and counts
  //----------------------------------------------------------------------
  typedef class uvm_report_server;

  class uvm_report_server;
    // Singleton instance
    static local uvm_report_server m_global_server;

    // Severity counts
    protected int m_info_count;
    protected int m_warning_count;
    protected int m_error_count;
    protected int m_fatal_count;

    // Message ID counts (id -> count)
    protected int m_id_counts[string];

    // Max quit count (simulation stops after this many errors)
    protected int m_max_quit_count = 10;
    protected int m_quit_count = 0;

    function new();
      m_info_count = 0;
      m_warning_count = 0;
      m_error_count = 0;
      m_fatal_count = 0;
    endfunction

    // Get the global report server
    static function uvm_report_server get_server();
      if (m_global_server == null)
        m_global_server = new();
      return m_global_server;
    endfunction

    // Set the global report server
    static function void set_server(uvm_report_server server);
      m_global_server = server;
    endfunction

    // Increment severity counts
    virtual function void incr_severity_count(uvm_severity severity);
      case (severity)
        UVM_INFO:    m_info_count++;
        UVM_WARNING: m_warning_count++;
        UVM_ERROR: begin
          m_error_count++;
          m_quit_count++;
          if (m_max_quit_count > 0 && m_quit_count >= m_max_quit_count) begin
            $display("[UVM_FATAL] Quit count reached max (%0d errors)", m_max_quit_count);
            $fatal(1, "UVM_ERROR count exceeded max_quit_count");
          end
        end
        UVM_FATAL:   m_fatal_count++;
      endcase
    endfunction

    // Increment ID count
    virtual function void incr_id_count(string id);
      if (m_id_counts.exists(id))
        m_id_counts[id]++;
      else
        m_id_counts[id] = 1;
    endfunction

    // Get severity counts
    virtual function int get_severity_count(uvm_severity severity);
      case (severity)
        UVM_INFO:    return m_info_count;
        UVM_WARNING: return m_warning_count;
        UVM_ERROR:   return m_error_count;
        UVM_FATAL:   return m_fatal_count;
        default:     return 0;
      endcase
    endfunction

    // Get ID count
    virtual function int get_id_count(string id);
      if (m_id_counts.exists(id))
        return m_id_counts[id];
      return 0;
    endfunction

    // Set/get max quit count
    virtual function void set_max_quit_count(int count);
      m_max_quit_count = count;
    endfunction

    virtual function int get_max_quit_count();
      return m_max_quit_count;
    endfunction

    virtual function int get_quit_count();
      return m_quit_count;
    endfunction

    virtual function void set_quit_count(int count);
      m_quit_count = count;
    endfunction

    // Reset counts
    virtual function void reset_severity_counts();
      m_info_count = 0;
      m_warning_count = 0;
      m_error_count = 0;
      m_fatal_count = 0;
    endfunction

    virtual function void reset_quit_count();
      m_quit_count = 0;
    endfunction

    // Report summary
    virtual function void report_summarize(UVM_FILE file = 0);
      $display("\n--- UVM Report Summary ---");
      $display("");
      $display("** Report counts by severity");
      $display("UVM_INFO:    %0d", m_info_count);
      $display("UVM_WARNING: %0d", m_warning_count);
      $display("UVM_ERROR:   %0d", m_error_count);
      $display("UVM_FATAL:   %0d", m_fatal_count);
      $display("");
      if (m_error_count > 0 || m_fatal_count > 0)
        $display("** TEST FAILED **");
      else
        $display("** TEST PASSED **");
      $display("--------------------------\n");
    endfunction

    // Compose message (can be overridden for custom formatting)
    virtual function string compose_message(uvm_severity severity,
                                            string name,
                                            string id,
                                            string message,
                                            string filename,
                                            int line);
      string severity_str;
      case (severity)
        UVM_INFO:    severity_str = "UVM_INFO";
        UVM_WARNING: severity_str = "UVM_WARNING";
        UVM_ERROR:   severity_str = "UVM_ERROR";
        UVM_FATAL:   severity_str = "UVM_FATAL";
        default:     severity_str = "UVM_UNKNOWN";
      endcase
      return $sformatf("[%s] %s(%0d) @ %0t: %s [%s]",
                       severity_str, filename, line, $time, message, id);
    endfunction
  endclass

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
  // uvm_event - event synchronization class
  // Provides event-based synchronization between processes
  //----------------------------------------------------------------------
  class uvm_event #(type T = uvm_object) extends uvm_object;
    protected bit m_triggered;
    protected time m_trigger_time;
    protected T m_data;
    protected event m_event;
    protected int m_num_waiters;

    function new(string name = "uvm_event");
      super.new(name);
      m_triggered = 0;
      m_trigger_time = 0;
      m_data = null;
      m_num_waiters = 0;
    endfunction

    // Trigger the event, optionally passing data
    virtual function void trigger(T data = null);
      m_triggered = 1;
      m_trigger_time = $time;
      m_data = data;
      -> m_event;
    endfunction

    // Check if event is triggered (on)
    virtual function bit is_on();
      return m_triggered;
    endfunction

    // Check if event is not triggered (off)
    virtual function bit is_off();
      return !m_triggered;
    endfunction

    // Reset the event to untriggered state
    virtual function void reset(bit wakeup = 0);
      m_triggered = 0;
      m_data = null;
      if (wakeup) -> m_event;  // Wake up waiters even on reset
    endfunction

    // Get the time when event was triggered
    virtual function time get_trigger_time();
      return m_trigger_time;
    endfunction

    // Get the data passed with trigger
    virtual function T get_trigger_data();
      return m_data;
    endfunction

    // Get number of processes waiting
    virtual function int get_num_waiters();
      return m_num_waiters;
    endfunction

    // Wait for the event to be triggered
    virtual task wait_trigger();
      m_num_waiters++;
      if (!m_triggered)
        @(m_event);
      m_num_waiters--;
    endtask

    // Wait for event if already on, or wait for next trigger
    virtual task wait_on(bit delta = 0);
      if (m_triggered) begin
        if (delta) #0;  // Wait a delta cycle if requested
        return;
      end
      m_num_waiters++;
      @(m_event);
      m_num_waiters--;
    endtask

    // Wait for event to be off
    virtual task wait_off(bit delta = 0);
      if (!m_triggered) begin
        if (delta) #0;
        return;
      end
      m_num_waiters++;
      wait (!m_triggered);
      m_num_waiters--;
    endtask

    // Wait for trigger and get the data
    virtual task wait_trigger_data(output T data);
      wait_trigger();
      data = m_data;
    endtask

    // Wait and clear in one operation (for one-shot events)
    virtual task wait_ptrigger();
      m_num_waiters++;
      @(m_event);
      m_num_waiters--;
    endtask

    // Add callback (stub - not implemented)
    virtual function void add_callback(uvm_object cb, bit append = 1);
      // Callbacks not implemented in simple version
    endfunction

    // Delete callback (stub - not implemented)
    virtual function void delete_callback(uvm_object cb);
      // Callbacks not implemented in simple version
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_barrier - barrier synchronization class
  // Allows multiple processes to synchronize at a barrier point
  //----------------------------------------------------------------------
  class uvm_barrier extends uvm_object;
    protected int m_threshold;
    protected int m_num_waiters;
    protected bit m_auto_reset;
    protected event m_barrier_event;

    function new(string name = "uvm_barrier", int threshold = 0);
      super.new(name);
      m_threshold = threshold;
      m_num_waiters = 0;
      m_auto_reset = 1;
    endfunction

    // Set the threshold (number of processes to wait for)
    virtual function void set_threshold(int threshold);
      m_threshold = threshold;
    endfunction

    // Get current threshold
    virtual function int get_threshold();
      return m_threshold;
    endfunction

    // Set auto-reset mode
    virtual function void set_auto_reset(bit value = 1);
      m_auto_reset = value;
    endfunction

    // Get auto-reset mode
    virtual function bit get_auto_reset();
      return m_auto_reset;
    endfunction

    // Get number of processes waiting at barrier
    virtual function int get_num_waiters();
      return m_num_waiters;
    endfunction

    // Wait at the barrier
    virtual task wait_for();
      m_num_waiters++;
      if (m_num_waiters >= m_threshold) begin
        // Threshold reached, release all waiters
        -> m_barrier_event;
        if (m_auto_reset)
          m_num_waiters = 0;
      end else begin
        @(m_barrier_event);
      end
      // Decrement after wakeup (but not if auto-reset already did it)
      if (!m_auto_reset || m_num_waiters > 0)
        m_num_waiters--;
    endtask

    // Reset the barrier
    virtual function void reset(bit wakeup = 1);
      if (wakeup && m_num_waiters > 0)
        -> m_barrier_event;
      m_num_waiters = 0;
    endfunction

    // Cancel barrier (alias for reset with wakeup)
    virtual function void cancel();
      reset(1);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_heartbeat - watchdog for detecting deadlocks/hangs
  //----------------------------------------------------------------------
  typedef enum int {
    UVM_NO_HB_MODE,      // Heartbeat disabled
    UVM_ALL_ACTIVE,      // All components must be active
    UVM_ONE_ACTIVE,      // At least one component must be active
    UVM_ANY_ACTIVE       // Same as ONE_ACTIVE
  } uvm_heartbeat_modes;

  class uvm_heartbeat extends uvm_object;
    protected uvm_component m_cntxt;
    protected uvm_objection m_objection;
    protected uvm_component m_comp_list[$];
    protected uvm_heartbeat_modes m_mode;
    protected time m_hb_window;
    protected bit m_started;
    protected int unsigned m_cnt;
    protected event m_stop_event;

    function new(string name = "uvm_heartbeat", uvm_component cntxt = null, uvm_objection objection = null);
      super.new(name);
      m_cntxt = cntxt;
      m_objection = objection;
      m_mode = UVM_NO_HB_MODE;
      m_hb_window = 0;
      m_started = 0;
      m_cnt = 0;
    endfunction

    // Set heartbeat mode
    virtual function void set_mode(uvm_heartbeat_modes mode);
      m_mode = mode;
    endfunction

    // Set heartbeat window (timeout)
    virtual function void set_heartbeat(time hbs, uvm_component comps[$]);
      m_hb_window = hbs;
      m_comp_list = comps;
    endfunction

    // Add components to monitor
    virtual function void add(uvm_component comp);
      m_comp_list.push_back(comp);
    endfunction

    // Remove component from monitor
    virtual function void remove(uvm_component comp);
      foreach (m_comp_list[i]) begin
        if (m_comp_list[i] == comp) begin
          m_comp_list.delete(i);
          return;
        end
      end
    endfunction

    // Signal activity (heartbeat) from a component
    virtual function void raise_objection(uvm_object obj = null, string description = "", int count = 1);
      m_cnt++;
    endfunction

    // Start heartbeat monitoring
    virtual task start(uvm_event e = null);
      m_started = 1;
      fork
        begin
          while (m_started) begin
            int last_cnt = m_cnt;
            #(m_hb_window);
            if (!m_started) break;
            if (m_mode != UVM_NO_HB_MODE && m_cnt == last_cnt) begin
              $display("[UVM_FATAL] Heartbeat timeout - no activity in %0t", m_hb_window);
              $fatal(1, "Heartbeat timeout");
            end
          end
        end
        begin
          @(m_stop_event);
        end
      join_any
      disable fork;
    endtask

    // Stop heartbeat monitoring
    virtual function void stop();
      m_started = 0;
      -> m_stop_event;
    endfunction

    // Check if heartbeat is running
    virtual function bit is_started();
      return m_started;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_reg_adapter - base class for register adapters
  // Converts between register operations and bus transactions
  //----------------------------------------------------------------------
  class uvm_reg_adapter extends uvm_object;
    // Configuration for adapter behavior
    bit supports_byte_enable;
    bit provides_responses;

    function new(string name = "uvm_reg_adapter");
      super.new(name);
      supports_byte_enable = 0;
      provides_responses = 0;
    endfunction

    // Convert a register operation to a bus transaction
    // Must be overridden in derived class
    virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
      $fatal(1, "UVM_REG_ADAPTER: reg2bus must be implemented in derived class");
      return null;
    endfunction

    // Convert a bus transaction to a register operation
    // Must be overridden in derived class
    virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
      $fatal(1, "UVM_REG_ADAPTER: bus2reg must be implemented in derived class");
    endfunction

    // Get the parent sequence for bus item (optional override)
    virtual function uvm_sequence_base get_parent_sequence();
      return null;
    endfunction

    // Get the sequencer for bus item (optional override)
    virtual function uvm_sequencer_base get_sequencer();
      return null;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Forward declarations for RAL classes
  //----------------------------------------------------------------------
  typedef class uvm_reg;
  typedef class uvm_reg_field;
  typedef class uvm_reg_block;
  typedef class uvm_reg_map;
  typedef class uvm_mem;

  //----------------------------------------------------------------------
  // uvm_reg_field - Individual field within a register
  //----------------------------------------------------------------------
  class uvm_reg_field extends uvm_object;
    protected uvm_reg m_parent;
    protected int unsigned m_lsb;
    protected int unsigned m_size;
    protected bit m_volatile;
    protected uvm_access_e m_access;
    protected uvm_reg_data_t m_reset;
    protected uvm_reg_data_t m_value;
    protected uvm_reg_data_t m_mirrored;
    protected string m_name;

    function new(string name = "uvm_reg_field");
      super.new(name);
      m_name = name;
      m_volatile = 0;
      m_access = UVM_RW;
      m_reset = 0;
      m_value = 0;
      m_mirrored = 0;
    endfunction

    // Configure the field
    function void configure(uvm_reg parent,
                           int unsigned size,
                           int unsigned lsb_pos,
                           string access,
                           bit volatile_field,
                           uvm_reg_data_t reset,
                           bit has_reset,
                           bit is_rand,
                           bit individually_accessible);
      m_parent = parent;
      m_size = size;
      m_lsb = lsb_pos;
      m_volatile = volatile_field;
      m_reset = reset;
      m_value = reset;
      m_mirrored = reset;

      case (access)
        "RO": m_access = UVM_READ;
        "RW": m_access = UVM_RW;
        "WO": m_access = UVM_WRITE;
        default: m_access = UVM_RW;
      endcase
    endfunction

    // Get field properties
    virtual function string get_name();
      return m_name;
    endfunction

    virtual function int unsigned get_n_bits();
      return m_size;
    endfunction

    virtual function int unsigned get_lsb_pos();
      return m_lsb;
    endfunction

    virtual function uvm_access_e get_access(uvm_reg_map map = null);
      return m_access;
    endfunction

    virtual function uvm_reg get_parent();
      return m_parent;
    endfunction

    virtual function uvm_reg get_register();
      return m_parent;
    endfunction

    // Value access
    virtual function uvm_reg_data_t get();
      return m_value;
    endfunction

    virtual function void set(uvm_reg_data_t value, string fname = "", int lineno = 0);
      uvm_reg_data_t mask = (1 << m_size) - 1;
      m_value = value & mask;
    endfunction

    virtual function uvm_reg_data_t get_mirrored_value();
      return m_mirrored;
    endfunction

    virtual function uvm_reg_data_t get_reset(string kind = "HARD");
      return m_reset;
    endfunction

    virtual function void reset(string kind = "HARD");
      m_value = m_reset;
      m_mirrored = m_reset;
    endfunction

    virtual function bit needs_update();
      return m_value != m_mirrored;
    endfunction

    // Predict value after access
    virtual function void predict(uvm_reg_data_t value, uvm_predict_e kind = UVM_PREDICT_DIRECT);
      uvm_reg_data_t mask = (1 << m_size) - 1;
      m_mirrored = value & mask;
      if (kind == UVM_PREDICT_DIRECT)
        m_value = m_mirrored;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_reg - Register abstraction
  //----------------------------------------------------------------------
  class uvm_reg extends uvm_object;
    protected uvm_reg_block m_parent;
    protected uvm_reg_field m_fields[$];
    protected int unsigned m_n_bits;
    protected int unsigned m_n_used_bits;
    protected bit m_locked;
    protected uvm_reg_data_t m_reset;
    protected string m_name;

    function new(string name = "uvm_reg", int unsigned n_bits = 32, int has_coverage = 0);
      super.new(name);
      m_name = name;
      m_n_bits = n_bits;
      m_n_used_bits = 0;
      m_locked = 0;
      m_reset = 0;
    endfunction

    // Configure the register
    function void configure(uvm_reg_block blk_parent,
                           uvm_reg_file regfile_parent = null,
                           string hdl_path = "");
      m_parent = blk_parent;
      if (blk_parent != null)
        blk_parent.add_reg(this);
    endfunction

    // Add a field to this register
    function void add_field(uvm_reg_field field);
      m_fields.push_back(field);
      m_n_used_bits += field.get_n_bits();
    endfunction

    // Get register properties
    virtual function string get_name();
      return m_name;
    endfunction

    virtual function int unsigned get_n_bits();
      return m_n_bits;
    endfunction

    virtual function int unsigned get_n_bytes();
      return (m_n_bits + 7) / 8;
    endfunction

    virtual function uvm_reg_block get_parent();
      return m_parent;
    endfunction

    virtual function uvm_reg_block get_block();
      return m_parent;
    endfunction

    // Get all fields
    virtual function void get_fields(ref uvm_reg_field fields[$]);
      fields = m_fields;
    endfunction

    virtual function uvm_reg_field get_field_by_name(string name);
      foreach (m_fields[i])
        if (m_fields[i].get_name() == name)
          return m_fields[i];
      return null;
    endfunction

    // Value access - composite of all fields
    virtual function uvm_reg_data_t get();
      uvm_reg_data_t value = 0;
      foreach (m_fields[i]) begin
        value |= m_fields[i].get() << m_fields[i].get_lsb_pos();
      end
      return value;
    endfunction

    virtual function void set(uvm_reg_data_t value, string fname = "", int lineno = 0);
      foreach (m_fields[i]) begin
        uvm_reg_data_t field_val = (value >> m_fields[i].get_lsb_pos()) &
                                   ((1 << m_fields[i].get_n_bits()) - 1);
        m_fields[i].set(field_val);
      end
    endfunction

    virtual function uvm_reg_data_t get_mirrored_value();
      uvm_reg_data_t value = 0;
      foreach (m_fields[i]) begin
        value |= m_fields[i].get_mirrored_value() << m_fields[i].get_lsb_pos();
      end
      return value;
    endfunction

    virtual function uvm_reg_data_t get_reset(string kind = "HARD");
      uvm_reg_data_t value = 0;
      foreach (m_fields[i]) begin
        value |= m_fields[i].get_reset(kind) << m_fields[i].get_lsb_pos();
      end
      return value;
    endfunction

    virtual function void reset(string kind = "HARD");
      foreach (m_fields[i])
        m_fields[i].reset(kind);
    endfunction

    virtual function bit needs_update();
      foreach (m_fields[i])
        if (m_fields[i].needs_update())
          return 1;
      return 0;
    endfunction

    // Predict value after access
    virtual function void predict(uvm_reg_data_t value, uvm_predict_e kind = UVM_PREDICT_DIRECT);
      foreach (m_fields[i]) begin
        uvm_reg_data_t field_val = (value >> m_fields[i].get_lsb_pos()) &
                                   ((1 << m_fields[i].get_n_bits()) - 1);
        m_fields[i].predict(field_val, kind);
      end
    endfunction

    // Lock configuration
    virtual function void lock_model();
      m_locked = 1;
    endfunction

    virtual function bit is_locked();
      return m_locked;
    endfunction

    // Read/write tasks - to be overridden or use through map
    virtual task read(output uvm_status_e status,
                      output uvm_reg_data_t value,
                      input uvm_path_e path = UVM_DEFAULT_PATH,
                      input uvm_reg_map map = null,
                      input uvm_sequence_base parent = null,
                      input int prior = -1,
                      input uvm_object extension = null,
                      input string fname = "",
                      input int lineno = 0);
      status = UVM_NOT_OK;
      value = 0;
      $display("[UVM_WARNING] uvm_reg::read not implemented - use through map");
    endtask

    virtual task write(output uvm_status_e status,
                       input uvm_reg_data_t value,
                       input uvm_path_e path = UVM_DEFAULT_PATH,
                       input uvm_reg_map map = null,
                       input uvm_sequence_base parent = null,
                       input int prior = -1,
                       input uvm_object extension = null,
                       input string fname = "",
                       input int lineno = 0);
      status = UVM_NOT_OK;
      $display("[UVM_WARNING] uvm_reg::write not implemented - use through map");
    endtask
  endclass

  //----------------------------------------------------------------------
  // uvm_mem - Memory abstraction
  //----------------------------------------------------------------------
  class uvm_mem extends uvm_object;
    protected uvm_reg_block m_parent;
    protected longint unsigned m_size;
    protected int unsigned m_n_bits;
    protected uvm_access_e m_access;
    protected string m_name;
    protected uvm_reg_data_t m_mem[longint unsigned];

    function new(string name = "uvm_mem",
                 longint unsigned size = 0,
                 int unsigned n_bits = 32,
                 string access = "RW",
                 int has_coverage = 0);
      super.new(name);
      m_name = name;
      m_size = size;
      m_n_bits = n_bits;
      case (access)
        "RO": m_access = UVM_READ;
        "RW": m_access = UVM_RW;
        "WO": m_access = UVM_WRITE;
        default: m_access = UVM_RW;
      endcase
    endfunction

    // Configure the memory
    function void configure(uvm_reg_block parent, string hdl_path = "");
      m_parent = parent;
      if (parent != null)
        parent.add_mem(this);
    endfunction

    // Get memory properties
    virtual function string get_name();
      return m_name;
    endfunction

    virtual function longint unsigned get_size();
      return m_size;
    endfunction

    virtual function int unsigned get_n_bits();
      return m_n_bits;
    endfunction

    virtual function int unsigned get_n_bytes();
      return (m_n_bits + 7) / 8;
    endfunction

    virtual function uvm_access_e get_access(uvm_reg_map map = null);
      return m_access;
    endfunction

    virtual function uvm_reg_block get_parent();
      return m_parent;
    endfunction

    virtual function uvm_reg_block get_block();
      return m_parent;
    endfunction

    // Direct memory access (for backdoor)
    virtual function uvm_reg_data_t peek(longint unsigned offset);
      if (m_mem.exists(offset))
        return m_mem[offset];
      return 0;
    endfunction

    virtual function void poke(longint unsigned offset, uvm_reg_data_t value);
      m_mem[offset] = value;
    endfunction

    // Read/write tasks
    virtual task read(output uvm_status_e status,
                      input longint unsigned offset,
                      output uvm_reg_data_t value,
                      input uvm_path_e path = UVM_DEFAULT_PATH,
                      input uvm_reg_map map = null,
                      input uvm_sequence_base parent = null,
                      input int prior = -1,
                      input uvm_object extension = null,
                      input string fname = "",
                      input int lineno = 0);
      if (offset < m_size) begin
        value = peek(offset);
        status = UVM_IS_OK;
      end else begin
        value = 0;
        status = UVM_NOT_OK;
      end
    endtask

    virtual task write(output uvm_status_e status,
                       input longint unsigned offset,
                       input uvm_reg_data_t value,
                       input uvm_path_e path = UVM_DEFAULT_PATH,
                       input uvm_reg_map map = null,
                       input uvm_sequence_base parent = null,
                       input int prior = -1,
                       input uvm_object extension = null,
                       input string fname = "",
                       input int lineno = 0);
      if (offset < m_size) begin
        poke(offset, value);
        status = UVM_IS_OK;
      end else begin
        status = UVM_NOT_OK;
      end
    endtask
  endclass

  //----------------------------------------------------------------------
  // uvm_reg_map - Address map for registers
  //----------------------------------------------------------------------
  class uvm_reg_map extends uvm_object;
    protected uvm_reg_block m_parent;
    protected uvm_reg_addr_t m_base_addr;
    protected int unsigned m_n_bytes;
    protected uvm_endianness_e m_endian;
    protected string m_name;
    protected uvm_reg m_regs_by_offset[uvm_reg_addr_t];
    protected uvm_mem m_mems_by_offset[uvm_reg_addr_t];
    protected uvm_reg_map m_submaps[$];
    protected uvm_sequencer_base m_sequencer;
    protected uvm_reg_adapter m_adapter;

    function new(string name = "uvm_reg_map");
      super.new(name);
      m_name = name;
      m_base_addr = 0;
      m_n_bytes = 4;
      m_endian = UVM_LITTLE_ENDIAN;
    endfunction

    // Configure the map
    function void configure(uvm_reg_block parent,
                           uvm_reg_addr_t base_addr,
                           int unsigned n_bytes,
                           uvm_endianness_e endian,
                           bit byte_addressing = 1);
      m_parent = parent;
      m_base_addr = base_addr;
      m_n_bytes = n_bytes;
      m_endian = endian;
    endfunction

    // Get map properties
    virtual function string get_name();
      return m_name;
    endfunction

    virtual function string get_full_name();
      if (m_parent != null)
        return {m_parent.get_full_name(), ".", m_name};
      return m_name;
    endfunction

    virtual function uvm_reg_addr_t get_base_addr(uvm_hier_e hier = UVM_HIER);
      return m_base_addr;
    endfunction

    virtual function int unsigned get_n_bytes(uvm_hier_e hier = UVM_HIER);
      return m_n_bytes;
    endfunction

    virtual function uvm_endianness_e get_endian(uvm_hier_e hier = UVM_HIER);
      return m_endian;
    endfunction

    virtual function uvm_reg_block get_parent();
      return m_parent;
    endfunction

    // Add register to map
    virtual function void add_reg(uvm_reg rg, uvm_reg_addr_t offset,
                                  string rights = "RW", bit unmapped = 0,
                                  uvm_reg_frontdoor frontdoor = null);
      m_regs_by_offset[offset] = rg;
    endfunction

    // Add memory to map
    virtual function void add_mem(uvm_mem mem, uvm_reg_addr_t offset,
                                  string rights = "RW", bit unmapped = 0,
                                  uvm_reg_frontdoor frontdoor = null);
      m_mems_by_offset[offset] = mem;
    endfunction

    // Add submap
    virtual function void add_submap(uvm_reg_map child_map, uvm_reg_addr_t offset);
      m_submaps.push_back(child_map);
    endfunction

    // Get register by offset
    virtual function uvm_reg get_reg_by_offset(uvm_reg_addr_t offset, bit read = 1);
      if (m_regs_by_offset.exists(offset))
        return m_regs_by_offset[offset];
      return null;
    endfunction

    // Get memory by offset
    virtual function uvm_mem get_mem_by_offset(uvm_reg_addr_t offset);
      if (m_mems_by_offset.exists(offset))
        return m_mems_by_offset[offset];
      return null;
    endfunction

    // Get all registers
    virtual function void get_registers(ref uvm_reg regs[$], input uvm_hier_e hier = UVM_HIER);
      foreach (m_regs_by_offset[offset])
        regs.push_back(m_regs_by_offset[offset]);
    endfunction

    // Get all memories
    virtual function void get_memories(ref uvm_mem mems[$], input uvm_hier_e hier = UVM_HIER);
      foreach (m_mems_by_offset[offset])
        mems.push_back(m_mems_by_offset[offset]);
    endfunction

    // Set/get sequencer and adapter
    virtual function void set_sequencer(uvm_sequencer_base sequencer,
                                        uvm_reg_adapter adapter = null);
      m_sequencer = sequencer;
      m_adapter = adapter;
    endfunction

    virtual function uvm_sequencer_base get_sequencer();
      return m_sequencer;
    endfunction

    virtual function uvm_reg_adapter get_adapter();
      return m_adapter;
    endfunction

    // Get offset of a register
    virtual function uvm_reg_addr_t get_reg_offset(uvm_reg rg, uvm_hier_e hier = UVM_FLAT);
      foreach (m_regs_by_offset[offset])
        if (m_regs_by_offset[offset] == rg)
          return offset;
      return -1;
    endfunction

    // Get offset of a memory
    virtual function uvm_reg_addr_t get_mem_offset(uvm_mem mem, uvm_hier_e hier = UVM_FLAT);
      foreach (m_mems_by_offset[offset])
        if (m_mems_by_offset[offset] == mem)
          return offset;
      return -1;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_reg_block - Container for registers and memories
  //----------------------------------------------------------------------
  class uvm_reg_block extends uvm_object;
    protected uvm_reg_block m_parent;
    protected uvm_reg m_regs[$];
    protected uvm_mem m_mems[$];
    protected uvm_reg_map m_maps[$];
    protected uvm_reg_map m_default_map;
    protected uvm_reg_block m_children[$];
    protected bit m_locked;
    protected string m_name;

    function new(string name = "uvm_reg_block", int has_coverage = 0);
      super.new(name);
      m_name = name;
      m_locked = 0;
    endfunction

    // Configure the block
    function void configure(uvm_reg_block parent = null, string hdl_path = "");
      m_parent = parent;
      if (parent != null)
        parent.add_block(this);
    endfunction

    // Create a map for this block
    virtual function uvm_reg_map create_map(string name,
                                            uvm_reg_addr_t base_addr,
                                            int unsigned n_bytes,
                                            uvm_endianness_e endian,
                                            bit byte_addressing = 1);
      uvm_reg_map map = new(name);
      map.configure(this, base_addr, n_bytes, endian, byte_addressing);
      m_maps.push_back(map);
      if (m_default_map == null)
        m_default_map = map;
      return map;
    endfunction

    // Get block properties
    virtual function string get_name();
      return m_name;
    endfunction

    virtual function string get_full_name();
      if (m_parent != null)
        return {m_parent.get_full_name(), ".", m_name};
      return m_name;
    endfunction

    virtual function uvm_reg_block get_parent();
      return m_parent;
    endfunction

    // Add register
    virtual function void add_reg(uvm_reg rg);
      m_regs.push_back(rg);
    endfunction

    // Add memory
    virtual function void add_mem(uvm_mem mem);
      m_mems.push_back(mem);
    endfunction

    // Add child block
    virtual function void add_block(uvm_reg_block child);
      m_children.push_back(child);
    endfunction

    // Get all registers
    virtual function void get_registers(ref uvm_reg regs[$], input uvm_hier_e hier = UVM_HIER);
      regs = m_regs;
      if (hier == UVM_HIER) begin
        foreach (m_children[i]) begin
          uvm_reg child_regs[$];
          m_children[i].get_registers(child_regs, hier);
          foreach (child_regs[j])
            regs.push_back(child_regs[j]);
        end
      end
    endfunction

    // Get all memories
    virtual function void get_memories(ref uvm_mem mems[$], input uvm_hier_e hier = UVM_HIER);
      mems = m_mems;
      if (hier == UVM_HIER) begin
        foreach (m_children[i]) begin
          uvm_mem child_mems[$];
          m_children[i].get_memories(child_mems, hier);
          foreach (child_mems[j])
            mems.push_back(child_mems[j]);
        end
      end
    endfunction

    // Get all maps
    virtual function void get_maps(ref uvm_reg_map maps[$]);
      maps = m_maps;
    endfunction

    virtual function uvm_reg_map get_map_by_name(string name);
      foreach (m_maps[i])
        if (m_maps[i].get_name() == name)
          return m_maps[i];
      return null;
    endfunction

    virtual function uvm_reg_map get_default_map();
      return m_default_map;
    endfunction

    virtual function void set_default_map(uvm_reg_map map);
      m_default_map = map;
    endfunction

    // Get register by name
    virtual function uvm_reg get_reg_by_name(string name);
      foreach (m_regs[i])
        if (m_regs[i].get_name() == name)
          return m_regs[i];
      foreach (m_children[i]) begin
        uvm_reg rg = m_children[i].get_reg_by_name(name);
        if (rg != null)
          return rg;
      end
      return null;
    endfunction

    // Get memory by name
    virtual function uvm_mem get_mem_by_name(string name);
      foreach (m_mems[i])
        if (m_mems[i].get_name() == name)
          return m_mems[i];
      foreach (m_children[i]) begin
        uvm_mem mem = m_children[i].get_mem_by_name(name);
        if (mem != null)
          return mem;
      end
      return null;
    endfunction

    // Get child blocks
    virtual function void get_blocks(ref uvm_reg_block blks[$], input uvm_hier_e hier = UVM_HIER);
      blks = m_children;
    endfunction

    // Lock configuration
    virtual function void lock_model();
      m_locked = 1;
      foreach (m_regs[i])
        m_regs[i].lock_model();
      foreach (m_children[i])
        m_children[i].lock_model();
    endfunction

    virtual function bit is_locked();
      return m_locked;
    endfunction

    // Reset all registers
    virtual function void reset(string kind = "HARD");
      foreach (m_regs[i])
        m_regs[i].reset(kind);
      foreach (m_children[i])
        m_children[i].reset(kind);
    endfunction
  endclass

  // Typedef for frontdoor (placeholder)
  typedef class uvm_reg_frontdoor;
  class uvm_reg_frontdoor extends uvm_object;
    function new(string name = "uvm_reg_frontdoor");
      super.new(name);
    endfunction
  endclass

  // Typedef for reg file (placeholder)
  typedef class uvm_reg_file;
  class uvm_reg_file extends uvm_object;
    function new(string name = "uvm_reg_file");
      super.new(name);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_pool - parameterized pool for sharing objects
  // Used for sharing objects across the testbench hierarchy
  //----------------------------------------------------------------------
  class uvm_pool #(type KEY = int, type T = uvm_object) extends uvm_object;
    protected T pool[KEY];

    function new(string name = "uvm_pool");
      super.new(name);
    endfunction

    // Add an item to the pool
    virtual function void add(KEY key, T item);
      pool[key] = item;
    endfunction

    // Get an item from the pool
    virtual function T get(KEY key);
      if (pool.exists(key))
        return pool[key];
      else
        return null;
    endfunction

    // Check if key exists
    virtual function bit exists(KEY key);
      return pool.exists(key);
    endfunction

    // Delete an item
    virtual function void delete(KEY key);
      if (pool.exists(key))
        pool.delete(key);
    endfunction

    // Get number of items
    virtual function int num();
      return pool.num();
    endfunction

    // Get first key
    virtual function bit first(ref KEY key);
      return pool.first(key) != 0;
    endfunction

    // Get next key
    virtual function bit next(ref KEY key);
      return pool.next(key) != 0;
    endfunction

    // Get last key
    virtual function bit last(ref KEY key);
      return pool.last(key) != 0;
    endfunction

    // Get prev key
    virtual function bit prev(ref KEY key);
      return pool.prev(key) != 0;
    endfunction
  endclass

  // Convenience typedef for string-keyed object pools
  typedef uvm_pool #(string, uvm_object) uvm_object_string_pool;

  //----------------------------------------------------------------------
  // uvm_queue - parameterized queue container
  //----------------------------------------------------------------------
  class uvm_queue #(type T = uvm_object) extends uvm_object;
    protected T queue[$];

    function new(string name = "uvm_queue");
      super.new(name);
    endfunction

    // Get size
    virtual function int size();
      return queue.size();
    endfunction

    // Insert at back
    virtual function void push_back(T item);
      queue.push_back(item);
    endfunction

    // Insert at front
    virtual function void push_front(T item);
      queue.push_front(item);
    endfunction

    // Remove from back
    virtual function T pop_back();
      if (queue.size() > 0)
        return queue.pop_back();
      return null;
    endfunction

    // Remove from front
    virtual function T pop_front();
      if (queue.size() > 0)
        return queue.pop_front();
      return null;
    endfunction

    // Get item at index
    virtual function T get(int index);
      if (index >= 0 && index < queue.size())
        return queue[index];
      return null;
    endfunction

    // Insert at index
    virtual function void insert(int index, T item);
      if (index >= 0 && index <= queue.size())
        queue.insert(index, item);
    endfunction

    // Delete at index
    virtual function void delete(int index = -1);
      if (index < 0)
        queue.delete();  // Delete all
      else if (index < queue.size())
        queue.delete(index);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_cmdline_processor - command line argument processing
  // Singleton class for accessing command line plusargs
  //----------------------------------------------------------------------
  class uvm_cmdline_processor extends uvm_object;
    static local uvm_cmdline_processor m_inst;

    // Get singleton instance
    static function uvm_cmdline_processor get_inst();
      if (m_inst == null)
        m_inst = new("cmdline");
      return m_inst;
    endfunction

    function new(string name = "uvm_cmdline_processor");
      super.new(name);
    endfunction

    // Get a single plusarg value
    // Returns 1 if found, 0 if not found
    virtual function bit get_arg_value(string match, ref string value);
      string arg;
      if ($value$plusargs({match, "=%s"}, arg)) begin
        value = arg;
        return 1;
      end
      return 0;
    endfunction

    // Get multiple plusarg values matching a pattern
    // Returns number of matches found
    virtual function int get_arg_values(string match, ref string values[$]);
      string arg;
      values.delete();
      if ($value$plusargs({match, "=%s"}, arg)) begin
        values.push_back(arg);
        return 1;
      end
      return 0;
    endfunction

    // Check if a plusarg exists (with or without value)
    virtual function bit get_arg_matches(string match);
      string dummy;
      return $test$plusargs(match) || $value$plusargs({match, "=%s"}, dummy);
    endfunction

    // Get UVM verbosity setting from +UVM_VERBOSITY
    virtual function uvm_verbosity get_verbosity();
      string verb_str;
      if (get_arg_value("UVM_VERBOSITY", verb_str)) begin
        case (verb_str)
          "UVM_NONE":   return UVM_NONE;
          "UVM_LOW":    return UVM_LOW;
          "UVM_MEDIUM": return UVM_MEDIUM;
          "UVM_HIGH":   return UVM_HIGH;
          "UVM_FULL":   return UVM_FULL;
          "UVM_DEBUG":  return UVM_DEBUG;
          default:      return UVM_MEDIUM;
        endcase
      end
      return UVM_MEDIUM;  // Default
    endfunction

    // Get test name from +UVM_TESTNAME
    virtual function bit get_test_name(ref string name);
      return get_arg_value("UVM_TESTNAME", name);
    endfunction

    // Get timeout from +UVM_TIMEOUT
    virtual function bit get_timeout(ref int timeout);
      string val;
      if (get_arg_value("UVM_TIMEOUT", val)) begin
        timeout = val.atoi();
        return 1;
      end
      return 0;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_callback - base class for callbacks
  // Allows extending component behavior without modifying source
  //----------------------------------------------------------------------
  virtual class uvm_callback extends uvm_object;
    bit callback_mode = 1;  // Enable/disable this callback

    function new(string name = "uvm_callback");
      super.new(name);
    endfunction

    // Enable this callback
    function void enable();
      callback_mode = 1;
    endfunction

    // Disable this callback
    function void set_enabled(bit en);
      callback_mode = en;
    endfunction

    // Check if enabled
    function bit is_enabled();
      return callback_mode;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_callbacks - registry for callbacks
  // Parametric class to manage callbacks for a specific component type
  //----------------------------------------------------------------------
  class uvm_callbacks #(type T = uvm_component, type CB = uvm_callback) extends uvm_object;
    static local CB m_callbacks[$];
    static local CB m_type_callbacks[string][$];

    function new(string name = "uvm_callbacks");
      super.new(name);
    endfunction

    // Add a callback to the global list
    static function void add(T obj, CB cb, bit append = 1);
      if (obj == null) begin
        // Global callback
        if (append)
          m_callbacks.push_back(cb);
        else
          m_callbacks.push_front(cb);
      end else begin
        // Per-instance callback
        string key = obj.get_full_name();
        if (append)
          m_type_callbacks[key].push_back(cb);
        else
          m_type_callbacks[key].push_front(cb);
      end
    endfunction

    // Delete a callback
    static function void delete(T obj, CB cb);
      if (obj == null) begin
        foreach (m_callbacks[i]) begin
          if (m_callbacks[i] == cb) begin
            m_callbacks.delete(i);
            return;
          end
        end
      end else begin
        string key = obj.get_full_name();
        if (m_type_callbacks.exists(key)) begin
          foreach (m_type_callbacks[key][i]) begin
            if (m_type_callbacks[key][i] == cb) begin
              m_type_callbacks[key].delete(i);
              return;
            end
          end
        end
      end
    endfunction

    // Get all callbacks for an object (global + instance-specific)
    static function void get(T obj, ref CB cbs[$]);
      cbs.delete();
      // Add global callbacks first
      foreach (m_callbacks[i]) begin
        if (m_callbacks[i].is_enabled())
          cbs.push_back(m_callbacks[i]);
      end
      // Add instance-specific callbacks
      if (obj != null) begin
        string key = obj.get_full_name();
        if (m_type_callbacks.exists(key)) begin
          foreach (m_type_callbacks[key][i]) begin
            if (m_type_callbacks[key][i].is_enabled())
              cbs.push_back(m_type_callbacks[key][i]);
          end
        end
      end
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_is_match - simple wildcard pattern matching
  //----------------------------------------------------------------------
  function automatic bit uvm_is_match(string pattern, string str);
    // Simple wildcard matching supporting '*' and '?'
    int pi = 0;  // pattern index
    int si = 0;  // string index
    int star_pi = -1;  // position of last '*' in pattern
    int star_si = -1;  // position in string when '*' was encountered

    while (si < str.len()) begin
      if (pi < pattern.len() && (pattern[pi] == str[si] || pattern[pi] == "?")) begin
        pi++;
        si++;
      end else if (pi < pattern.len() && pattern[pi] == "*") begin
        star_pi = pi;
        star_si = si;
        pi++;
      end else if (star_pi >= 0) begin
        pi = star_pi + 1;
        star_si++;
        si = star_si;
      end else begin
        return 0;
      end
    end

    // Check remaining pattern characters (should all be '*')
    while (pi < pattern.len() && pattern[pi] == "*")
      pi++;

    return pi == pattern.len();
  endfunction

  //----------------------------------------------------------------------
  // uvm_resource - generic resource with value
  //----------------------------------------------------------------------
  class uvm_resource #(type T = int) extends uvm_object;
    local T m_val;
    local bit m_is_set = 0;

    function new(string name = "uvm_resource");
      super.new(name);
    endfunction

    virtual function void set(T val);
      m_val = val;
      m_is_set = 1;
    endfunction

    virtual function T get();
      return m_val;
    endfunction

    virtual function T read();
      return m_val;
    endfunction

    virtual function void write(T val);
      m_val = val;
      m_is_set = 1;
    endfunction

    virtual function bit is_set();
      return m_is_set;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_resource_db - simplified resource database (alternative to config_db)
  //----------------------------------------------------------------------
  class uvm_resource_db #(type T = int);
    // Storage for resources by scope and name
    static local T m_resources[string][string];
    static local bit m_set[string][string];

    // Set a resource value
    static function void set(string scope, string name, T val, input uvm_object accessor = null);
      m_resources[scope][name] = val;
      m_set[scope][name] = 1;
    endfunction

    // Get a resource value - returns 1 if found
    static function bit get_by_name(string scope, string name, ref T val, input uvm_object accessor = null);
      // Try exact match first
      if (m_set.exists(scope) && m_set[scope].exists(name)) begin
        val = m_resources[scope][name];
        return 1;
      end
      // Try wildcard scopes
      foreach (m_set[s]) begin
        if (m_set[s].exists(name)) begin
          if (uvm_is_match(s, scope)) begin
            val = m_resources[s][name];
            return 1;
          end
        end
      end
      return 0;
    endfunction

    // Read value (alias for get_by_name that returns value directly)
    static function T read_by_name(string scope, string name, input uvm_object accessor = null);
      T val;
      void'(get_by_name(scope, name, val, accessor));
      return val;
    endfunction

    // Check if resource exists
    static function bit exists(string scope, string name);
      if (m_set.exists(scope) && m_set[scope].exists(name))
        return 1;
      foreach (m_set[s]) begin
        if (m_set[s].exists(name)) begin
          if (uvm_is_match(s, scope))
            return 1;
        end
      end
      return 0;
    endfunction

    // Clear all resources
    static function void clear();
      m_resources.delete();
      m_set.delete();
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

    // Utility methods - print component hierarchy starting from this component
    virtual function void print_topology(uvm_printer printer = null);
      __print_topology_recursive(this, 0);
    endfunction

    // Helper for recursive topology printing
    protected function void __print_topology_recursive(uvm_component comp, int depth);
      string indent;
      uvm_component children[$];
      for (int i = 0; i < depth; i++) indent = {indent, "  "};
      $display("%s%s (%s)", indent,
               comp.get_full_name() == "" ? "<unnamed>" : comp.get_full_name(),
               comp.get_type_name());
      comp.get_children(children);
      foreach (children[i])
        __print_topology_recursive(children[i], depth + 1);
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
    protected uvm_sequencer_base m_sequencer;
    protected uvm_sequence_base m_parent_sequence;
    static protected int m_next_transaction_id = 0;

    function new(string name = "uvm_sequence_item");
      super.new(name);
      m_transaction_id = m_next_transaction_id++;
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

    virtual function uvm_sequencer_base get_sequencer();
      return m_sequencer;
    endfunction

    virtual function void set_sequencer(uvm_sequencer_base sequencer);
      m_sequencer = sequencer;
    endfunction

    virtual function uvm_sequence_base get_parent_sequence();
      return m_parent_sequence;
    endfunction

    virtual function void set_item_context(uvm_sequence_base parent_seq, uvm_sequencer_base sequencer = null);
      m_parent_sequence = parent_seq;
      if (sequencer != null)
        m_sequencer = sequencer;
      else if (parent_seq != null)
        m_sequencer = parent_seq.get_sequencer();
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

    // Set p_sequencer by casting m_sequencer - overridden by uvm_declare_p_sequencer macro
    virtual function void m_set_p_sequencer();
      // Base implementation does nothing - derived classes override this
    endfunction

    virtual task start(uvm_sequencer_base sequencer, uvm_sequence_base parent_sequence = null,
                       int this_priority = -1, bit call_pre_post = 1);
      m_sequencer = sequencer;
      m_parent_sequence = parent_sequence;
      // Set p_sequencer by casting m_sequencer (if uvm_declare_p_sequencer was used)
      m_set_p_sequencer();
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
      uvm_sequencer_base sqr;
      // Get the sequencer - use passed one or default to sequence's sequencer
      sqr = (sequencer != null) ? sequencer : m_sequencer;
      if (sqr == null) begin
        $display("UVM_ERROR [SEQR] Null sequencer in start_item");
        return;
      end
      // Set item context
      item.set_item_context(this, sqr);
      // Wait for grant from sequencer (arbitration)
      sqr.wait_for_grant(this, set_priority, 0);
    endtask

    virtual task finish_item(uvm_sequence_item item, int set_priority = -1);
      uvm_sequencer_base sqr;
      sqr = item.get_sequencer();
      if (sqr == null) sqr = m_sequencer;
      if (sqr == null) begin
        $display("UVM_ERROR [SEQR] Null sequencer in finish_item");
        return;
      end
      // Send the item to the sequencer
      sqr.send_request(this, item, 0);
      // Wait for driver to call item_done
      sqr.wait_for_item_done(this, item.get_transaction_id());
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
  // uvm_sequence_library - collection of sequences to run
  //----------------------------------------------------------------------
  typedef enum int {
    UVM_SEQ_LIB_RAND,     // Random selection
    UVM_SEQ_LIB_RANDC,    // Random cyclic selection
    UVM_SEQ_LIB_ITEM,     // Single item per sequence
    UVM_SEQ_LIB_USER      // User-defined selection
  } uvm_sequence_lib_mode;

  class uvm_sequence_library #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_sequence #(REQ, RSP);
    protected uvm_sequence_base m_sequences[$];
    protected int unsigned min_random_count = 10;
    protected int unsigned max_random_count = 10;
    protected uvm_sequence_lib_mode selection_mode = UVM_SEQ_LIB_RAND;

    function new(string name = "uvm_sequence_library");
      super.new(name);
    endfunction

    // Add a sequence to the library
    virtual function void add_sequence(uvm_sequence_base seq);
      m_sequences.push_back(seq);
    endfunction

    // Get number of sequences in library
    virtual function int unsigned get_num_sequences();
      return m_sequences.size();
    endfunction

    // Set min/max random count
    virtual function void set_random_count(int unsigned min_val, int unsigned max_val);
      min_random_count = min_val;
      max_random_count = max_val;
    endfunction

    // Set selection mode
    virtual function void set_selection_mode(uvm_sequence_lib_mode mode);
      selection_mode = mode;
    endfunction

    // Body - execute sequences from library
    virtual task body();
      int unsigned count;
      int idx;

      if (m_sequences.size() == 0) begin
        $display("[UVM_WARNING] Sequence library is empty");
        return;
      end

      // Randomize count between min and max
      count = min_random_count + ($urandom() % (max_random_count - min_random_count + 1));

      for (int i = 0; i < count; i++) begin
        case (selection_mode)
          UVM_SEQ_LIB_RAND: idx = $urandom() % m_sequences.size();
          UVM_SEQ_LIB_RANDC: idx = i % m_sequences.size();  // Simplified cyclic
          UVM_SEQ_LIB_ITEM: idx = 0;  // Just use first
          UVM_SEQ_LIB_USER: idx = select_sequence(i);
          default: idx = 0;
        endcase

        if (m_sequences[idx] != null) begin
          m_sequences[idx].start(m_sequencer, this);
        end
      end
    endtask

    // Override for custom selection
    virtual function int select_sequence(int idx);
      return idx % m_sequences.size();
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_sequencer_base - base sequencer
  //----------------------------------------------------------------------
  class uvm_sequencer_base extends uvm_component;
    // Completion tracking - maps transaction_id to done status
    protected bit m_item_done[int];
    protected int m_current_transaction_id = -1;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void set_arbitration(uvm_sequencer_arb_mode val);
      // Stub - simplified arbitration
    endfunction

    virtual task wait_for_grant(uvm_sequence_base sequence_ptr, int item_priority = -1, bit lock_request = 0);
      // Simplified - grant immediately (no arbitration)
    endtask

    virtual function void send_request(uvm_sequence_base sequence_ptr = null, uvm_sequence_item t = null, bit rerandomize = 0);
      // Mark item as not done
      if (t != null)
        m_item_done[t.get_transaction_id()] = 0;
    endfunction

    virtual task wait_for_item_done(uvm_sequence_base sequence_ptr = null, int transaction_id = -1);
      // Wait until the item is marked done
      wait (m_item_done.exists(transaction_id) && m_item_done[transaction_id] == 1);
      // Clean up
      m_item_done.delete(transaction_id);
    endtask

    // Signal item completion (called by driver via seq_item_pull_port)
    virtual function void item_done_base(int transaction_id);
      m_item_done[transaction_id] = 1;
    endfunction
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
    protected REQ m_last_req;  // Track current item for item_done

    // seq_item_export for driver connection (alias to this sequencer)
    uvm_sequencer #(REQ, RSP) seq_item_export;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      seq_item_export = this;
    endfunction

    // Override base class send_request - queue the item
    virtual function void send_request(uvm_sequence_base sequence_ptr = null, uvm_sequence_item t = null, bit rerandomize = 0);
      REQ req;
      if (t == null) return;
      super.send_request(sequence_ptr, t, rerandomize);
      // verilator lint_off CASTCONST
      if ($cast(req, t)) begin
        m_req_fifo.push_back(req);
      end
      // verilator lint_on CASTCONST
    endfunction

    // Get number of pending requests
    virtual function int num_pending_reqs();
      return m_req_fifo.size();
    endfunction

    virtual task get_next_item(output REQ t);
      while (m_req_fifo.size() == 0) begin
        #1;  // Yield to allow sequences to run
      end
      t = m_req_fifo.pop_front();
      m_last_req = t;  // Track for item_done
    endtask

    virtual task try_next_item(output REQ t);
      if (m_req_fifo.size() > 0) begin
        t = m_req_fifo.pop_front();
        m_last_req = t;
      end else
        t = null;
    endtask

    virtual function void item_done(RSP item = null);
      // Signal completion of the last retrieved item
      if (m_last_req != null) begin
        item_done_base(m_last_req.get_transaction_id());
        m_last_req = null;
      end
      // Optionally store response
      if (item != null)
        m_rsp_fifo.push_back(item);
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

    // Get response (for sequences that need responses)
    virtual task get_response(output RSP t);
      wait (m_rsp_fifo.size() > 0);
      t = m_rsp_fifo.pop_front();
    endtask
  endclass

  //----------------------------------------------------------------------
  // Analysis port base class for type-independent storage
  // (moved before uvm_driver which uses these)
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
  // Analysis port - can connect to imps or other ports (hierarchical connections)
  class uvm_analysis_port #(type T = uvm_object) extends uvm_analysis_imp_base;
    protected uvm_component m_parent;
    protected uvm_analysis_imp_base m_subscribers[$];

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
    endfunction

    // Connect to any analysis imp or port (type-erased)
    virtual function void connect(uvm_analysis_imp_base imp);
      m_subscribers.push_back(imp);
    endfunction

    virtual function void write(T t);
      foreach (m_subscribers[i])
        m_subscribers[i].write_object(t);
    endfunction

    // Implementation for when this port is a subscriber (hierarchical connection)
    virtual function void write_object(uvm_object t);
      T item;
      if ($cast(item, t))
        write(item);
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

  // Analysis export - can be connected to from ports (hierarchical connections)
  class uvm_analysis_export #(type T = uvm_object) extends uvm_analysis_imp_base;
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

    // Implementation for when this export is a subscriber
    virtual function void write_object(uvm_object t);
      T item;
      if ($cast(item, t))
        write(item);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // TLM blocking ports and imps
  //----------------------------------------------------------------------

  // Base class for blocking put imp (type-erased)
  virtual class uvm_blocking_put_imp_base extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
    pure virtual task put_object(uvm_object t);
  endclass

  // Blocking put port
  class uvm_blocking_put_port #(type T = uvm_object) extends uvm_object;
    protected uvm_component m_parent;
    protected uvm_blocking_put_imp_base m_imp;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
    endfunction

    virtual function void connect(uvm_blocking_put_imp_base imp);
      m_imp = imp;
    endfunction

    virtual task put(T t);
      if (m_imp != null)
        m_imp.put_object(t);
    endtask
  endclass

  // Blocking put imp
  class uvm_blocking_put_imp #(type T = uvm_object, type IMP = uvm_component) extends uvm_blocking_put_imp_base;
    protected IMP m_imp;

    function new(string name = "", IMP imp = null);
      super.new(name);
      m_imp = imp;
    endfunction

    virtual task put_object(uvm_object t);
      T item;
      if ($cast(item, t) && m_imp != null)
        m_imp.put(item);
    endtask
  endclass

  // Base class for blocking get imp (type-erased)
  virtual class uvm_blocking_get_imp_base extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
    pure virtual task get_object(output uvm_object t);
  endclass

  // Blocking get port
  class uvm_blocking_get_port #(type T = uvm_object) extends uvm_object;
    protected uvm_component m_parent;
    protected uvm_blocking_get_imp_base m_imp;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
    endfunction

    virtual function void connect(uvm_blocking_get_imp_base imp);
      m_imp = imp;
    endfunction

    virtual task get(output T t);
      uvm_object obj;
      if (m_imp != null) begin
        m_imp.get_object(obj);
        if (!$cast(t, obj))
          t = null;
      end
    endtask
  endclass

  // Blocking get imp
  class uvm_blocking_get_imp #(type T = uvm_object, type IMP = uvm_component) extends uvm_blocking_get_imp_base;
    protected IMP m_imp;

    function new(string name = "", IMP imp = null);
      super.new(name);
      m_imp = imp;
    endfunction

    virtual task get_object(output uvm_object t);
      T item;
      if (m_imp != null) begin
        m_imp.get(item);
        t = item;
      end
    endtask
  endclass

  // Blocking put/get port (combined)
  class uvm_blocking_put_get_port #(type T = uvm_object) extends uvm_object;
    uvm_blocking_put_port #(T) put_port;
    uvm_blocking_get_port #(T) get_port;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      put_port = new({name, ".put"}, parent);
      get_port = new({name, ".get"}, parent);
    endfunction

    virtual task put(T t);
      put_port.put(t);
    endtask

    virtual task get(output T t);
      get_port.get(t);
    endtask
  endclass

  //----------------------------------------------------------------------
  // Nonblocking TLM ports and imps
  //----------------------------------------------------------------------

  // Base class for nonblocking put imp (type-erased)
  virtual class uvm_nonblocking_put_imp_base extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
    pure virtual function bit try_put_object(uvm_object t);
    pure virtual function bit can_put();
  endclass

  // Nonblocking put port
  class uvm_nonblocking_put_port #(type T = uvm_object) extends uvm_object;
    protected uvm_component m_parent;
    protected uvm_nonblocking_put_imp_base m_imp;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
    endfunction

    virtual function void connect(uvm_nonblocking_put_imp_base imp);
      m_imp = imp;
    endfunction

    virtual function bit try_put(T t);
      if (m_imp != null)
        return m_imp.try_put_object(t);
      return 0;
    endfunction

    virtual function bit can_put();
      if (m_imp != null)
        return m_imp.can_put();
      return 0;
    endfunction
  endclass

  // Nonblocking put imp
  class uvm_nonblocking_put_imp #(type T = uvm_object, type IMP = uvm_component) extends uvm_nonblocking_put_imp_base;
    protected IMP m_imp;

    function new(string name = "", IMP imp = null);
      super.new(name);
      m_imp = imp;
    endfunction

    virtual function bit try_put_object(uvm_object t);
      T item;
      if ($cast(item, t) && m_imp != null)
        return m_imp.try_put(item);
      return 0;
    endfunction

    virtual function bit can_put();
      if (m_imp != null)
        return m_imp.can_put();
      return 0;
    endfunction
  endclass

  // Base class for nonblocking get imp (type-erased)
  virtual class uvm_nonblocking_get_imp_base extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
    pure virtual function bit try_get_object(output uvm_object t);
    pure virtual function bit can_get();
  endclass

  // Nonblocking get port
  class uvm_nonblocking_get_port #(type T = uvm_object) extends uvm_object;
    protected uvm_component m_parent;
    protected uvm_nonblocking_get_imp_base m_imp;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
    endfunction

    virtual function void connect(uvm_nonblocking_get_imp_base imp);
      m_imp = imp;
    endfunction

    virtual function bit try_get(output T t);
      uvm_object obj;
      if (m_imp != null && m_imp.try_get_object(obj)) begin
        if ($cast(t, obj))
          return 1;
      end
      return 0;
    endfunction

    virtual function bit can_get();
      if (m_imp != null)
        return m_imp.can_get();
      return 0;
    endfunction
  endclass

  // Nonblocking get imp
  class uvm_nonblocking_get_imp #(type T = uvm_object, type IMP = uvm_component) extends uvm_nonblocking_get_imp_base;
    protected IMP m_imp;

    function new(string name = "", IMP imp = null);
      super.new(name);
      m_imp = imp;
    endfunction

    virtual function bit try_get_object(output uvm_object t);
      T item;
      if (m_imp != null && m_imp.try_get(item)) begin
        t = item;
        return 1;
      end
      return 0;
    endfunction

    virtual function bit can_get();
      if (m_imp != null)
        return m_imp.can_get();
      return 0;
    endfunction
  endclass

  // Combined put port (blocking + nonblocking)
  class uvm_put_port #(type T = uvm_object) extends uvm_object;
    uvm_blocking_put_port #(T) blocking;
    uvm_nonblocking_put_port #(T) nonblocking;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      blocking = new({name, ".blocking"}, parent);
      nonblocking = new({name, ".nonblocking"}, parent);
    endfunction

    virtual task put(T t);
      blocking.put(t);
    endtask

    virtual function bit try_put(T t);
      return nonblocking.try_put(t);
    endfunction

    virtual function bit can_put();
      return nonblocking.can_put();
    endfunction
  endclass

  // Combined get port (blocking + nonblocking)
  class uvm_get_port #(type T = uvm_object) extends uvm_object;
    uvm_blocking_get_port #(T) blocking;
    uvm_nonblocking_get_port #(T) nonblocking;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      blocking = new({name, ".blocking"}, parent);
      nonblocking = new({name, ".nonblocking"}, parent);
    endfunction

    virtual task get(output T t);
      blocking.get(t);
    endtask

    virtual function bit try_get(output T t);
      return nonblocking.try_get(t);
    endfunction

    virtual function bit can_get();
      return nonblocking.can_get();
    endfunction
  endclass

  //----------------------------------------------------------------------
  // TLM ports (moved before uvm_driver which uses these)
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
  // uvm_driver - driver base class
  //----------------------------------------------------------------------
  class uvm_driver #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_component;
    uvm_seq_item_pull_port #(REQ, RSP) seq_item_port;
    uvm_analysis_port #(RSP) rsp_port;

    // Request and response objects - convenience variables for derived classes
    REQ req;
    RSP rsp;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
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
  // uvm_tlm_req_rsp_channel - Bidirectional TLM channel
  // Provides FIFOs for request and response transactions
  //----------------------------------------------------------------------
  class uvm_tlm_req_rsp_channel #(type REQ = uvm_object, type RSP = REQ) extends uvm_component;
    uvm_tlm_fifo #(REQ) m_req_fifo;
    uvm_tlm_fifo #(RSP) m_rsp_fifo;

    function new(string name = "", uvm_component parent = null, int req_size = 1, int rsp_size = 1);
      super.new(name, parent);
      m_req_fifo = new("req_fifo", this, req_size);
      m_rsp_fifo = new("rsp_fifo", this, rsp_size);
    endfunction

    // Request interface
    virtual task put_request(REQ req);
      m_req_fifo.put(req);
    endtask

    virtual function bit try_put_request(REQ req);
      return m_req_fifo.try_put(req);
    endfunction

    virtual task get_request(output REQ req);
      m_req_fifo.get(req);
    endtask

    virtual function bit try_get_request(output REQ req);
      return m_req_fifo.try_get(req);
    endfunction

    virtual task peek_request(output REQ req);
      m_req_fifo.peek(req);
    endtask

    virtual function bit try_peek_request(output REQ req);
      return m_req_fifo.try_peek(req);
    endfunction

    // Response interface
    virtual task put_response(RSP rsp);
      m_rsp_fifo.put(rsp);
    endtask

    virtual function bit try_put_response(RSP rsp);
      return m_rsp_fifo.try_put(rsp);
    endfunction

    virtual task get_response(output RSP rsp);
      m_rsp_fifo.get(rsp);
    endtask

    virtual function bit try_get_response(output RSP rsp);
      return m_rsp_fifo.try_get(rsp);
    endfunction

    virtual task peek_response(output RSP rsp);
      m_rsp_fifo.peek(rsp);
    endtask

    virtual function bit try_peek_response(output RSP rsp);
      return m_rsp_fifo.try_peek(rsp);
    endfunction

    // Status
    virtual function bit request_is_empty();
      return m_req_fifo.is_empty();
    endfunction

    virtual function bit response_is_empty();
      return m_rsp_fifo.is_empty();
    endfunction

    virtual function int request_used();
      return m_req_fifo.used();
    endfunction

    virtual function int response_used();
      return m_rsp_fifo.used();
    endfunction

    virtual function void flush();
      m_req_fifo.flush();
      m_rsp_fifo.flush();
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_in_order_comparator - Compares two streams of transactions
  // Receives expected on before_export and actual on after_export
  //----------------------------------------------------------------------
  class uvm_in_order_comparator #(type T = uvm_object) extends uvm_component;
    uvm_tlm_analysis_fifo #(T) m_before_fifo;
    uvm_tlm_analysis_fifo #(T) m_after_fifo;
    uvm_analysis_imp #(T, uvm_in_order_comparator #(T)) before_export;
    uvm_analysis_imp #(T, uvm_in_order_comparator #(T)) after_export;
    protected int m_matches;
    protected int m_mismatches;
    protected bit m_before_called;
    protected T m_last_before;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      m_before_fifo = new("before_fifo", this);
      m_after_fifo = new("after_fifo", this);
      before_export = new("before_export", this);
      after_export = new("after_export", this);
      m_matches = 0;
      m_mismatches = 0;
      m_before_called = 0;
    endfunction

    virtual function void write(T t);
      // This is called for both before and after
      // We use a flag to track which one was called
      if (m_before_called) begin
        // This is an after transaction
        m_after_fifo.write(t);
        m_before_called = 0;
        do_compare();
      end else begin
        // This is a before transaction
        m_before_fifo.write(t);
        m_before_called = 1;
      end
    endfunction

    virtual function void write_before(T t);
      m_before_fifo.write(t);
      do_compare();
    endfunction

    virtual function void write_after(T t);
      m_after_fifo.write(t);
      do_compare();
    endfunction

    virtual function void do_compare();
      T before_item, after_item;
      while (!m_before_fifo.is_empty() && !m_after_fifo.is_empty()) begin
        if (m_before_fifo.try_get(before_item) && m_after_fifo.try_get(after_item)) begin
          if (compare(before_item, after_item)) begin
            m_matches++;
          end else begin
            m_mismatches++;
            $display("[UVM_ERROR] %s: Mismatch detected", get_full_name());
          end
        end
      end
    endfunction

    virtual function bit compare(T before_item, T after_item);
      // Default: use object compare method
      return before_item.compare(after_item);
    endfunction

    virtual function int get_matches();
      return m_matches;
    endfunction

    virtual function int get_mismatches();
      return m_mismatches;
    endfunction

    virtual function void flush();
      m_before_fifo.flush();
      m_after_fifo.flush();
    endfunction

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $display("[UVM_INFO] %s: Comparator report - Matches: %0d, Mismatches: %0d",
               get_full_name(), m_matches, m_mismatches);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_algorithmic_comparator - Comparator with transform function
  // Applies a transformation to the before item before comparing
  //----------------------------------------------------------------------
  class uvm_algorithmic_comparator #(type BEFORE = uvm_object, type AFTER = BEFORE,
                                      type TRANSFORMER = uvm_object) extends uvm_component;
    uvm_tlm_analysis_fifo #(BEFORE) m_before_fifo;
    uvm_tlm_analysis_fifo #(AFTER) m_after_fifo;
    protected TRANSFORMER m_transformer;
    protected int m_matches;
    protected int m_mismatches;

    function new(string name = "", uvm_component parent = null, TRANSFORMER transformer = null);
      super.new(name, parent);
      m_before_fifo = new("before_fifo", this);
      m_after_fifo = new("after_fifo", this);
      m_transformer = transformer;
      m_matches = 0;
      m_mismatches = 0;
    endfunction

    virtual function void write_before(BEFORE t);
      m_before_fifo.write(t);
      do_compare();
    endfunction

    virtual function void write_after(AFTER t);
      m_after_fifo.write(t);
      do_compare();
    endfunction

    protected function void do_compare();
      BEFORE before_item;
      AFTER after_item, transformed;
      while (!m_before_fifo.is_empty() && !m_after_fifo.is_empty()) begin
        if (m_before_fifo.try_get(before_item) && m_after_fifo.try_get(after_item)) begin
          transformed = transform(before_item);
          if (compare(transformed, after_item)) begin
            m_matches++;
          end else begin
            m_mismatches++;
            $display("[UVM_ERROR] %s: Mismatch detected after transform", get_full_name());
          end
        end
      end
    endfunction

    virtual function AFTER transform(BEFORE b);
      AFTER a;
      // Default: try to cast
      if ($cast(a, b))
        return a;
      return null;
    endfunction

    virtual function bit compare(AFTER a, AFTER b);
      if (a == null || b == null) return 0;
      return a.compare(b);
    endfunction

    virtual function int get_matches();
      return m_matches;
    endfunction

    virtual function int get_mismatches();
      return m_mismatches;
    endfunction
  endclass

  //----------------------------------------------------------------------
  // uvm_config_db - configuration database
  // Functional implementation using associative arrays for storage
  // Follows standard UVM semantics for hierarchical configuration
  //----------------------------------------------------------------------
  class uvm_config_db #(type T = int);
    // Storage: maps "target_pattern:field_name" to value
    // target_pattern is the hierarchical path pattern where this value applies
    static T m_config_db[string];
    // List of all keys for pattern matching
    static string m_all_keys[$];

    // Build the target path pattern from set() arguments
    // set(cntxt, "*", field) -> pattern = "cntxt_path.*" (all descendants)
    // set(cntxt, "env*", field) -> pattern = "cntxt_path.env*"
    // set(cntxt, "", field) -> pattern = "cntxt_path" (exact)
    // set(null, "*", field) -> pattern = "*" (global)
    static function string build_target_pattern(uvm_component cntxt, string inst_name);
      string cntxt_path;
      if (cntxt != null)
        cntxt_path = cntxt.get_full_name();
      else
        cntxt_path = "";

      if (inst_name == "*") begin
        // Wildcard for all descendants
        if (cntxt_path == "")
          return "*";
        else
          return {cntxt_path, ".*"};
      end else if (inst_name == "") begin
        // Exact match for context itself
        return cntxt_path;
      end else begin
        // Specific inst_name under context
        if (cntxt_path == "")
          return inst_name;
        else
          return {cntxt_path, ".", inst_name};
      end
    endfunction

    // Build the requester path from get() arguments
    // get(cntxt, "", field) -> path = "cntxt_path"
    // get(cntxt, "foo", field) -> path = "cntxt_path.foo"
    static function string build_requester_path(uvm_component cntxt, string inst_name);
      string cntxt_path;
      if (cntxt != null)
        cntxt_path = cntxt.get_full_name();
      else
        cntxt_path = "";

      if (inst_name == "")
        return cntxt_path;
      else if (cntxt_path == "")
        return inst_name;
      else
        return {cntxt_path, ".", inst_name};
    endfunction

    // Check if a segment pattern matches a segment
    // "*" matches anything
    // "foo*" matches "foo", "foobar"
    // "*foo" matches "foo", "barfoo"
    // "*foo*" matches anything containing "foo"
    // "foo" matches only "foo"
    static function bit segment_matches(string pattern, string segment);
      int plen, slen;
      bit starts_with_star, ends_with_star;

      if (pattern == "*") return 1;
      if (pattern == segment) return 1;

      plen = pattern.len();
      slen = segment.len();
      if (plen == 0) return (slen == 0);

      starts_with_star = (pattern[0] == "*");
      ends_with_star = (pattern[plen-1] == "*");

      // *foo* pattern - contains match
      if (starts_with_star && ends_with_star && plen > 2) begin
        string middle = pattern.substr(1, plen-2);
        int mlen = middle.len();
        for (int i = 0; i <= slen - mlen; i++) begin
          if (segment.substr(i, i + mlen - 1) == middle)
            return 1;
        end
        return 0;
      end

      // *foo pattern - ends with match
      if (starts_with_star && !ends_with_star) begin
        string suffix = pattern.substr(1, plen-1);
        int sufflen = suffix.len();
        if (slen >= sufflen && segment.substr(slen - sufflen, slen - 1) == suffix)
          return 1;
        return 0;
      end

      // foo* pattern - starts with match
      if (ends_with_star && !starts_with_star) begin
        string prefix = pattern.substr(0, plen-2);
        int preflen = prefix.len();
        if (slen >= preflen && segment.substr(0, preflen - 1) == prefix)
          return 1;
        return 0;
      end

      return 0;
    endfunction

    // Check if a pattern matches a path
    // Patterns can contain wildcards in individual path segments
    // "foo.bar" matches only "foo.bar"
    // "foo.*" matches "foo.bar", "foo.baz", etc.
    // "foo.*env*" matches "foo.myenv", "foo.axi4_env_h", etc.
    static function bit pattern_matches_path(string pattern, string path);
      int plen, pathlen;

      // Empty pattern matches empty path only
      if (pattern == "") return (path == "");

      // Global wildcard matches everything
      if (pattern == "*") return 1;

      plen = pattern.len();
      pathlen = path.len();

      // Check for ".*" suffix (descendant wildcard - matches any depth)
      if (plen >= 2 && pattern.substr(plen-2, plen-1) == ".*") begin
        string prefix = pattern.substr(0, plen-3);
        int prefix_len = prefix.len();
        // Matches the prefix itself
        if (path == prefix) return 1;
        // Or any descendant (path starts with prefix.)
        if (pathlen > prefix_len) begin
          if (path.substr(0, prefix_len-1) == prefix && path[prefix_len] == ".")
            return 1;
        end
        return 0;
      end

      // Split pattern and path by dots and match segment by segment
      begin
        string pat_segments[$];
        string path_segments[$];
        int pi, si;
        string cur_seg;

        // Split pattern into segments
        cur_seg = "";
        for (int i = 0; i < plen; i++) begin
          if (pattern[i] == ".") begin
            pat_segments.push_back(cur_seg);
            cur_seg = "";
          end else begin
            cur_seg = {cur_seg, pattern[i]};
          end
        end
        pat_segments.push_back(cur_seg);

        // Split path into segments
        cur_seg = "";
        for (int i = 0; i < pathlen; i++) begin
          if (path[i] == ".") begin
            path_segments.push_back(cur_seg);
            cur_seg = "";
          end else begin
            cur_seg = {cur_seg, path[i]};
          end
        end
        path_segments.push_back(cur_seg);

        // Must have same number of segments for match
        if (pat_segments.size() != path_segments.size())
          return 0;

        // Match each segment
        for (int i = 0; i < pat_segments.size(); i++) begin
          if (!segment_matches(pat_segments[i], path_segments[i]))
            return 0;
        end
        return 1;
      end
    endfunction

    static function void set(uvm_component cntxt, string inst_name, string field_name, T value);
      string pattern = build_target_pattern(cntxt, inst_name);
      string key = {pattern, ":", field_name};
      // Add to keys list if not already there (check before setting)
      if (!m_config_db.exists(key)) begin
        m_all_keys.push_back(key);
      end
      m_config_db[key] = value;
    endfunction

    static function bit get(uvm_component cntxt, string inst_name, string field_name, inout T value);
      string req_path = build_requester_path(cntxt, inst_name);
      string exact_key = {req_path, ":", field_name};

      // First try exact match
      if (m_config_db.exists(exact_key)) begin
        value = m_config_db[exact_key];
        return 1;
      end

      // Try pattern matches - scan all keys looking for matching patterns
      foreach (m_all_keys[i]) begin
        string key = m_all_keys[i];
        // Key format is "pattern:field_name"
        // Find the last colon to split pattern and field
        int last_colon = -1;
        foreach (key[j]) begin
          if (key[j] == ":") last_colon = j;
        end
        if (last_colon > 0) begin
          string key_pattern = key.substr(0, last_colon-1);
          string key_field = key.substr(last_colon+1, key.len()-1);
          if (key_field == field_name) begin
            if (pattern_matches_path(key_pattern, req_path)) begin
              value = m_config_db[key];
              return 1;
            end
          end
        end
      end

      // Not found
      return 0;
    endfunction

    static function bit exists(uvm_component cntxt, string inst_name, string field_name);
      T dummy;
      return get(cntxt, inst_name, field_name, dummy);
    endfunction

    static function void wait_modified(uvm_component cntxt, string inst_name, string field_name);
      // Stub - immediate return (no event-based waiting in simple implementation)
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
    string cmdline_test;

    // Ensure globals are initialized
    __uvm_pkg_init();

    // Check for +UVM_TESTNAME on command line - this overrides the passed test_name
    if ($value$plusargs("UVM_TESTNAME=%s", cmdline_test)) begin
      test_name = cmdline_test;
    end

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

      // With wait fork, all run_phase tasks have completed
      $display("[UVM_INFO] @ %0t: run_test: All run_phase tasks completed [UVM]", $time);

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
    // Build phase must run top-down, but children are created during build_phase
    // So we need to process level-by-level
    uvm_component queue[$];
    uvm_component children[$];
    uvm_component comp;
    int loop_count;

    // Start with root
    queue.push_back(root);

    while (queue.size() > 0) begin
      loop_count++;
      if (loop_count > 1000) begin
        $display("[UVM_ERROR] __run_build_phase: Loop count exceeded 1000, breaking");
        break;
      end
      comp = queue.pop_front();
      // Run build_phase on this component
      $display("[UVM_DEBUG] __run_build_phase: Calling build_phase on %s", comp.get_full_name());
      comp.build_phase(phase);
      $display("[UVM_DEBUG] __run_build_phase: build_phase returned, getting children");
      // After build_phase, collect any newly created children
      comp.get_children(children);
      $display("[UVM_DEBUG] __run_build_phase: Found %0d children", children.size());
      foreach (children[i]) begin
        $display("[UVM_DEBUG] __run_build_phase: Adding child %s to queue", children[i].get_full_name());
        queue.push_back(children[i]);
      end
      children.delete();
    end
    $display("[UVM_DEBUG] __run_build_phase: Complete, processed %0d components", loop_count);
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
    int poll_count;
    __collect_components(root, comps);
    // Run phase launches all run_phase tasks in parallel
    // Fork all run_phase tasks first
    fork begin
      foreach (comps[i]) begin
        automatic int idx = i;
        fork
          comps[idx].run_phase(phase);
        join_none
      end
      // Now wait for objections or completion
      // Give components a chance to raise objections
      #1;
      // If no objections raised, wait a bit longer
      if (phase.get_objection_count() == 0) begin
        #99;  // Total of 100 time units grace period
      end
      // Poll for objections to be dropped (or timeout)
      poll_count = 0;
      while (phase.get_objection_count() > 0 && poll_count < 100000) begin
        #10;
        poll_count++;
      end
      // Objections dropped (or timeout) - phase is done
      if (poll_count >= 100000) begin
        $display("[UVM_WARNING] @ %0t: run_phase objection timeout [UVM]", $time);
      end
    end join
    // Kill any remaining run_phase tasks (like driver forever loops)
    disable fork;
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
