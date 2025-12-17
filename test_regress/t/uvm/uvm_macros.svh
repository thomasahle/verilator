// DESCRIPTION: Verilator: Concatenated UVM header for internal testing
// SPDX-License-Identifier: Apache-2.0
//----------------------------------------------------------------------
// To recreate:
//   Using verilator_ext_tests:
//     t_uvm_hello_v2020_3_1_dpi --gold
//
//----------------------------------------------------------------------
// Copyright 2007-2022 Cadence Design Systems, Inc.
// Copyright 2023 Intel Corporation
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2013-2024 NVIDIA Corporation
// Copyright 2011-2022 Synopsys, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------
`define UVM_PKG_SV
`define UVM_MACROS_SVH
`define UVM_STRING_QUEUE_STREAMING_PACK(q) uvm_pkg::m_uvm_string_queue_join(q)
`define uvm_typename(X) $typename(X)
`define uvm_delay(TIME) #(TIME);
`define UVM_VERSION_DEFINES_SVH
`define UVM_VERSION 2020
`define UVM_VERSION_POST_2017
`define UVM_VERSION_POST_2017_1_0
`define UVM_VERSION_POST_2017_1_1
`define UVM_VERSION_POST_2020_1_0
`define UVM_VERSION_POST_2020_1_1
`define UVM_VERSION_POST_2020_2_0
`define UVM_NAME UVM
`define UVM_MAJOR_REV 2020
`define UVM_MINOR_REV 3.0
`define UVM_VERSION_STRING uvm_pkg::UVM_VERSION_STRING
`define UVM_POST_VERSION_1_1
`define UVM_POST_VERSION_1_2
`define UVM_GLOBAL_DEFINES_SVH
`define UVM_COMPONENT_CONFIG_MODE_DEFAULT CONFIG_CHECK_NAMES
`define UVM_MAX_STREAMBITS 4096
`define UVM_PACKER_MAX_BYTES `UVM_MAX_STREAMBITS
`define UVM_DEFAULT_TIMEOUT 9200s
`define UVM_MESSAGE_DEFINES_SVH
`define UVM_LINE_WIDTH 120
`define UVM_NUM_LINES 120
`define uvm_file `__FILE__
`define uvm_line `__LINE__
`define uvm_report_begin(SEVERITY, ID, VERBOSITY, RO=uvm_get_report_object()) \
   begin \
     uvm_pkg::uvm_report_object _local_report_object_;\
     _local_report_object_ = RO.uvm_get_report_object() ; \
     if ((_local_report_object_.get_report_verbosity_level(SEVERITY, ID) >= VERBOSITY) && \
         (_local_report_object_.get_report_action(SEVERITY, ID) != uvm_pkg::UVM_NO_ACTION)) begin
`define uvm_report_end \
     end \
   end
`define uvm_info(ID, MSG, VERBOSITY) \
  `uvm_report_begin(uvm_pkg::UVM_INFO, ID, VERBOSITY) \
  uvm_report_info(ID, MSG, VERBOSITY, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_warning(ID, MSG) \
  `uvm_report_begin(uvm_pkg::UVM_WARNING, ID, uvm_pkg::UVM_NONE) \
  uvm_report_warning(ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_error(ID, MSG) \
  `uvm_report_begin(uvm_pkg::UVM_ERROR, ID, uvm_pkg::UVM_NONE) \
  uvm_report_error(ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_fatal(ID, MSG) \
  `uvm_report_begin(uvm_pkg::UVM_FATAL, ID, uvm_pkg::UVM_NONE) \
  uvm_report_fatal(ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_info_context(ID, MSG, VERBOSITY, RO) \
  `uvm_report_begin(uvm_pkg::UVM_INFO, ID, VERBOSITY, RO) \
   _local_report_object_.uvm_report_info(ID, MSG, VERBOSITY, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_warning_context(ID, MSG, RO) \
  `uvm_report_begin(uvm_pkg::UVM_WARNING, ID, uvm_pkg::UVM_NONE, RO) \
   _local_report_object_.uvm_report_warning(ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_error_context(ID, MSG, RO) \
  `uvm_report_begin(uvm_pkg::UVM_ERROR, ID, uvm_pkg::UVM_NONE, RO) \
   _local_report_object_.uvm_report_error(ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_fatal_context(ID, MSG, RO) \
  `uvm_report_begin(uvm_pkg::UVM_FATAL, ID, uvm_pkg::UVM_NONE, RO) \
   _local_report_object_.uvm_report_fatal(ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
  `uvm_report_end
`define uvm_message_begin(SEVERITY, ID, MSG, VERBOSITY, FILE, LINE, RM) \
   `uvm_report_begin(SEVERITY, ID, VERBOSITY) \
     uvm_pkg::uvm_report_message __uvm_msg; \
     if (RM == null) RM = uvm_pkg::uvm_report_message::new_report_message(); \
     __uvm_msg = RM; \
     __uvm_msg.set_report_message(SEVERITY, ID, MSG, VERBOSITY, FILE, LINE, "");
`define uvm_message_end \
    uvm_process_report_message(__uvm_msg); \
  `uvm_report_end
`define uvm_message_context_begin(SEVERITY, ID, MSG, VERBOSITY, FILE, LINE, RO, RM) \
   `uvm_report_begin(SEVERITY, ID, VERBOSITY, RO) \
     uvm_pkg::uvm_report_object __report_object; \
     uvm_pkg::uvm_report_message __uvm_msg; \
     __report_object = RO; \
     if (RM == null) RM = uvm_pkg::uvm_report_message::new_report_message(); \
       __uvm_msg = RM; \
       __uvm_msg.set_report_message(SEVERITY, ID, MSG, VERBOSITY, FILE, LINE, "");
`define uvm_message_context_end \
       __report_object.uvm_process_report_message(__uvm_msg); \
  `uvm_report_end
`define uvm_info_begin(ID, MSG, VERBOSITY, RM = __uvm_msg) \
   `uvm_message_begin(uvm_pkg::UVM_INFO, ID, MSG, VERBOSITY, `uvm_file, `uvm_line, RM)
`define uvm_info_end \
   `uvm_message_end
`define uvm_warning_begin(ID, MSG, RM = __uvm_msg) \
   `uvm_message_begin(uvm_pkg::UVM_WARNING, ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, RM)
`define uvm_warning_end \
   `uvm_message_end
`define uvm_error_begin(ID, MSG, RM = __uvm_msg) \
   `uvm_message_begin(uvm_pkg::UVM_ERROR, ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, RM)
`define uvm_error_end \
   `uvm_message_end
`define uvm_fatal_begin(ID, MSG, RM = __uvm_msg) \
   `uvm_message_begin(uvm_pkg::UVM_FATAL, ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, RM)
`define uvm_fatal_end \
   `uvm_message_end
`define uvm_info_context_begin(ID, MSG, VERBOSITY, RO, RM = __uvm_msg) \
   `uvm_message_context_begin(uvm_pkg::UVM_INFO, ID, MSG, VERBOSITY, `uvm_file, `uvm_line, RO, RM)
`define uvm_info_context_end \
   `uvm_message_context_end
`define uvm_warning_context_begin(ID, MSG, RO, RM = __uvm_msg) \
   `uvm_message_context_begin(uvm_pkg::UVM_WARNING, ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, RO, RM)
`define uvm_warning_context_end \
   `uvm_message_context_end
`define uvm_error_context_begin(ID, MSG, RO, RM = __uvm_msg) \
   `uvm_message_context_begin(uvm_pkg::UVM_ERROR, ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, RO, RM)
`define uvm_error_context_end \
   `uvm_message_context_end
`define uvm_fatal_context_begin(ID, MSG, RO, RM = __uvm_msg) \
   `uvm_message_context_begin(uvm_pkg::UVM_FATAL, ID, MSG, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, RO, RM)
`define uvm_fatal_context_end \
   `uvm_message_context_end
`define uvm_message_add_tag(NAME, VALUE, ACTION=(uvm_pkg::UVM_LOG|uvm_pkg::UVM_RM_RECORD)) \
    __uvm_msg.add_string(NAME, VALUE, ACTION);
`define uvm_message_add_int(VAR, RADIX, LABEL="", ACTION=(uvm_pkg::UVM_LOG|uvm_pkg::UVM_RM_RECORD)) \
    if (LABEL == "") \
      __uvm_msg.add_int(`"VAR`", VAR, $bits(VAR), RADIX, ACTION); \
    else \
      __uvm_msg.add_int(LABEL, VAR, $bits(VAR), RADIX, ACTION);
`define uvm_message_add_string(VAR, LABEL="", ACTION=(uvm_pkg::UVM_LOG|uvm_pkg::UVM_RM_RECORD)) \
    if (LABEL == "") \
      __uvm_msg.add_string(`"VAR`", VAR, ACTION); \
    else \
      __uvm_msg.add_string(LABEL, VAR, ACTION);
`define uvm_message_add_object(VAR, LABEL="", ACTION=(uvm_pkg::UVM_LOG|uvm_pkg::UVM_RM_RECORD)) \
    if (LABEL == "") \
      __uvm_msg.add_object(`"VAR`", VAR, ACTION); \
    else \
      __uvm_msg.add_object(LABEL, VAR, ACTION);
`define UVM_PHASE_DEFINES_SVH
`define m_uvm_task_phase(PHASE,COMP,PREFIX) \
        class PREFIX``PHASE``_phase extends uvm_task_phase; \
          virtual task exec_task(uvm_component comp, uvm_phase phase); \
            COMP comp_; \
            if ($cast(comp_,comp)) \
              comp_.``PHASE``_phase(phase); \
          endtask \
          local static PREFIX``PHASE``_phase m_inst; \
          `uvm_type_name_decl(`"PREFIX``PHASE``_phase`") \
          static function PREFIX``PHASE``_phase get(); \
            if(m_inst == null) begin \
              m_inst = new; \
            end \
            return m_inst; \
          endfunction \
          protected function new(string name=`"PHASE`"); \
            super.new(name); \
          endfunction \
        endclass \

`define m_uvm_topdown_phase(PHASE,COMP,PREFIX) \
        class PREFIX``PHASE``_phase extends uvm_topdown_phase; \
          virtual function void exec_func(uvm_component comp, uvm_phase phase); \
            COMP comp_; \
            if ($cast(comp_,comp)) \
              comp_.``PHASE``_phase(phase); \
          endfunction \
          local static PREFIX``PHASE``_phase m_inst; \
          `uvm_type_name_decl(`"PREFIX``PHASE``_phase`") \
          static function PREFIX``PHASE``_phase get(); \
            if(m_inst == null) begin \
              m_inst = new(); \
            end \
            return m_inst; \
          endfunction \
          protected function new(string name=`"PHASE`"); \
            super.new(name); \
          endfunction \
        endclass \

`define m_uvm_bottomup_phase(PHASE,COMP,PREFIX) \
        class PREFIX``PHASE``_phase extends uvm_bottomup_phase; \
          virtual function void exec_func(uvm_component comp, uvm_phase phase); \
            COMP comp_; \
            if ($cast(comp_,comp)) \
              comp_.``PHASE``_phase(phase); \
          endfunction \
          static PREFIX``PHASE``_phase m_inst; \
          `uvm_type_name_decl(`"PREFIX``PHASE``_phase`") \
          static function PREFIX``PHASE``_phase get(); \
            if(m_inst == null) begin \
              m_inst = new(); \
            end \
            return m_inst; \
          endfunction \
          protected function new(string name=`"PHASE`"); \
            super.new(name); \
          endfunction \
        endclass \

`define uvm_builtin_task_phase(PHASE) \
        `m_uvm_task_phase(PHASE,uvm_component,uvm_)
`define uvm_builtin_topdown_phase(PHASE) \
        `m_uvm_topdown_phase(PHASE,uvm_component,uvm_)
`define uvm_builtin_bottomup_phase(PHASE) \
        `m_uvm_bottomup_phase(PHASE,uvm_component,uvm_)
`define uvm_user_task_phase(PHASE,COMP,PREFIX) \
        `m_uvm_task_phase(PHASE,COMP,PREFIX)
`define uvm_user_topdown_phase(PHASE,COMP,PREFIX) \
        `m_uvm_topdown_phase(PHASE,COMP,PREFIX)
`define uvm_user_bottomup_phase(PHASE,COMP,PREFIX) \
        `m_uvm_bottomup_phase(PHASE,COMP,PREFIX)
`define UVM_PRINTER_DEFINES_SVH
`define uvm_print_int(VALUE, SIZE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_int(`"VALUE`", VALUE, SIZE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_named_int(NAME, VALUE, SIZE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
if (SIZE > 64) \
  PRINTER.print_field(NAME, VALUE, SIZE, RADIX, ".", `"VALUE_TYPE`"); \
else \
  PRINTER.print_field_int(NAME, VALUE, SIZE, RADIX, ".", `"VALUE_TYPE`");
`define uvm_print_real(VALUE, PRINTER=printer) \
  `uvm_print_named_real(`"VALUE`", VALUE, PRINTER)
`define uvm_print_named_real(NAME, VALUE, PRINTER=printer) \
  PRINTER.print_real(NAME, VALUE);
`define uvm_print_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_enum(TYPE, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_enum(TYPE, NAME, VALUE, PRINTER=printer) \
if (VALUE.name()  == "") \
  `uvm_print_named_int(NAME, VALUE, $bits(VALUE), UVM_NORADIX, TYPE, PRINTER) \
else \
  PRINTER.print_generic(NAME, `"TYPE`", $bits(VALUE), VALUE.name());
`define uvm_print_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_object(`"VALUE`", VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_named_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
    (RECURSION_POLICY != PRINTER.get_recursion_policy())) begin \
  uvm_recursion_policy_enum __saved_recursion_policy  = PRINTER.get_recursion_policy(); \
  PRINTER.set_recursion_policy(RECURSION_POLICY); \
  `m_uvm_print_named_object(NAME, VALUE, PRINTER) \
  PRINTER.set_recursion_policy(__saved_recursion_policy); \
end \
else begin \
  `m_uvm_print_named_object(NAME, VALUE, PRINTER) \
end
`define m_uvm_print_named_object(NAME, VALUE, PRINTER) \
if (PRINTER.object_printed(VALUE, PRINTER.get_recursion_policy()) != uvm_policy::NEVER) begin \
  uvm_recursion_policy_enum __saved_recursion_policy = PRINTER.get_recursion_policy(); \
  PRINTER.set_recursion_policy(UVM_REFERENCE); \
  PRINTER.print_object(NAME, VALUE); \
  PRINTER.set_recursion_policy(__saved_recursion_policy); \
end \
else begin \
  PRINTER.print_object(NAME, VALUE); \
end
`define uvm_print_string(VALUE, PRINTER=printer) \
  `uvm_print_named_string(`"VALUE`", VALUE, PRINTER)
`define uvm_print_named_string(NAME, VALUE, PRINTER=printer) \
  PRINTER.print_string(NAME, VALUE);
`define uvm_print_qda_int(ARRAY_TYPE, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(ARRAY_TYPE, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_named_qda_int(ARRAY_TYPE, NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(``VALUE_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements      = PRINTER.get_begin_elements(); \
    __tmp_end_elements        = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_int($sformatf("[%0d]", __tmp_index), \
                             VALUE[__tmp_index], \
                             $bits(VALUE[__tmp_index]), \
                             RADIX, \
                             VALUE_TYPE, \
                             PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_int($sformatf("[%0d]", __tmp_index), \
                               VALUE[__tmp_index], \
                               $bits(VALUE[__tmp_index]), \
                               RADIX, \
                               VALUE_TYPE, \
                               PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_int($sformatf("[%0d]", __tmp_curr), \
                               VALUE[__tmp_curr], \
                               $bits(VALUE[__tmp_curr]), \
                               RADIX, \
                               VALUE_TYPE, \
                               PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end
`define uvm_print_array_int(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(da, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_named_array_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(da, NAME, VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_sarray_int(VALUE, RADIX=UVM_RADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(sa, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_named_sarray_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(sa, NAME, VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_queue_int(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(queue, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_named_queue_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(queue, NAME, VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_qda_real(ARRAY_TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(ARRAY_TYPE, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_qda_real(ARRAY_TYPE, NAME, VALUE, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(real)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements    = PRINTER.get_begin_elements(); \
    __tmp_end_elements      = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_real($sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_real($sformatf("[%0d]", __tmp_index), \
                                  VALUE[__tmp_index], \
                                  PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_real($sformatf("[%0d]", __tmp_curr), \
                                  VALUE[__tmp_curr], \
                                  PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end
`define uvm_print_array_real(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(da, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_array_real(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(da, NAME, VALUE, PRINTER)
`define uvm_print_sarray_real(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(sa, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_sarray_real(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(sa, NAME, VALUE, PRINTER)
`define uvm_print_queue_real(VALUE,PRINTER=printer) \
  `uvm_print_named_qda_real(queue, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_queue_real(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(queue, NAME, VALUE, PRINTER)
`define uvm_print_qda_enum(ARRAY_TYPE, TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(ARRAY_TYPE, TYPE, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_qda_enum(ARRAY_TYPE, TYPE, NAME, VALUE, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             {`"ARRAY_TYPE``(`", `"TYPE`", ")"}); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements      = PRINTER.get_begin_elements(); \
    __tmp_end_elements        = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_enum(TYPE, \
                              $sformatf("[%0d]", __tmp_index), \
                              VALUE[__tmp_index], \
                              PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_enum(TYPE, \
                                $sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_enum(TYPE, \
                                $sformatf("[%0d]", __tmp_curr), \
                                VALUE[__tmp_curr], \
                                PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end
`define uvm_print_array_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(da, `"VALUE`", TYPE, VALUE, PRINTER)
`define uvm_print_named_array_enum(TYPE, NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(da, TYPE, NAME, VALUE, PRINTER)
`define uvm_print_sarray_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(sa, TYPE, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_sarray_enum(TYPE, NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(sa, TYPE, NAME, VALUE, PRINTER)
`define uvm_print_queue_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(queue, TYPE, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_queue_enum(TYPE, NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(queue, TYPE, NAME, VALUE, PRINTER)
`define uvm_print_qda_object(ARRAY_TYPE, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(ARRAY_TYPE, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_named_qda_object(ARRAY_TYPE, NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(object)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    uvm_recursion_policy_enum __tmp_recursion_policy; \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements    = PRINTER.get_begin_elements(); \
    __tmp_end_elements      = PRINTER.get_end_elements(); \
    __tmp_recursion_policy  = PRINTER.get_recursion_policy(); \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(RECURSION_POLICY); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `m_uvm_print_named_object($sformatf("[%0d]", __tmp_index), \
                                  VALUE[__tmp_index], \
                                  PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `m_uvm_print_named_object($sformatf("[%0d]", __tmp_index), \
                                    VALUE[__tmp_index], \
                                    PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `m_uvm_print_named_object($sformatf("[%0d]", __tmp_curr), \
                                    VALUE[__tmp_curr], \
                                    PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(__tmp_recursion_policy); \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end
`define uvm_print_array_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(da, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_named_array_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(da, NAME, VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_sarray_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(sa, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_named_sarray_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(sa, NAME, VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_queue_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(queue, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_named_queue_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(queue, NAME, VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_qda_string(ARRAY_TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(ARRAY_TYPE, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_qda_string(ARRAY_TYPE, NAME, VALUE, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(string)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements    = PRINTER.get_begin_elements(); \
    __tmp_end_elements      = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_string($sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_string($sformatf("[%0d]", __tmp_index), \
                                  VALUE[__tmp_index], \
                                  PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_string($sformatf("[%0d]", __tmp_curr), \
                                  VALUE[__tmp_curr], \
                                  PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end
`define uvm_print_array_string(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(da, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_array_string(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(da, NAME, VALUE, PRINTER)
`define uvm_print_sarray_string(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(sa, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_sarray_string(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(sa, NAME, VALUE, PRINTER)
`define uvm_print_queue_string(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(queue, `"VALUE`", VALUE, PRINTER)
`define uvm_print_named_queue_string(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(queue, NAME, VALUE, PRINTER)
`define uvm_print_aa_int_string(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_aa_int_string(`"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_named_aa_int_string(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(``VALUE_TYPE``,string)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_int($sformatf("[%s]", __tmp_index), \
                           VALUE[__tmp_index], \
                           $bits(VALUE[__tmp_index]), \
                           RADIX, \
                           VALUE_TYPE, \
                           PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end
`define uvm_print_aa_object_string(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_aa_object_string(`"VALUE`", VALUE, RECURSION_POLICY, PRINTER)
`define uvm_print_named_aa_object_string(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             "aa(object,string)"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    uvm_recursion_policy_enum __tmp_recursion_policy; \
    __tmp_recursion_policy  = PRINTER.get_recursion_policy(); \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(RECURSION_POLICY); \
    foreach(VALUE[__tmp_index]) \
      `m_uvm_print_named_object($sformatf("[%s]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER ) \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(__tmp_recursion_policy); \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end
`define uvm_print_aa_string_string(VALUE, PRINTER=printer) \
  `uvm_print_named_aa_string_string(`"VALUE`", VALUE, PRINTER)
`define uvm_print_named_aa_string_string(NAME, VALUE, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             "aa(string,string)"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_string($sformatf("[%s]", __tmp_index), \
                              VALUE[__tmp_index], \
                              PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end
`define uvm_print_aa_int_int(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, INDEX_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_int_int(`"VALUE`", VALUE, RADIX, VALUE_TYPE, INDEX_TYPE, PRINTER)
`define uvm_print_named_aa_int_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, INDEX_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(``VALUE_TYPE``,``INDEX_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_int($sformatf("[%0d]", __tmp_index), \
                           VALUE[__tmp_index], \
                           $bits(VALUE[__tmp_index]), \
                           RADIX, \
                           VALUE_TYPE, \
                           PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end
`define uvm_print_aa_object_int(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, INDEX_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_object_int(`"VALUE`", VALUE, RECURSION_POLICY, INDEX_TYPE, PRINTER)
`define uvm_print_named_aa_object_int(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, INDEX_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(object,``INDEX_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    uvm_recursion_policy_enum __tmp_recursion_policy; \
    __tmp_recursion_policy  = PRINTER.get_recursion_policy(); \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(RECURSION_POLICY); \
    foreach(VALUE[__tmp_index]) \
      `m_uvm_print_named_object($sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER ) \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(__tmp_recursion_policy); \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end
`define uvm_print_aa_string_int(VALUE, INDEX_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_string_int(`"VALUE`", VALUE, INDEX_TYPE, PRINTER)
`define uvm_print_named_aa_string_int(NAME, VALUE, INDEX_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(string,``INDEX_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_string($sformatf("[%0d]", __tmp_index), \
                              VALUE[__tmp_index], \
                              PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end
`define uvm_print_aa_int_enum(ENUM_TYPE, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_int_enum(`"VALUE`", ENUM_TYPE, VALUE, RADIX, VALUE_TYPE, PRINTER)
`define uvm_print_named_aa_int_enum(NAME, ENUM_TYPE, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(``VALUE_TYPE``,``ENUM_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_int((__tmp_index.name() == "") ? $sformatf("[%s'(%0d)]", `"ENUM_TYPE`",__tmp_index) \
                                                      : $sformatf("[%s]", __tmp_index.name()), \
                           VALUE[__tmp_index], \
                           $bits(VALUE[__tmp_index]), \
                           RADIX, \
                           VALUE_TYPE, \
                           PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end
`define uvm_print_int3(F, R, P) \
  `uvm_print_int(F, $bits(F), R, , P)
`define uvm_print_int4(F, R, NM, P) \
  `uvm_print_named_int(NM, F, $bits(F), R, , P)
`define uvm_print_object2(F, P) \
  `uvm_print_object(F, ,P)
`define uvm_print_string2(F, P) \
  `uvm_print_string(F, P)
`define uvm_print_array_int3(F, R, P) \
  `uvm_print_named_qda_int(da, `"F`", F, R, ,P)
`define uvm_print_sarray_int3(F, R, P) \
  `uvm_print_named_qda_int(sa, `"F`", F, R, ,P)
`define uvm_print_qda_int4(F, R, P, T) \
  `uvm_print_named_qda_int(T, `"F`", F, R, ,P)
`define uvm_print_queue_int3(F, R, P) \
  `uvm_print_named_qda_int(queue, `"F`", F, R, ,P)
`define uvm_print_array_object3(F, P, FLAG) \
  `uvm_print_array_object(F, ,P)
`define uvm_print_sarray_object3(F, P,FLAG) \
  `uvm_print_sarray_object(F, ,P)
`define uvm_print_object_qda4(F, P, T, FLAG) \
  `uvm_print_named_qda_object(T, `"F`", F, ,P)
`define uvm_print_object_queue3(F, P, FLAG) \
  `uvm_print_queue_object(F, ,P)
`define uvm_print_array_string2(F, P) \
  `uvm_print_array_string(F, P)
`define uvm_print_sarray_string2(F, P) \
  `uvm_print_sarray_string(F, P)
`define uvm_print_string_qda3(F, P, T) \
  `uvm_print_named_qda_string(T, `"F`", F, P)
`define uvm_print_string_queue2(F, P) \
  `uvm_print_queue_string(F, P)
`define uvm_print_aa_string_int3(F, R, P) \
  `uvm_print_aa_int_string(F, R, ,P)
`define uvm_print_aa_string_object3(F, P, FLAG) \
  `uvm_print_aa_object_string(F, ,P)
`define uvm_print_aa_string_string2(F, P) \
  `uvm_print_aa_string_string(F, P)
`define uvm_print_aa_int_object3(F, P, FLAG) \
  `uvm_print_aa_object_int(F, ,P)
`define uvm_print_aa_int_key4(KEY, F, R, P) \
  `uvm_print_aa_int_int(F, R, ,KEY, P)
`define UVM_COMPARER_DEFINES_SVH
`define m_uvm_compare_threshold_begin(COMPARER) \
  if ((!COMPARER.get_threshold() || \
       (COMPARER.get_result() < COMPARER.get_threshold()))) begin \

`define m_uvm_compare_threshold_end \
  end
`define m_uvm_compare_begin(LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) !== (RVALUE)) begin \

`define m_uvm_compare_end \
    end \
  `m_uvm_compare_threshold_end
`define uvm_compare_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
`define uvm_compare_named_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
     if ($bits(LVALUE) <= 64) \
       void'(COMPARER.compare_field_int(NAME , LVALUE, RVALUE, $bits(LVALUE), RADIX)); \
     else \
       void'(COMPARER.compare_field(NAME , LVALUE, RVALUE, $bits(LVALUE), RADIX)); \
  `m_uvm_compare_end
`define uvm_compare_enum(LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `uvm_compare_named_enum(`"LVALUE`", LVALUE, RVALUE, TYPE, COMPARER)
`define uvm_compare_named_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
     void'(COMPARER.compare_string(NAME , \
                                   $sformatf("%s'(%s)", `"TYPE`", LVALUE.name()), \
                                   $sformatf("%s'(%s)", `"TYPE`", RVALUE.name())) ); \
  `m_uvm_compare_end
`define uvm_compare_real(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_real(`"LVALUE`", LVALUE, RVALUE, COMPARER)
`define uvm_compare_named_real(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) != (RVALUE)) begin \
      void'(COMPARER.compare_field_real(NAME , LVALUE, RVALUE)); \
    end \
  `m_uvm_compare_threshold_end
`define uvm_compare_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_object(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
`define uvm_compare_named_object(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
     uvm_recursion_policy_enum prev_rec__; \
     prev_rec__ = COMPARER.get_recursion_policy(); \
     if (POLICY != UVM_DEFAULT_POLICY) \
       COMPARER.set_recursion_policy(POLICY); \
     `m_uvm_compare_named_object(NAME, LVALUE, RVALUE, COMPARER) \
     if (POLICY != UVM_DEFAULT_POLICY) \
       COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end
`define m_uvm_compare_named_object(NAME, LVALUE, RVALUE, COMPARER) \
  if (COMPARER.get_recursion_policy() != UVM_REFERENCE) begin \
    bit local_rv__; \
    uvm_policy::recursion_state_e local_state__; \
    local_state__ = COMPARER.object_compared(LVALUE, RVALUE, COMPARER.get_recursion_policy(), local_rv__); \
    if ((local_state__ == uvm_policy::FINISHED) && \
        !local_rv__) \
      COMPARER.print_msg($sformatf("'%s' miscompared using saved return value", NAME)); \
    else if (local_state__ == uvm_policy::NEVER) \
      void'(COMPARER.compare_object(NAME, LVALUE, RVALUE)); \
    /* else skip to avoid infinite loop */ \
  end \
  else begin \
    void'(COMPARER.compare_object(NAME, LVALUE, RVALUE)); \
  end
`define uvm_compare_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
`define uvm_compare_named_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) != (RVALUE)) begin \
      void'(COMPARER.compare_string(NAME , LVALUE, RVALUE)); \
    end \
  `m_uvm_compare_threshold_end
`define uvm_compare_sarray_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_sarray_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
`define uvm_compare_named_sarray_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach (LVALUE[i]) begin \
      `uvm_compare_named_int($sformatf("%s[%0d]", NAME, i), \
                             LVALUE[i], \
                             RVALUE[i], \
                             RADIX, \
                             COMPARER) \
    end \
  `m_uvm_compare_end
`define uvm_compare_qda_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_qda_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
`define uvm_compare_named_qda_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_int(NAME, LVALUE, RVALUE, RADIX, COMPARER) \
  `m_uvm_compare_end
`define uvm_compare_sarray_real(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_sarray_real(`"LVALUE`", LVALUE, RVALUE,COMPARER)
`define uvm_compare_named_sarray_real(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) != (RVALUE)) begin \
      foreach (LVALUE[i]) begin \
        `uvm_compare_named_real($sformatf("%s[%0d]", NAME, i), \
                               LVALUE[i], \
                               RVALUE[i], \
                               COMPARER) \
      end \
    end \
  `m_uvm_compare_threshold_end
`define uvm_compare_qda_real(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_qda_real(`"LVALUE`", LVALUE, RVALUE, COMPARER)
`define uvm_compare_named_qda_real(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    `uvm_compare_named_real($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           COMPARER) \
    `uvm_compare_named_sarray_real(NAME, LVALUE, RVALUE, COMPARER) \
  `m_uvm_compare_threshold_end
`define uvm_compare_sarray_enum(LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `uvm_compare_named_sarray_enum(`"LVALUE`", LVALUE, RVALUE, TYPE, COMPARER)
`define uvm_compare_named_sarray_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach (LVALUE[i]) begin \
      `uvm_compare_named_enum($sformatf("%s[%0d]", NAME, i), \
                              LVALUE[i], \
                              RVALUE[i], \
                              TYPE, \
                              COMPARER) \
    end \
  `m_uvm_compare_end
`define uvm_compare_qda_enum(LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `uvm_compare_named_qda_enum(`"LVALUE`", LVALUE, RVALUE, TYPE, COMPARER)
`define uvm_compare_named_qda_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER) \
  `m_uvm_compare_end
`define uvm_compare_sarray_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_sarray_object(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
`define uvm_compare_named_sarray_object(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    uvm_recursion_policy_enum prev_rec__; \
    prev_rec__ = COMPARER.get_recursion_policy(); \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(POLICY); \
    foreach (LVALUE[i]) begin \
      `m_uvm_compare_named_object($sformatf("%s[%0d]", NAME, i), \
                                  LVALUE[i], \
                                  RVALUE[i], \
                                  COMPARER) \
    end \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end
`define uvm_compare_qda_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_qda_object(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
`define uvm_compare_named_qda_object(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_object(NAME, LVALUE, RVALUE, POLICY, COMPARER) \
  `m_uvm_compare_end
`define uvm_compare_sarray_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_sarray_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
`define uvm_compare_named_sarray_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach (LVALUE[i]) begin \
      `uvm_compare_named_string($sformatf("%s[%0d]", NAME, i), \
                                LVALUE[i], \
                                RVALUE[i], \
                                COMPARER) \
    end \
  `m_uvm_compare_end
`define uvm_compare_qda_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_qda_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
`define uvm_compare_named_qda_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_string(NAME, LVALUE, RVALUE, COMPARER) \
  `m_uvm_compare_end
`define uvm_compare_aa_int_string(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_aa_int_string(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
`define uvm_compare_named_aa_int_string(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_int($sformatf("%s[%s]", NAME, i), \
                               LVALUE[i], \
                               RVALUE[i], \
                               RADIX, \
                               COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end
`define uvm_compare_aa_object_string(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_aa_object_string(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
`define uvm_compare_named_aa_object_string(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    uvm_recursion_policy_enum prev_rec__; \
    prev_rec__ = COMPARER.get_recursion_policy(); \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(POLICY); \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in RHS", NAME, i)); \
      end \
      else begin \
        `m_uvm_compare_named_object($sformatf("%s[%s]", NAME, i), \
                                    LVALUE[i], \
                                    RVALUE[i], \
                                    COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in LHS", NAME, i)); \
      end \
    end \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end
`define uvm_compare_aa_string_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_aa_string_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
`define uvm_compare_named_aa_string_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_string($sformatf("%s[%s]", NAME, i), \
                                  LVALUE[i], \
                                  RVALUE[i], \
                                  COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end
`define uvm_compare_aa_int_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_aa_int_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
`define uvm_compare_named_aa_int_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_int($sformatf("%s[%d]", NAME, i), \
                               LVALUE[i], \
                               RVALUE[i], \
                               RADIX, \
                               COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end
`define uvm_compare_aa_object_int(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_aa_object_int(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
`define uvm_compare_named_aa_object_int(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    uvm_recursion_policy_enum prev_rec__; \
    prev_rec__ = COMPARER.get_recursion_policy(); \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(POLICY); \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in RHS", NAME, i)); \
      end \
      else begin \
        `m_uvm_compare_named_object($sformatf("%s[%s]", NAME, i), \
                                    LVALUE[i], \
                                    RVALUE[i], \
                                    COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in LHS", NAME, i)); \
      end \
    end \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end
`define uvm_compare_aa_string_int(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_aa_string_int(`"LVALUE`", LVALUE, RVALUE, COMPARER)
`define uvm_compare_named_aa_string_int(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%d' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_string($sformatf("%s[%d]", NAME, i), \
                                  LVALUE[i], \
                                  RVALUE[i], \
                                  COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%d' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end
`define UVM_RECORDER_DEFINES_SVH
`define uvm_record_attribute(TR_HANDLE,NAME,VALUE,RECORDER=recorder) \
      RECORDER.record_generic(NAME, $sformatf("%p", VALUE));
`define uvm_record_int(NAME,VALUE,SIZE,RADIX = UVM_NORADIX,RECORDER=recorder) \
    if (RECORDER != null && RECORDER.is_open()) begin \
      if (RECORDER.use_record_attribute()) \
        `uvm_record_attribute(RECORDER.get_record_attribute_handle(),NAME,VALUE,RECORDER) \
      else \
        if (SIZE > 64) \
          RECORDER.record_field(NAME, VALUE, SIZE, RADIX); \
        else \
          RECORDER.record_field_int(NAME, VALUE, SIZE, RADIX); \
    end
`define uvm_record_string(NAME,VALUE,RECORDER=recorder) \
    if (RECORDER != null && RECORDER.is_open()) begin \
      if (RECORDER.use_record_attribute()) \
        `uvm_record_attribute(RECORDER.get_record_attribute_handle(),NAME,VALUE,RECORDER) \
      else \
        RECORDER.record_string(NAME,VALUE); \
    end
`define uvm_record_time(NAME,VALUE,RECORDER=recorder) \
    if (RECORDER != null && RECORDER.is_open()) begin \
      if (RECORDER.use_record_attribute()) \
        `uvm_record_attribute(RECORDER.get_record_attribute_handle(),NAME,VALUE,RECORDER) \
      else \
         RECORDER.record_time(NAME,VALUE); \
    end
`define uvm_record_real(NAME,VALUE,RECORDER=recorder) \
    if (RECORDER != null && RECORDER.is_open()) begin \
      if (RECORDER.use_record_attribute()) \
        `uvm_record_attribute(RECORDER.get_record_attribute_handle(),NAME,VALUE,RECORDER) \
      else \
        RECORDER.record_field_real(NAME,VALUE); \
    end
`define uvm_record_field(NAME,VALUE,RECORDER=recorder) \
   if (RECORDER != null && RECORDER.is_open()) begin \
     if (RECORDER.use_record_attribute()) begin \
       `uvm_record_attribute(RECORDER.get_record_attribute_handle(),NAME,VALUE,RECORDER) \
     end \
     else \
       RECORDER.record_generic(NAME, $sformatf("%p", VALUE)); \
   end
`define uvm_record_enum(NAME,VALUE,TYPE,RECORDER=recorder) \
  if (RECORDER != null && RECORDER.is_open()) begin \
    if (RECORDER.use_record_attribute()) begin \
       `uvm_record_attribute(RECORDER.get_record_attribute_handle(),NAME,VALUE,RECORDER) \
    end \
    else begin \
      if (VALUE.name() == "") \
        RECORDER.record_generic(NAME, $sformatf("%0d", VALUE), `"TYPE`"); \
      else \
        RECORDER.record_generic(NAME, VALUE.name(), `"TYPE`"); \
    end \
 end
`define uvm_record_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, RECORDER=recorder) \
  `uvm_record_named_object(`"VALUE`", VALUE, RECURSION_POLICY, RECORDER)
`define uvm_record_named_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, RECORDER=recorder) \
if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
    (RECURSION_POLICY != RECORDER.get_recursion_policy())) begin \
  uvm_recursion_policy_enum __saved_recursion_policy  = RECORDER.get_recursion_policy(); \
  RECORDER.set_recursion_policy(RECURSION_POLICY); \
  `m_uvm_record_named_object(NAME, VALUE, RECORDER) \
  RECORDER.set_recursion_policy(__saved_recursion_policy); \
end \
else begin \
  `m_uvm_record_named_object(NAME, VALUE, RECORDER) \
end
`define m_uvm_record_named_object(NAME, VALUE, RECORDER) \
if (RECORDER.object_recorded(VALUE, RECORDER.get_recursion_policy()) != uvm_policy::NEVER) begin \
  uvm_recursion_policy_enum __saved_recursion_policy = RECORDER.get_recursion_policy(); \
  RECORDER.set_recursion_policy(UVM_REFERENCE); \
  RECORDER.record_object(NAME, VALUE); \
  RECORDER.set_recursion_policy(__saved_recursion_policy); \
end \
else begin \
  RECORDER.record_object(NAME, VALUE); \
end
`define uvm_record_qda_int(ARG, RADIX,RECORDER=recorder) \
  begin \
    int sz__ = $size(ARG); \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC,RECORDER) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_int(nm__, ARG[i], $bits(ARG[i]), RADIX, RECORDER) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_int(nm__, ARG[i], $bits(ARG[i]), RADIX, RECORDER) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_int(nm__, ARG[i], $bits(ARG[i]), RADIX, RECORDER) \
      end \
    end \
  end
`define uvm_record_qda_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, RECORDER=recorder) \
   begin \
    int sz__ = $size(VALUE); \
     if(sz__ == 0) begin \
      `uvm_record_int(`"VALUE`", 0, 32, UVM_DEC, RECORDER) \
     end \
    else begin \
      uvm_recursion_policy_enum __tmp_recursion_policy; \
      __tmp_recursion_policy  = RECORDER.get_recursion_policy(); \
      if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
          (__tmp_recursion_policy != RECURSION_POLICY)) \
        RECORDER.set_recursion_policy(RECURSION_POLICY); begin \
        if(sz__ < 10) begin \
          foreach(VALUE[__tmp_index]) begin \
            `m_uvm_record_named_object($sformatf("%s[%0d]", `"VALUE`", __tmp_index), \
                                      VALUE[__tmp_index], \
                                      RECORDER) \
           end \
         end \
         else begin \
          for(int __tmp_index=0; __tmp_index<5; ++__tmp_index) begin \
            `m_uvm_record_named_object($sformatf("%s[%0d]", `"VALUE`", __tmp_index), \
                                      VALUE[__tmp_index], \
                                      RECORDER) \
          end \
          for(int __tmp_index=sz__-5; __tmp_index<sz__; ++__tmp_index) begin \
            `m_uvm_record_named_object($sformatf("%s[%0d]", `"VALUE`", __tmp_index), \
                                      VALUE[__tmp_index], \
                                      RECORDER) \
          end \
         end \
       end \
      if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
          (__tmp_recursion_policy != RECURSION_POLICY)) \
        RECORDER.set_recursion_policy(__tmp_recursion_policy); \
     end \
   end
`define uvm_record_qda_enum(ARG, T,RECORDER=recorder) \
  begin \
    int sz__ = $size(ARG); \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC, RECORDER) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_enum(nm__, ARG[i], T, RECORDER) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_enum(nm__, ARG[i], T, RECORDER) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_enum(nm__, ARG[i], T, RECORDER) \
      end \
    end \
  end
`define uvm_record_qda_string(ARG,RECORDER=recorder) \
  begin \
    int sz__; \
    /* workaround for sarray string + $size */ \
    foreach (ARG[i]) \
      sz__ = i; \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC, RECORDER) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_string(nm__, ARG[i], RECORDER) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_string(nm__, ARG[i], RECORDER) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_string(nm__, ARG[i], RECORDER) \
      end \
    end \
  end
`define uvm_record_qda_real(ARG,RECORDER=recorder) \
  begin \
    int sz__; \
    /* workaround for sarray real + $size */ \
    foreach (ARG[i]) \
      sz__ = i; \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC, RECORDER) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_real(nm__, ARG[i], RECORDER) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_real(nm__, ARG[i], RECORDER) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_real(nm__, ARG[i], RECORDER) \
      end \
    end \
  end
`define UVM_RESOURCE_DEFINES_SVH
`define uvm_resource_read(SUCCESS, RSRC, TYPE, VAL, OBJ=null) \
begin                                                           \
  uvm_resource#(TYPE) __tmp_rsrc__;                             \
  SUCCESS = $cast(__tmp_rsrc__, RSRC);                          \
  if (SUCCESS) begin                                            \
    VAL = __tmp_rsrc__.read(OBJ);                               \
  end                                                           \
end
`define uvm_resource_builtin_int_read(SUCCESS, RSRC, VAL, OBJ=null) \
begin                                                               \
  `uvm_resource_read(SUCCESS, RSRC, uvm_integral_t, VAL, OBJ)                \
  if (!SUCCESS)                                                     \
    `uvm_resource_read(SUCCESS, RSRC, uvm_bitstream_t, VAL, OBJ)             \
  if (!SUCCESS)                                                     \
    `uvm_resource_read(SUCCESS, RSRC, int, VAL, OBJ)                         \
  if (!SUCCESS)                                                     \
    `uvm_resource_read(SUCCESS, RSRC, int unsigned, VAL, OBJ)                \
end
`define uvm_resource_int_read(SUCCESS, RSRC, TYPE, VAL, OBJ=null) \
begin                                                             \
  `uvm_resource_read(SUCCESS, RSRC, TYPE, VAL, OBJ)               \
  if (!SUCCESS)                                                   \
    `uvm_resource_builtin_int_read(SUCCESS, RSRC, VAL, OBJ)       \
end
`define uvm_resource_enum_read(SUCCESS, RSRC, TYPE, VAL, OBJ=null) \
begin                                                              \
  `uvm_resource_read(SUCCESS, RSRC, TYPE, VAL, OBJ)                \
  if (!SUCCESS) begin                                              \
    TYPE __tmp_val__;                                              \
    string __tmp_string_val__;                                     \
    bit   __tmp_success_val__;                                     \
    `uvm_resource_read(__tmp_success_val__, \
                         RSRC, \
                         string, \
                         __tmp_string_val__, \
                         OBJ)                                      \
    if (__tmp_success_val__ &&                                     \
    uvm_enum_wrapper#(TYPE)::from_name(__tmp_string_val__, \
                       __tmp_val__)) begin     \
       VAL = __tmp_val__;                                          \
       SUCCESS = __tmp_success_val__;                              \
    end                                                            \
  end                                                              \
  if (!SUCCESS) begin                                              \
     typedef bit [$bits(TYPE)-1:0] __tmp_int_t__;                  \
     __tmp_int_t__                 __tmp_int_val__;                \
     bit                __tmp_success_val__;            \
     `uvm_resource_int_read(__tmp_success_val__, \
                RSRC, \
                __tmp_int_t__, \
                __tmp_int_val__, \
                OBJ)                                   \
     if (__tmp_success_val__) begin                                \
       VAL = TYPE'(__tmp_int_val__);                               \
       SUCCESS = __tmp_success_val__;                              \
     end                                                           \
  end                                                              \
end
`define uvm_resource_real_read(SUCCESS, RSRC, VAL, OBJ=null) \
begin                                                              \
  `uvm_resource_read(SUCCESS, RSRC, real, VAL, OBJ)                \
  if (!SUCCESS) begin                                              \
     typedef bit [63:0] __tmp_int_t__;                             \
     __tmp_int_t__      __tmp_int_val__;                           \
     bit             __tmp_success_val__;                       \
     `uvm_resource_int_read(__tmp_success_val__, \
                RSRC, \
                __tmp_int_t__, \
                __tmp_int_val__, \
                OBJ)                                   \
     if (__tmp_success_val__) begin                                \
       VAL = $bitstoreal(__tmp_int_val__);                         \
       SUCCESS = __tmp_success_val__;                              \
     end                                                           \
  end                                                              \
end
`define UVM_PACKER_DEFINES_SVH
`define uvm_pack_intN(VAR,SIZE,PACKER=packer) \
  if (SIZE <= $bits(uvm_integral_t)) begin \
     PACKER.pack_field_int(VAR, SIZE); \
  end \
  else if (SIZE <= $bits(uvm_bitstream_t)) begin \
     PACKER.pack_field(VAR, SIZE); \
  end \
  else begin \
    bit __array[]; \
    { << bit { __array}} = VAR; \
    __array = new [SIZE] (__array); \
    PACKER.pack_bits(__array, SIZE); \
  end
`define uvm_pack_enumN(VAR,SIZE,PACKER=packer) \
   `uvm_pack_intN(VAR,SIZE,PACKER)
`define uvm_packer_array_extension_begin(PACKER) \
  begin \
    uvm_object m__ext; \
    uvm_object m__prev_ext; \
    m__ext = uvm_packer_array_extension::get(); \
    m__prev_ext = PACKER.set_extension(m__ext);
`define uvm_packer_array_extension_end(PACKER) \
    if (m__prev_ext != null) begin \
      void'(PACKER.set_extension(m__prev_ext)); \
    end \
    else begin \
      PACKER.clear_extension(m__ext.get_object_type()); \
    end \
  end
`define uvm_pack_sarrayN(VAR,SIZE,PACKER=packer) \
    `uvm_packer_array_extension_begin(PACKER) \
        foreach(VAR `` [index]) begin \
          `uvm_pack_intN(VAR[index],SIZE,PACKER) \
        end \
    `uvm_packer_array_extension_end(PACKER)
`define uvm_pack_arrayN(VAR,SIZE,PACKER=packer) \
    begin \
      `uvm_pack_intN(VAR.size(),32,PACKER) \
      `uvm_pack_sarrayN(VAR,SIZE,PACKER) \
    end
`define uvm_pack_queueN(VAR,SIZE,PACKER=packer) \
   `uvm_pack_arrayN(VAR,SIZE,PACKER)
`define uvm_pack_int(VAR,PACKER=packer) \
   `uvm_pack_intN(VAR,$bits(VAR),PACKER)
`define uvm_pack_object(VAR,PACKER=packer) \
  PACKER.pack_object_with_meta(VAR);
`define uvm_pack_enum(VAR,PACKER=packer) \
   `uvm_pack_enumN(VAR,$bits(VAR),PACKER)
`define uvm_pack_string(VAR,PACKER=packer) \
  PACKER.pack_string(VAR);
`define uvm_pack_real(VAR,PACKER=packer) \
  PACKER.pack_real(VAR);
`define uvm_pack_sarray(VAR,PACKER=packer) \
   `uvm_pack_sarrayN(VAR,$bits(VAR[0]),PACKER)
`define uvm_pack_array(VAR,PACKER=packer) \
   `uvm_pack_arrayN(VAR,$bits(VAR[0]),PACKER)
`define uvm_pack_da(VAR,PACKER=packer) \
  `uvm_pack_array(VAR,PACKER)
`define uvm_pack_queue(VAR,PACKER=packer) \
   `uvm_pack_queueN(VAR,$bits(VAR[0]),PACKER)
`define uvm_unpack_intN(VAR,SIZE,PACKER=packer) \
  if (SIZE <= $bits(uvm_integral_t)) begin \
    VAR = PACKER.unpack_field_int(SIZE); \
  end \
  else if (SIZE <= $bits(uvm_bitstream_t)) begin \
    VAR = PACKER.unpack_field(SIZE); \
  end \
  else begin \
    bit __array[] = new [SIZE]; \
    PACKER.unpack_bits(__array, SIZE); \
    __array = new [$bits(VAR)] (__array); \
    VAR = { << bit { __array }}; \
  end
`define uvm_unpack_enumN(VAR,SIZE,TYPE,PACKER=packer) \
  begin \
    bit __array[] = new [SIZE]; \
    PACKER.unpack_bits(__array, SIZE); \
    __array = new [$bits(VAR)] (__array); \
    VAR = TYPE'({ << bit { __array }}); \
  end
`define uvm_unpack_sarrayN(VAR,SIZE,PACKER=packer) \
    `uvm_packer_array_extension_begin(PACKER) \
        foreach (VAR `` [i]) begin \
          `uvm_unpack_intN(VAR``[i], SIZE, PACKER) \
        end \
    `uvm_packer_array_extension_end(PACKER)
`define uvm_unpack_arrayN(VAR,SIZE,PACKER=packer) \
    begin \
      int sz__; \
      `uvm_unpack_intN(sz__,32,PACKER) \
      VAR = new[sz__]; \
      `uvm_unpack_sarrayN(VAR,SIZE,PACKER) \
    end
`define uvm_unpack_queueN(VAR,SIZE,PACKER=packer) \
    begin \
      int sz__; \
      `uvm_unpack_intN(sz__,32,PACKER) \
      while (VAR.size() > sz__) \
        void'(VAR.pop_back()); \
      for (int i=0; i<sz__; i++) \
        `uvm_unpack_intN(VAR[i],SIZE,PACKER) \
    end
`define uvm_unpack_int(VAR,PACKER=packer) \
   `uvm_unpack_intN(VAR,$bits(VAR),PACKER)
`define uvm_unpack_object(VAR,PACKER=packer) \
  begin \
    uvm_object __ref = VAR; \
    PACKER.unpack_object_with_meta(__ref); \
    if ((__ref != VAR) && !$cast(VAR,__ref)) begin \
      `uvm_fatal("UVM/UNPACK_EXT/OBJ_CAST_FAILED", \
                {"Could not cast object of type '", __ref.get_type_name(), \
                 "' into '", `"LVALUE`"}) \
    end \
  end
`define uvm_unpack_enum(VAR,TYPE,PACKER=packer) \
   `uvm_unpack_enumN(VAR,$bits(VAR),TYPE,PACKER)
`define uvm_unpack_string(VAR,PACKER=packer) \
  VAR = PACKER.unpack_string();
`define uvm_unpack_real(VAR,PACKER=packer) \
  VAR = PACKER.unpack_real();
`define uvm_unpack_sarray(VAR,PACKER=packer) \
   `uvm_unpack_sarrayN(VAR,$bits(VAR[0]),PACKER)
`define uvm_unpack_array(VAR,PACKER=packer) \
   `uvm_unpack_arrayN(VAR,$bits(VAR[0]),PACKER)
`define uvm_unpack_da(VAR,PACKER=packer) \
  `uvm_unpack_array(VAR,PACKER)
`define uvm_unpack_queue(VAR,PACKER=packer) \
   `uvm_unpack_queueN(VAR,$bits(VAR[0]),PACKER)
`define uvm_pack_aa_int_intN(VAR, SIZE, PACKER=packer) \
begin \
  `uvm_pack_intN(VAR.num(), 32, PACKER) \
  if (VAR.num()) begin \
    `uvm_pack_intN(SIZE, 32, PACKER) \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_int(VAR[i],PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_int_intN(VAR, SIZE, PACKER=packer) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32, PACKER) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32, PACKER) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Unpack size '%0d' different from pack size '%0d'", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, SIZE, PACKER) \
      `uvm_unpack_int(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_aa_object_intN(VAR, SIZE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    PACKER.pack_field_int(SIZE, 32); \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_object(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_object_intN(VAR, SIZE, PACKER=packer) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32, PACKER) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32, PACKER) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Size '%d' insufficient to store '%d' bits", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, __sz__, PACKER) \
      `uvm_unpack_object(VAR[__index__],PACKER) \
    end \
  end \
end
`define uvm_pack_aa_string_intN(VAR, SIZE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    PACKER.pack_field_int(SIZE, 32); \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_string(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_string_intN(VAR, SIZE, PACKER=packer) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32, PACKER) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32, PACKER) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Size '%d' insufficient to store '%d' bits", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, __sz__, PACKER) \
      `uvm_unpack_string(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_aa_object_string(VAR, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i, PACKER) \
      `uvm_pack_object(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_object_string(VAR, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__, PACKER) \
      `uvm_unpack_object(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_aa_int_string(VAR, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i, PACKER) \
      `uvm_pack_int(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_int_string(VAR, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__, PACKER) \
      `uvm_unpack_int(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_aa_string_string(VAR, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i, PACKER) \
      `uvm_pack_string(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_string_string(VAR, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__, PACKER) \
      `uvm_unpack_string(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_aa_int_enum(VAR, TYPE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_enum(i, PACKER) \
      `uvm_pack_int(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_int_enum(VAR, TYPE, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE, PACKER) \
      `uvm_unpack_int(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_aa_object_enum(VAR, TYPE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_enum(i, PACKER) \
      `uvm_pack_object(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_object_enum(VAR, TYPE, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE, PACKER) \
      `uvm_unpack_object(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_aa_string_enum(VAR, TYPE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_string(VAR[i], PACKER) \
    end \
  end \
end
`define uvm_unpack_aa_string_enum(VAR, TYPE, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE, PACKER) \
      `uvm_unpack_string(VAR[__index__], PACKER) \
    end \
  end \
end
`define uvm_pack_sarray_real(VAR, PACKER=packer) \
  `uvm_packer_array_extension_begin(PACKER) \
    foreach(VAR[index]) \
      `uvm_pack_real(VAR[index], PACKER) \
  `uvm_packer_array_extension_end(PACKER)
`define m_uvm_pack_qda_real(VAR, PACKER=packer) \
  `uvm_pack_intN(VAR.size(), 32, PACKER) \
  `uvm_pack_sarray_real(VAR, PACKER)
`define uvm_pack_queue_real(VAR, PACKER=packer) \
  `m_uvm_pack_qda_real(VAR, PACKER)
`define uvm_pack_da_real(VAR, PACKER=packer) \
  `m_uvm_pack_qda_real(VAR, PACKER)
`define uvm_unpack_sarray_real(VAR, PACKER=packer) \
  `uvm_packer_array_extension_begin(PACKER) \
  foreach(VAR[index]) \
    `uvm_unpack_real(VAR[index], PACKER) \
  `uvm_packer_array_extension_end(PACKER)
`define uvm_unpack_da_real(VAR, PACKER=packer) \
  begin \
    int tmp_size__; \
    `uvm_unpack_intN(tmp_size__, 32, PACKER) \
    VAR = new [tmp_size__]; \
    `uvm_unpack_sarray_real(VAR, PACKER) \
  end
`define uvm_unpack_queue_real(VAR, PACKER=packer) \
  begin \
    int tmp_size__; \
    `uvm_unpack_intN(tmp_size__, 32, PACKER) \
    while (VAR.size() > tmp_size__) \
      void'(VAR.pop_back()); \
    for (int i = 0; i < tmp_size__; i++) \
      `uvm_unpack_real(VAR[i], PACKER) \
  end
`define UVM_COPIER_DEFINES_SVH
`define uvm_copy_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COPIER=copier) \
if (LVALUE != RVALUE) begin \
  if ((RVALUE == null) || \
      (POLICY == UVM_REFERENCE) || \
      ((POLICY == UVM_DEFAULT_POLICY) && \
       (COPIER.get_recursion_policy() == UVM_REFERENCE))) begin \
    LVALUE = RVALUE; \
  end \
  else begin \
    uvm_object lvalue_ref__; \
    if (!COPIER.get_first_copy(RVALUE,lvalue_ref__) || !$cast(LVALUE,lvalue_ref__)) begin \
        uvm_recursion_policy_enum prev_pol__ = COPIER.get_recursion_policy(); \
        uvm_recursion_policy_enum curr_pol__; \
        if (POLICY != UVM_DEFAULT_POLICY) \
          COPIER.set_recursion_policy(POLICY); \
        curr_pol__ = COPIER.get_recursion_policy(); \
        if (LVALUE == null) begin \
          if (($cast(LVALUE, RVALUE.create(RVALUE.get_name())) == 0) || \
              (LVALUE == null)) begin \
            `uvm_fatal("UVM/COPY/NULL_CREATE", \
                   {"Could not create '", RVALUE.get_full_name(), \
                        "' of type '", RVALUE.get_type_name(), \
                        "', into '", `"LVALUE`", "'."}) \
          end \
          else begin \
             COPIER.copy_object(LVALUE, RVALUE); \
          end \
        end \
        else begin \
           if (COPIER.object_copied(LVALUE, RVALUE, curr_pol__) == uvm_policy::STARTED) begin \
             `uvm_warning("UVM/COPY/LOOP", \
                      {"Loop detected in copy operation (LHS:'", \
                   LVALUE.get_full_name(), \
                   "', RHS:'", \
                           RVALUE.get_full_name(), \
                   "')"}) \
           end \
           else begin \
             COPIER.copy_object(LVALUE, RVALUE); \
           end \
        end \
        if (POLICY != UVM_DEFAULT_POLICY) \
          COPIER.set_recursion_policy(prev_pol__); \
     end \
  end \
end
`define uvm_copy_aa_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COPIER=copier) \
if ((POLICY == UVM_REFERENCE) || !RVALUE.size()) \
  LVALUE = RVALUE; \
else begin \
  LVALUE.delete(); \
  foreach(RVALUE[i]) \
    `uvm_copy_object(LVALUE[i], RVALUE[i], POLICY, COPIER) \
end
`define uvm_copier_get_function(FUNCTION) \
function int get_``FUNCTION``_copy(uvm_object rhs, ref uvm_object lhs); \
  if (m_recur_states.exists(rhs)) \
    return m_recur_states[rhs].FUNCTION(lhs); \
  return 0; \
endfunction : get_``FUNCTION``_copy
`define UVM_OBJECT_DEFINES_SVH
`define UVM_FIELD_FLAG_SIZE UVM_FIELD_FLAG_RESERVED_BITS
`define uvm_field_utils_begin(T) \
function void do_execute_op( uvm_field_op op );                                 \
  super.do_execute_op(op);                                                      \
  __m_uvm_execute_field_op(op);                                                 \
endfunction : do_execute_op                                                     \
local function void __m_uvm_execute_field_op( uvm_field_op __local_op__ );      \
   uvm_field_flag_t local_op_type__; /* Used to avoid re-querying */            \
   T local_rhs__; /* Used for $casting copy and compare */                      \
   uvm_resource_base local_rsrc__; /* Used for UVM_SET ops */                   \
   string local_rsrc_name__;                                                    \
   uvm_object local_obj__; /* Used when trying to read uvm_object resources */  \
   bit local_success__; /* Used when trying to read resources */                \
   typedef T __local_type__; /* Used for referring to type T in field macros */ \
   int local_size__; /* Used when unpacking size values */                      \
   /* All possible policy classes */                                            \
   /* Using the same name as the do_* methods, allows macro reuse */            \
   uvm_printer __local_printer__;                                               \
   uvm_comparer __local_comparer__;                                             \
   uvm_recorder __local_recorder__;                                             \
   uvm_packer __local_packer__;                                                 \
   uvm_copier __local_copier__;                                                 \
   uvm_queue#(uvm_acs_name_struct) __local_field_names__;                       \
   void'($cast(local_rhs__, __local_op__.get_rhs()));                           \
   if (($cast(local_rsrc__, __local_op__.get_rhs())) &&                         \
       (local_rsrc__ != null))                                                  \
     local_rsrc_name__ = local_rsrc__.get_name();                               \
   local_op_type__ = __local_op__.get_op_type();                                \
   case (local_op_type__)                                                       \
     UVM_PRINT: begin                                                           \
       $cast(__local_printer__, __local_op__.get_policy());                     \
     end                                                                        \
     UVM_COMPARE: begin                                                         \
       if (local_rhs__ == null) return;                                         \
       $cast(__local_comparer__, __local_op__.get_policy());                    \
     end                                                                        \
     UVM_RECORD: begin                                                          \
       $cast(__local_recorder__, __local_op__.get_policy());                    \
     end                                                                        \
     UVM_PACK, UVM_UNPACK: begin                                                \
       $cast(__local_packer__, __local_op__.get_policy());                      \
     end                                                                        \
     UVM_COPY: begin                                                            \
       if (local_rhs__ == null) return;                                         \
       $cast(__local_copier__, __local_op__.get_policy());                      \
     end                                                                        \
     UVM_SET: begin                                                             \
       if (local_rsrc__ == null) return;                                        \
     end                                                                        \
     UVM_CHECK_FIELDS: begin                                                    \
       $cast(__local_field_names__, __local_op__.get_rhs());                    \
     end                                                                        \
     default:                                                                   \
       return; /* unknown op, just return */                                    \
   endcase                                                                      \

`define uvm_field_utils_end \
endfunction : __m_uvm_execute_field_op
`define uvm_object_utils(T) \
  `m_uvm_object_registry_internal(T,T)  \
  `m_uvm_object_create_func(T) \
  `uvm_type_name_decl(`"T`")
`define uvm_object_param_utils(T) \
  `m_uvm_object_registry_param(T)  \
  `m_uvm_object_create_func(T)
`define uvm_object_utils_begin(T) \
  `uvm_object_utils(T) \
  `uvm_field_utils_begin(T)
`define uvm_object_param_utils_begin(T) \
  `uvm_object_param_utils(T) \
  `uvm_field_utils_begin(T)
`define uvm_object_abstract_utils(T) \
  `m_uvm_object_abstract_registry_internal(T,T)  \
  `uvm_type_name_decl(`"T`")
`define uvm_object_abstract_param_utils(T) \
  `m_uvm_object_abstract_registry_param(T)
`define uvm_object_abstract_utils_begin(T) \
  `uvm_object_abstract_utils(T) \
  `uvm_field_utils_begin(T)
`define uvm_object_abstract_param_utils_begin(T) \
  `uvm_object_abstract_param_utils(T) \
  `uvm_field_utils_begin(T)
`define uvm_object_utils_end \
  `uvm_field_utils_end
`define uvm_component_utils(T) \
   `m_uvm_component_registry_internal(T,T) \
   `uvm_type_name_decl(`"T`") \

`define uvm_component_param_utils(T) \
   `m_uvm_component_registry_param(T) \

`define uvm_component_utils_begin(T) \
   `uvm_component_utils(T) \
   `uvm_field_utils_begin(T)
`define uvm_component_param_utils_begin(T) \
   `uvm_component_param_utils(T) \
   `uvm_field_utils_begin(T)
`define uvm_component_abstract_utils(T) \
   `m_uvm_component_abstract_registry_internal(T,T) \
   `uvm_type_name_decl(`"T`") \

`define uvm_component_abstract_param_utils(T) \
   `m_uvm_component_abstract_registry_param(T) \

`define uvm_component_abstract_utils_begin(T) \
   `uvm_component_abstract_utils(T) \
   `uvm_field_utils_begin(T)
`define uvm_component_abstract_param_utils_begin(T) \
   `uvm_component_abstract_param_utils(T) \
   `uvm_field_utils_begin(T)
`define uvm_component_utils_end \
  `uvm_field_utils_end
`define uvm_object_registry(T,S) \
   typedef uvm_object_registry#(T,S) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define uvm_component_registry(T,S) \
   typedef uvm_component_registry #(T,S) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define uvm_declare_type_alias(TYPE,NAME,SFX=) \
  static bit m__alias_declared``SFX = TYPE::type_id::set_type_alias(NAME);
`define uvm_new_func \
  function new (string name, uvm_component parent); \
    super.new(name, parent); \
  endfunction
`define m_uvm_object_create_func(T) \
   function uvm_object create (string name=""); \
     T tmp; \
     if (name=="") tmp = new(); \
     else tmp = new(name); \
     return tmp; \
   endfunction
`define uvm_type_name_decl(TNAME_STRING) \
     static function string type_name(); \
       return TNAME_STRING; \
     endfunction : type_name \
     virtual function string get_type_name(); \
       return TNAME_STRING; \
     endfunction : get_type_name
`define m_uvm_object_registry_internal(T,S) \
   typedef uvm_object_registry#(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_object_registry_param(T) \
   typedef uvm_object_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_object_abstract_registry_internal(T,S) \
   typedef uvm_abstract_object_registry#(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_object_abstract_registry_param(T) \
   typedef uvm_abstract_object_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_component_registry_internal(T,S) \
   typedef uvm_component_registry #(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_component_registry_param(T) \
   typedef uvm_component_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_component_abstract_registry_internal(T,S) \
   typedef uvm_abstract_component_registry #(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_component_abstract_registry_param(T) \
   typedef uvm_abstract_component_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`define m_uvm_field_radix(FLAG) uvm_radix_enum'((FLAG)&(UVM_RADIX))
`define m_uvm_field_recursion(FLAG) uvm_recursion_policy_enum'((FLAG)&(UVM_RECURSION))
`define m_warn_if_no_positive_ops(ARG,FLAG) \
  begin \
    static bit dont_warn_if_no_positive_ops ; \
    if (!dont_warn_if_no_positive_ops && !((FLAG)&UVM_FLAGS_ON) && ((FLAG)&(~(UVM_COPY|UVM_COMPARE|UVM_PRINT|UVM_RECORD|UVM_PACK|UVM_UNPACK)))) begin \
      string behavior; \
      `ifdef UVM_LEGACY_FIELD_MACRO_SEMANTICS behavior = "As UVM_LEGACY_FIELD_MACRO_SEMANTICS is set, we will treat this as if UVM_ALL_ON had been bitwise-or'd with FLAG.  This is not the behavior specified by IEEE 1800.2-2020."; \
      `else behavior = "Previous Accellera UVM libraries treated this as if UVM_ALL_ON had been bitwise-or'd with this FLAG, but per IEEE 1800.2-2020, we will treat it as a NO-OP (see UVM Mantis 7187)"; \
      `endif \
      `uvm_warning("UVM/FIELDS/NO_FLAG",{"Field macro for ARG uses FLAG without or'ing any explicit UVM_xxx actions. ",behavior}) \
      dont_warn_if_no_positive_ops = 1; \
    end \
  end
`define m_uvm_field_begin(ARG, FLAG, REGEX="") \
  `m_warn_if_no_positive_ops(ARG,FLAG) \
  begin \
    case (local_op_type__) \
      UVM_CHECK_FIELDS: \
        if ( \
           `ifndef UVM_LEGACY_FIELD_MACRO_SEMANTICS (((FLAG)&UVM_SET)) && `endif \
           (!((FLAG)&UVM_NOSET)) \
           ) begin \
          __local_field_names__.push_back('{`"ARG`", REGEX}); \
        end
`define m_uvm_field_end(ARG) \
    endcase \
  end
`define m_uvm_field_op_begin(OP, FLAG) \
UVM_``OP: \
  if ( \
     `ifndef UVM_LEGACY_FIELD_MACRO_SEMANTICS (((FLAG)&UVM_``OP)) && `endif \
     (!((FLAG)&UVM_NO``OP)) \
  ) begin
`define m_uvm_field_op_end(OP) \
  end
`define m_uvm_compat_physical_abstract(FLAG) \
     if ((__local_comparer__.physical&&((FLAG)&UVM_PHYSICAL)) || \
         (__local_comparer__.abstract&&((FLAG)&UVM_ABSTRACT)) || \
         (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT)) )
`define uvm_field_int(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_int(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_int(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_int(`"ARG`", \
                      ARG, \
                      $bits(ARG), \
                      `m_uvm_field_radix(FLAG), \
                      __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_int(ARG, $bits(ARG), `m_uvm_field_radix(FLAG),,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       ARG, \
                                       this) \
        /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_object(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      `uvm_copy_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_copier__) \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_pack_object(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_unpack_object(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_object(ARG, `m_uvm_field_recursion(FLAG), __local_recorder__); \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_object(ARG, `m_uvm_field_recursion(FLAG),__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_read(local_success__, \
                           local_rsrc__, \
                           uvm_object, \
                           local_obj__, \
                           this) \
        if (local_success__) begin \
          if (local_obj__ == null) begin \
            ARG = null; \
          end else if (!$cast(ARG, local_obj__) && uvm_config_db_options::is_tracing()) begin \
             `uvm_info("CFGDB/OBJ_TYPE", $sformatf("Can't set field '%s' on '%s' with '%s' type", \
                                                           `"ARG`", \
                                                           this.get_full_name(), \
                                                           local_obj__.get_type_name()),UVM_LOW) \
          end \
          /* TODO if(local_success__ && printing matches) */ \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_string(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_string(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_string(`"ARG`", ARG, __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      __local_printer__.print_string(`"ARG`", ARG); \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_read(local_success__, \
                           local_rsrc__, \
                           string, \
                           ARG, \
                           this) \
              /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_enum(T,ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_enum(ARG, local_rhs__.ARG, T, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_enum(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_enum(ARG, T, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_enum(`"ARG`", ARG, T, __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      if (`m_uvm_field_radix(FLAG) inside {UVM_NORADIX, UVM_ENUM, UVM_STRING}) \
        `uvm_print_enum(T, ARG,__local_printer__) \
      else \
        `uvm_print_int(ARG, $bits(ARG), `m_uvm_field_radix(FLAG),T,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_resource_enum_read(local_success__, \
                                 local_rsrc__, \
                                 T, \
                                 ARG, \
                                 this) \
              /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_real(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_real(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_real(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_real(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_real(`"ARG`", ARG, __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      __local_printer__.print_real(`"ARG`", ARG); \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_resource_real_read(local_success__, \
                                 local_rsrc__, \
                                 ARG, \
                                 this) \
              /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_event(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compare_begin(ARG, local_rhs__.ARG, __local_comparer__) \
        __local_comparer__.print_msg({`"ARG`", " event miscompare"}); \
      `m_uvm_compare_end \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      __local_printer__.print_generic(`"ARG`", "event", -1, ""); \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_sarray_int(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_sarray_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_sarray(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_sarray(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_int(ARG, `m_uvm_field_radix(FLAG), __local_recorder__)  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_int(ARG, \
                            `m_uvm_field_radix(FLAG),, \
                            __local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_builtin_int_read(local_success__, \
                                             local_rsrc__, \
                                             ARG[local_index__], \
                                             this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_sarray_object(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG, `"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      foreach(ARG[i]) begin \
        `uvm_copy_object(ARG[i], local_rhs__.ARG[i], `m_uvm_field_recursion(FLAG), __local_copier__) \
      end \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_sarray_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        foreach(ARG[i])  \
          `uvm_pack_object(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        foreach(ARG[i])  \
          `uvm_unpack_object(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_object(ARG, `m_uvm_field_recursion(FLAG), __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_object(ARG, `m_uvm_field_recursion(FLAG), __local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 uvm_object, \
                                 local_obj__, \
                                 this) \
              if (local_success__) begin \
                if (local_obj__ == null) begin \
                  ARG[local_index__] = null; \
                end else if (!$cast(ARG[local_index__], local_obj__) && uvm_config_db_options::is_tracing()) begin \
                  `uvm_info("CFGDB/OBJ_TYPE", $sformatf("Can't set field '%s[%d]' on '%s' with '%s' type", \
                                                                `"ARG`", \
                                                                local_index__, \
                                                                this.get_full_name(), \
                                                                local_obj__.get_type_name()),UVM_LOW) \
                end \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_sarray_string(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_sarray_string(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      foreach(ARG[i]) \
        `uvm_pack_string(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      foreach(ARG[i]) \
       `uvm_unpack_string(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_string(ARG, __local_recorder__)  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_string(ARG,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 string, \
                                 ARG[local_index__], \
                                 this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_sarray_enum(T,ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_sarray_enum(ARG, local_rhs__.ARG, T, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      foreach (ARG[i]) \
        `uvm_pack_enumN(ARG[i], $bits(T), __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      foreach (ARG[i]) \
        `uvm_unpack_enumN(ARG[i], $bits(T), T, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_enum(ARG, T, __local_recorder__)  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_enum(T, ARG ,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_enum_read(local_success__, \
                                      local_rsrc__, \
                                      T, \
                                      ARG[local_index__], \
                                      this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define m_uvm_queue_resize(ARG, SZ) \
  if (ARG.size() > SZ) \
    ARG  = ARG[0:SZ-1]; \
  else \
    while (ARG.size() < SZ) ARG.push_back(ARG[SZ]);
`define m_uvm_da_resize(ARG, SZ) \
  if (ARG.size() != SZ) ARG = new[SZ](ARG);
`define m_uvm_field_qda_int(TYPE,ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_qda_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_``TYPE``(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_``TYPE``(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_int(ARG, `m_uvm_field_radix(FLAG), __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_int(TYPE, ARG, `m_uvm_field_radix(FLAG),,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              bit tmp_stream__[]; \
              `uvm_resource_builtin_int_read(local_success__, \
                                             local_rsrc__, \
                                             { << bit { tmp_stream__ }}, \
                                             this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                tmp_stream__ = new[$bits(ARG[local_index__])] (tmp_stream__); \
                ARG[local_index__] = { << bit { tmp_stream__ }}; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_array_int(ARG,FLAG=UVM_DEFAULT) \
   `m_uvm_field_qda_int(da,ARG,FLAG)
`define m_uvm_field_qda_object(TYPE,ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      if ((`m_uvm_field_recursion(FLAG) == UVM_REFERENCE) || !local_rhs__.ARG.size()) \
        ARG = local_rhs__.ARG; \
      else begin \
        `m_uvm_``TYPE``_resize(ARG, local_rhs__.ARG.size()) \
        foreach (ARG[i]) \
          `uvm_copy_object(ARG[i], local_rhs__.ARG[i], `m_uvm_field_recursion(FLAG), __local_copier__) \
      end \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_qda_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      __local_packer__.pack_field_int(ARG.size(), 32); \
      foreach (ARG[i]) \
        `uvm_pack_object(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      local_size__ = __local_packer__.unpack_field_int(32); \
      `m_uvm_``TYPE``_resize(ARG, local_size__); \
      foreach (ARG[i]) \
        `uvm_unpack_object(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_object(ARG, `m_uvm_field_recursion(FLAG), __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_object(TYPE, ARG, `m_uvm_field_recursion(FLAG),__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 uvm_object, \
                                 local_obj__, \
                                 this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                if (local_obj__ == null) begin \
                  ARG[local_index__] = null; \
                end else if (!$cast(ARG[local_index__], local_obj__) && uvm_config_db_options::is_tracing()) begin \
                  `uvm_info("CFGDB/QDA_OBJ_TYPE", \
                             $sformatf("Can't set field '%s[%0d]' on '%s' with '%s' type", \
                                       `"ARG`", \
                                       local_index__, \
                                       this.get_full_name(), \
                                       local_obj__.get_type_name()),UVM_LOW) \
                end \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_array_object(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_qda_object(da,ARG,FLAG)
`define uvm_field_array_string(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_qda_string(da,ARG,FLAG)
`define m_uvm_field_qda_string(TYPE,ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_qda_string(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
       __local_packer__.pack_field_int(ARG.size(), 32); \
       foreach (ARG[i]) \
         `uvm_pack_string(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      local_size__ = __local_packer__.unpack_field_int(32); \
      `m_uvm_``TYPE``_resize(ARG, local_size__) \
      foreach (ARG[i]) \
        `uvm_unpack_string(ARG[i], __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_string(ARG, __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_string(TYPE, ARG,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                           local_index__, \
                                                           get_full_name(), \
                                                           `"ARG`", \
                                                           ARG.size() ) ) \
            end \
            else begin \
              string tmp_string__; \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 string, \
                                 tmp_string__, \
                                 this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                ARG[local_index__]  = tmp_string__; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_array_enum(T,ARG,FLAG=UVM_DEFAULT) \
  `m_field_qda_enum(da,T,ARG,FLAG)
`define m_field_qda_enum(TYPE,T,ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compat_physical_abstract(FLAG) \
      `uvm_compare_qda_enum(ARG, local_rhs__.ARG, T, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
       __local_packer__.pack_field_int(ARG.size(), 32); \
       foreach (ARG[i]) \
         `uvm_pack_enumN(ARG[i], $bits(T), __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      local_size__ = __local_packer__.unpack_field_int(32); \
      `m_uvm_``TYPE``_resize(ARG, local_size__) \
      foreach (ARG[i]) \
        `uvm_unpack_enumN(ARG[i], $bits(T), T, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_enum(ARG, T, __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_enum(TYPE, T, ARG,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              T tmp_enum__; \
              `uvm_resource_enum_read(local_success__, \
                                      local_rsrc__, \
                                      T, \
                                      tmp_enum__, \
                                      this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                ARG[local_index__] = tmp_enum__; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_queue_int(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_qda_int(queue,ARG,FLAG)
`define uvm_field_queue_object(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_qda_object(queue,ARG,FLAG)
`define uvm_field_queue_string(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_qda_string(queue,ARG,FLAG)
`define uvm_field_queue_enum(T,ARG,FLAG=UVM_DEFAULT) \
  `m_field_qda_enum(queue,T,ARG,FLAG)
`define uvm_field_aa_int_string(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_int_string(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_int_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_int_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_int_string(ARG, `m_uvm_field_radix(FLAG), int, __local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index__ = local_rsrc_name__.substr(local_name__.len(), \
                                                          local_rsrc_name__.len()-2); \
          `uvm_resource_builtin_int_read(local_success__, \
                                         local_rsrc__, \
                                         ARG[local_index__], \
                                         this) \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_aa_object_string(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      `uvm_copy_aa_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_copier__) \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_object_string(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_pack_aa_object_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
      `uvm_unpack_aa_object_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_object_string(ARG, `m_uvm_field_recursion(FLAG),__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index__ = local_rsrc_name__.substr(local_name__.len(), \
                                                          local_rsrc_name__.len()-2); \
          `uvm_resource_read(local_success__, \
                             local_rsrc__, \
                             uvm_object, \
                             local_obj__, \
                             this) \
          if (local_success__) begin \
            if (local_obj__ == null) begin \
              ARG[local_index__] = null; \
            end else if (!$cast(ARG[local_index__], local_obj__) && uvm_config_db_options::is_tracing()) begin \
              `uvm_info("CFGDB/OBJ_TYPE", $sformatf("Can't set field '%s[%s]' on '%s' with '%s' type", \
                                                            `"ARG`", \
                                                            local_index__, \
                                                            this.get_full_name(), \
                                                            local_obj__.get_type_name()),UVM_LOW) \
            end \
          end \
          /* TODO if(local_success__ && printing matches) */ \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_aa_string_string(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG,`"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_string_string(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_string_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_string_string(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_string_string(ARG,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index__ = local_rsrc_name__.substr(local_name__.len(), \
                                                          local_rsrc_name__.len()-2); \
          `uvm_resource_read(local_success__, \
                             local_rsrc__, \
                             string, \
                             ARG[local_index__], \
                             this) \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_aa_object_int(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_object_key(int, ARG, FLAG)
`define uvm_field_aa_object_key(KEY, ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG, `"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      `uvm_copy_aa_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_copier__) \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_object_int(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_pack_aa_object_intN(ARG, $bits(KEY), __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_unpack_aa_object_intN(ARG, $bits(KEY), __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_object_int(ARG, `m_uvm_field_recursion(FLAG), KEY,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          KEY local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            `uvm_resource_read(local_success__, \
                               local_rsrc__, \
                               uvm_object, \
                               local_obj__, \
                               this) \
            if (local_success__) begin \
              if (local_obj__ == null) begin \
                ARG[local_index__] = null; \
              end else if (!$cast(ARG[local_index__], local_obj__) && uvm_config_db_options::is_tracing()) begin \
                `uvm_info("CFGDB/OBJ_TYPE", $sformatf("Can't set field '%s[%d]' on '%s' with '%s' type", \
                                                              `"ARG`", \
                                                              local_index__, \
                                                              this.get_full_name(), \
                                                              local_obj__.get_type_name()),UVM_LOW) \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_aa_string_int(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_string_key(int, ARG, FLAG)
`define uvm_field_aa_string_key(KEY, ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG, `"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_string_int(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_string_intN(ARG, $bits(KEY), __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_string_intN(ARG, $bits(KEY), __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      /* TODO */ \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          KEY local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            `uvm_resource_read(local_success__, \
                               local_rsrc__, \
                               string, \
                               ARG[local_index__], \
                               this) \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_aa_int_int(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(int, ARG, FLAG) \

`define uvm_field_aa_int_int_unsigned(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(int unsigned, ARG, FLAG)
`define uvm_field_aa_int_integer(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(integer, ARG, FLAG)
`define uvm_field_aa_int_integer_unsigned(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(integer unsigned, ARG, FLAG)
`define uvm_field_aa_int_byte(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(byte, ARG, FLAG)
`define uvm_field_aa_int_byte_unsigned(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(byte unsigned, ARG, FLAG)
`define uvm_field_aa_int_shortint(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(shortint, ARG, FLAG)
`define uvm_field_aa_int_shortint_unsigned(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(shortint unsigned, ARG, FLAG)
`define uvm_field_aa_int_longint(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(longint, ARG, FLAG)
`define uvm_field_aa_int_longint_unsigned(ARG,FLAG=UVM_DEFAULT) \
  `uvm_field_aa_int_key(longint unsigned, ARG, FLAG)
`define uvm_field_aa_int_key(KEY, ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG, `"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_int_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_int_intN(ARG, $bits(KEY), __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_int_intN(ARG, $bits(KEY), __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_int_int(ARG, `m_uvm_field_radix(FLAG), , KEY,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          KEY local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            `uvm_resource_int_read(local_success__, \
                                   local_rsrc__, \
                                   KEY, \
                                   ARG[local_index__], \
                                   this) \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_aa_int_enumkey(KEY, ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG, FLAG, `"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_int_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG), __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_int_enum(ARG, KEY, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_int_enum(ARG, KEY, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_int_enum(KEY, ARG, `m_uvm_field_radix(FLAG),,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          KEY local_index__; \
          bit[$bits(KEY)-1:0] local_bit_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_bit_index__); \
          if (local_code__ > 0) begin \
            local_index__ = KEY'(local_bit_index__); \
            `uvm_resource_int_read(local_success__, \
                                   local_rsrc__, \
                                   KEY, \
                                   ARG[local_index__], \
                                   this) \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_sarray_real(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG, `"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_sarray_real(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_sarray_real(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_sarray_real(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_real(ARG, __local_recorder__)  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_real(ARG,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.", get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_real_read(local_success__, \
                                      local_rsrc__, \
                                      ARG[local_index__], \
                                      this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define m_uvm_field_qda_real(TYPE,ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_begin(ARG,FLAG, `"ARG[+]`") \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_qda_real(ARG, local_rhs__.ARG, __local_comparer__) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_``TYPE``_real(ARG, __local_packer__) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_``TYPE``_real(ARG, __local_packer__) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_real(ARG, __local_recorder__) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_real(TYPE, ARG,__local_printer__) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_real_read(local_success__, \
                                local_rsrc__, \
                                local_size__, \
                                this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-2); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              real tmp_real__; \
              `uvm_resource_real_read(local_success__, \
                                      local_rsrc__, \
                                      tmp_real__, \
                                      this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                ARG[local_index__] = tmp_real__; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)
`define uvm_field_array_real(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_qda_real(da,ARG,FLAG)
`define uvm_field_queue_real(ARG,FLAG=UVM_DEFAULT) \
  `m_uvm_field_qda_real(queue,ARG,FLAG)
`define uvm_blocking_put_imp_decl(SFX) \
class uvm_blocking_put_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_BLOCKING_PUT_MASK,`"uvm_blocking_put_imp``SFX`",IMP) \
  `UVM_BLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_nonblocking_put_imp_decl(SFX) \
class uvm_nonblocking_put_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_NONBLOCKING_PUT_MASK,`"uvm_nonblocking_put_imp``SFX`",IMP) \
  `UVM_NONBLOCKING_PUT_IMP_SFX( SFX, m_imp, T, t) \
endclass
`define uvm_put_imp_decl(SFX) \
class uvm_put_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_PUT_MASK,`"uvm_put_imp``SFX`",IMP) \
  `UVM_BLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_NONBLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_blocking_get_imp_decl(SFX) \
class uvm_blocking_get_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_BLOCKING_GET_MASK,`"uvm_blocking_get_imp``SFX`",IMP) \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_nonblocking_get_imp_decl(SFX) \
class uvm_nonblocking_get_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_NONBLOCKING_GET_MASK,`"uvm_nonblocking_get_imp``SFX`",IMP) \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_get_imp_decl(SFX) \
class uvm_get_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_GET_MASK,`"uvm_get_imp``SFX`",IMP) \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_blocking_peek_imp_decl(SFX) \
class uvm_blocking_peek_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_BLOCKING_PEEK_MASK,`"uvm_blocking_peek_imp``SFX`",IMP) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_nonblocking_peek_imp_decl(SFX) \
class uvm_nonblocking_peek_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_NONBLOCKING_PEEK_MASK,`"uvm_nonblocking_peek_imp``SFX`",IMP) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_peek_imp_decl(SFX) \
class uvm_peek_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_PEEK_MASK,`"uvm_peek_imp``SFX`",IMP) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_blocking_get_peek_imp_decl(SFX) \
class uvm_blocking_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_BLOCKING_GET_PEEK_MASK,`"uvm_blocking_get_peek_imp``SFX`",IMP) \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_nonblocking_get_peek_imp_decl(SFX) \
class uvm_nonblocking_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_NONBLOCKING_GET_PEEK_MASK,`"uvm_nonblocking_get_peek_imp``SFX`",IMP) \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_get_peek_imp_decl(SFX) \
class uvm_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_GET_PEEK_MASK,`"uvm_get_peek_imp``SFX`",IMP) \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass
`define uvm_blocking_master_imp_decl(SFX) \
class uvm_blocking_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                     type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends uvm_port_base #(uvm_tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `UVM_MS_IMP_COMMON(`UVM_TLM_BLOCKING_MASTER_MASK,`"uvm_blocking_master_imp``SFX`") \
  \
  `UVM_BLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) \
  \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  \
endclass
`define uvm_nonblocking_master_imp_decl(SFX) \
class uvm_nonblocking_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                   type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends uvm_port_base #(uvm_tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `UVM_MS_IMP_COMMON(`UVM_TLM_NONBLOCKING_MASTER_MASK,`"uvm_nonblocking_master_imp``SFX`") \
  \
  `UVM_NONBLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) \
  \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  \
endclass
`define uvm_master_imp_decl(SFX) \
class uvm_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                            type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends uvm_port_base #(uvm_tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `UVM_MS_IMP_COMMON(`UVM_TLM_MASTER_MASK,`"uvm_master_imp``SFX`") \
  \
  `UVM_BLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) \
  `UVM_NONBLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) \
  \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  \
endclass
`define uvm_blocking_slave_imp_decl(SFX) \
class uvm_blocking_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                    type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends uvm_port_base #(uvm_tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `UVM_MS_IMP_COMMON(`UVM_TLM_BLOCKING_SLAVE_MASK,`"uvm_blocking_slave_imp``SFX`") \
  \
  `UVM_BLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) \
  \
endclass
`define uvm_nonblocking_slave_imp_decl(SFX) \
class uvm_nonblocking_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                       type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends uvm_port_base #(uvm_tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `UVM_MS_IMP_COMMON(`UVM_TLM_NONBLOCKING_SLAVE_MASK,`"uvm_nonblocking_slave_imp``SFX`") \
  \
  `UVM_NONBLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) \
  \
endclass
`define uvm_slave_imp_decl(SFX) \
class uvm_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                           type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends uvm_port_base #(uvm_tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `UVM_MS_IMP_COMMON(`UVM_TLM_SLAVE_MASK,`"uvm_slave_imp``SFX`") \
  \
  `UVM_BLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  `UVM_NONBLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) \
  \
  `UVM_BLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) \
  `UVM_BLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) \
  `UVM_NONBLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) \
  `UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) \
  \
endclass
`define uvm_blocking_transport_imp_decl(SFX) \
class uvm_blocking_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(REQ, RSP)); \
  `UVM_IMP_COMMON(`UVM_TLM_BLOCKING_TRANSPORT_MASK,`"uvm_blocking_transport_imp``SFX`",IMP) \
  `UVM_BLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass
`define uvm_nonblocking_transport_imp_decl(SFX) \
class uvm_nonblocking_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(REQ, RSP)); \
  `UVM_IMP_COMMON(`UVM_TLM_NONBLOCKING_TRANSPORT_MASK,`"uvm_nonblocking_transport_imp``SFX`",IMP) \
  `UVM_NONBLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass
`define uvm_non_blocking_transport_imp_decl(SFX) \
  `uvm_nonblocking_transport_imp_decl(SFX)
`define uvm_transport_imp_decl(SFX) \
class uvm_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(REQ, RSP)); \
  `UVM_IMP_COMMON(`UVM_TLM_TRANSPORT_MASK,`"uvm_transport_imp``SFX`",IMP) \
  `UVM_BLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
  `UVM_NONBLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass
`define uvm_analysis_imp_decl(SFX) \
class uvm_analysis_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  `UVM_IMP_COMMON(`UVM_TLM_ANALYSIS_MASK,`"uvm_analysis_imp``SFX`",IMP) \
  function void write( input T t); \
    m_imp.write``SFX( t); \
  endfunction \
  \
endclass
`define UVM_BLOCKING_PUT_IMP_SFX(SFX, imp, TYPE, arg) \
  task put( input TYPE arg); imp.put``SFX( arg); endtask
`define UVM_BLOCKING_GET_IMP_SFX(SFX, imp, TYPE, arg) \
  task get( output TYPE arg); imp.get``SFX( arg); endtask
`define UVM_BLOCKING_PEEK_IMP_SFX(SFX, imp, TYPE, arg) \
  task peek( output TYPE arg);imp.peek``SFX( arg); endtask
`define UVM_NONBLOCKING_PUT_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_put( input TYPE arg); \
    if( !imp.try_put``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_put(); return imp.can_put``SFX(); endfunction
`define UVM_NONBLOCKING_GET_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_get( output TYPE arg); \
    if( !imp.try_get``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_get(); return imp.can_get``SFX(); endfunction
`define UVM_NONBLOCKING_PEEK_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_peek( output TYPE arg); \
    if( !imp.try_peek``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_peek(); return imp.can_peek``SFX(); endfunction
`define UVM_BLOCKING_TRANSPORT_IMP_SFX(SFX, imp, REQ, RSP, req_arg, rsp_arg) \
  task transport( input REQ req_arg, output RSP rsp_arg); \
    imp.transport``SFX(req_arg, rsp_arg); \
  endtask
`define UVM_NONBLOCKING_TRANSPORT_IMP_SFX(SFX, imp, REQ, RSP, req_arg, rsp_arg) \
  function bit nb_transport( input REQ req_arg, output RSP rsp_arg); \
    if(imp) return imp.nb_transport``SFX(req_arg, rsp_arg); \
  endfunction
`define UVM_SEQ_ITEM_PULL_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  function void disable_auto_item_recording(); imp.disable_auto_item_recording(); endfunction \
  function bit is_auto_item_recording_enabled(); return imp.is_auto_item_recording_enabled(); endfunction \
  task get_next_item(output REQ req_arg); imp.get_next_item(req_arg); endtask \
  task try_next_item(output REQ req_arg); imp.try_next_item(req_arg); endtask \
  function void item_done(input RSP rsp_arg = null); imp.item_done(rsp_arg); endfunction \
  task wait_for_sequences(); imp.wait_for_sequences(); endtask \
  function bit has_do_available(); return imp.has_do_available(); endfunction \
  function void put_response(input RSP rsp_arg); imp.put_response(rsp_arg); endfunction \
  task get(output REQ req_arg); imp.get(req_arg); endtask \
  task peek(output REQ req_arg); imp.peek(req_arg); endtask \
  task put(input RSP rsp_arg); imp.put(rsp_arg); endtask
`define UVM_TLM_BLOCKING_PUT_MASK (1<<0)
`define UVM_TLM_BLOCKING_GET_MASK (1<<1)
`define UVM_TLM_BLOCKING_PEEK_MASK (1<<2)
`define UVM_TLM_BLOCKING_TRANSPORT_MASK (1<<3)
`define UVM_TLM_NONBLOCKING_PUT_MASK (1<<4)
`define UVM_TLM_NONBLOCKING_GET_MASK (1<<5)
`define UVM_TLM_NONBLOCKING_PEEK_MASK (1<<6)
`define UVM_TLM_NONBLOCKING_TRANSPORT_MASK (1<<7)
`define UVM_TLM_ANALYSIS_MASK (1<<8)
`define UVM_TLM_MASTER_BIT_MASK (1<<9)
`define UVM_TLM_SLAVE_BIT_MASK (1<<10)
`define UVM_TLM_PUT_MASK (`UVM_TLM_BLOCKING_PUT_MASK    | `UVM_TLM_NONBLOCKING_PUT_MASK)
`define UVM_TLM_GET_MASK (`UVM_TLM_BLOCKING_GET_MASK    | `UVM_TLM_NONBLOCKING_GET_MASK)
`define UVM_TLM_PEEK_MASK (`UVM_TLM_BLOCKING_PEEK_MASK   | `UVM_TLM_NONBLOCKING_PEEK_MASK)
`define UVM_TLM_BLOCKING_GET_PEEK_MASK (`UVM_TLM_BLOCKING_GET_MASK    | `UVM_TLM_BLOCKING_PEEK_MASK)
`define UVM_TLM_BLOCKING_MASTER_MASK (`UVM_TLM_BLOCKING_PUT_MASK       | `UVM_TLM_BLOCKING_GET_MASK | `UVM_TLM_BLOCKING_PEEK_MASK | `UVM_TLM_MASTER_BIT_MASK)
`define UVM_TLM_BLOCKING_SLAVE_MASK (`UVM_TLM_BLOCKING_PUT_MASK       | `UVM_TLM_BLOCKING_GET_MASK | `UVM_TLM_BLOCKING_PEEK_MASK | `UVM_TLM_SLAVE_BIT_MASK)
`define UVM_TLM_NONBLOCKING_GET_PEEK_MASK (`UVM_TLM_NONBLOCKING_GET_MASK | `UVM_TLM_NONBLOCKING_PEEK_MASK)
`define UVM_TLM_NONBLOCKING_MASTER_MASK (`UVM_TLM_NONBLOCKING_PUT_MASK    | `UVM_TLM_NONBLOCKING_GET_MASK | `UVM_TLM_NONBLOCKING_PEEK_MASK | `UVM_TLM_MASTER_BIT_MASK)
`define UVM_TLM_NONBLOCKING_SLAVE_MASK (`UVM_TLM_NONBLOCKING_PUT_MASK    | `UVM_TLM_NONBLOCKING_GET_MASK | `UVM_TLM_NONBLOCKING_PEEK_MASK | `UVM_TLM_SLAVE_BIT_MASK)
`define UVM_TLM_GET_PEEK_MASK (`UVM_TLM_GET_MASK | `UVM_TLM_PEEK_MASK)
`define UVM_TLM_MASTER_MASK (`UVM_TLM_BLOCKING_MASTER_MASK    | `UVM_TLM_NONBLOCKING_MASTER_MASK)
`define UVM_TLM_SLAVE_MASK (`UVM_TLM_BLOCKING_SLAVE_MASK    | `UVM_TLM_NONBLOCKING_SLAVE_MASK)
`define UVM_TLM_TRANSPORT_MASK (`UVM_TLM_BLOCKING_TRANSPORT_MASK | `UVM_TLM_NONBLOCKING_TRANSPORT_MASK)
`define UVM_SEQ_ITEM_GET_NEXT_ITEM_MASK (1<<0)
`define UVM_SEQ_ITEM_TRY_NEXT_ITEM_MASK (1<<1)
`define UVM_SEQ_ITEM_ITEM_DONE_MASK (1<<2)
`define UVM_SEQ_ITEM_HAS_DO_AVAILABLE_MASK (1<<3)
`define UVM_SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK (1<<4)
`define UVM_SEQ_ITEM_PUT_RESPONSE_MASK (1<<5)
`define UVM_SEQ_ITEM_PUT_MASK (1<<6)
`define UVM_SEQ_ITEM_GET_MASK (1<<7)
`define UVM_SEQ_ITEM_PEEK_MASK (1<<8)
`define UVM_SEQ_ITEM_PULL_MASK (`UVM_SEQ_ITEM_GET_NEXT_ITEM_MASK | `UVM_SEQ_ITEM_TRY_NEXT_ITEM_MASK | \
                        `UVM_SEQ_ITEM_ITEM_DONE_MASK | `UVM_SEQ_ITEM_HAS_DO_AVAILABLE_MASK |  \
                        `UVM_SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK | `UVM_SEQ_ITEM_PUT_RESPONSE_MASK | \
                        `UVM_SEQ_ITEM_PUT_MASK | `UVM_SEQ_ITEM_GET_MASK | `UVM_SEQ_ITEM_PEEK_MASK)
`define UVM_SEQ_ITEM_UNI_PULL_MASK (`UVM_SEQ_ITEM_GET_NEXT_ITEM_MASK | `UVM_SEQ_ITEM_TRY_NEXT_ITEM_MASK | \
                           `UVM_SEQ_ITEM_ITEM_DONE_MASK | `UVM_SEQ_ITEM_HAS_DO_AVAILABLE_MASK | \
                           `UVM_SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK | `UVM_SEQ_ITEM_GET_MASK | \
                           `UVM_SEQ_ITEM_PEEK_MASK)
`define UVM_SEQ_ITEM_PUSH_MASK (`UVM_SEQ_ITEM_PUT_MASK)
`define UVM_TLM_IMPS_SVH
`define UVM_BLOCKING_PUT_IMP(imp, TYPE, arg) \
  task put (TYPE arg); \
    imp.put(arg); \
  endtask
`define UVM_NONBLOCKING_PUT_IMP(imp, TYPE, arg) \
  function bit try_put (TYPE arg); \
    return imp.try_put(arg); \
  endfunction \
  function bit can_put(); \
    return imp.can_put(); \
  endfunction
`define UVM_BLOCKING_GET_IMP(imp, TYPE, arg) \
  task get (output TYPE arg); \
    imp.get(arg); \
  endtask
`define UVM_NONBLOCKING_GET_IMP(imp, TYPE, arg) \
  function bit try_get (output TYPE arg); \
    return imp.try_get(arg); \
  endfunction \
  function bit can_get(); \
    return imp.can_get(); \
  endfunction
`define UVM_BLOCKING_PEEK_IMP(imp, TYPE, arg) \
  task peek (output TYPE arg); \
    imp.peek(arg); \
  endtask
`define UVM_NONBLOCKING_PEEK_IMP(imp, TYPE, arg) \
  function bit try_peek (output TYPE arg); \
    return imp.try_peek(arg); \
  endfunction \
  function bit can_peek(); \
    return imp.can_peek(); \
  endfunction
`define UVM_BLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  task transport (REQ req_arg, output RSP rsp_arg); \
    imp.transport(req_arg, rsp_arg); \
  endtask
`define UVM_NONBLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  function bit nb_transport (REQ req_arg, output RSP rsp_arg); \
    return imp.nb_transport(req_arg, rsp_arg); \
  endfunction
`define UVM_PUT_IMP(imp, TYPE, arg) \
  `UVM_BLOCKING_PUT_IMP(imp, TYPE, arg) \
  `UVM_NONBLOCKING_PUT_IMP(imp, TYPE, arg)
`define UVM_GET_IMP(imp, TYPE, arg) \
  `UVM_BLOCKING_GET_IMP(imp, TYPE, arg) \
  `UVM_NONBLOCKING_GET_IMP(imp, TYPE, arg)
`define UVM_PEEK_IMP(imp, TYPE, arg) \
  `UVM_BLOCKING_PEEK_IMP(imp, TYPE, arg) \
  `UVM_NONBLOCKING_PEEK_IMP(imp, TYPE, arg)
`define UVM_BLOCKING_GET_PEEK_IMP(imp, TYPE, arg) \
  `UVM_BLOCKING_GET_IMP(imp, TYPE, arg) \
  `UVM_BLOCKING_PEEK_IMP(imp, TYPE, arg)
`define UVM_NONBLOCKING_GET_PEEK_IMP(imp, TYPE, arg) \
  `UVM_NONBLOCKING_GET_IMP(imp, TYPE, arg) \
  `UVM_NONBLOCKING_PEEK_IMP(imp, TYPE, arg)
`define UVM_GET_PEEK_IMP(imp, TYPE, arg) \
  `UVM_BLOCKING_GET_PEEK_IMP(imp, TYPE, arg) \
  `UVM_NONBLOCKING_GET_PEEK_IMP(imp, TYPE, arg)
`define UVM_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  `UVM_BLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  `UVM_NONBLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg)
`define UVM_TLM_GET_TYPE_NAME(NAME) \
  virtual function string get_type_name(); \
    return NAME; \
  endfunction
`define UVM_PORT_COMMON(MASK,TYPE_NAME) \
  function new (string name, uvm_component parent, \
                int min_size=1, int max_size=1); \
    super.new (name, parent, UVM_PORT, min_size, max_size); \
    m_if_mask = MASK; \
  endfunction \
  `UVM_TLM_GET_TYPE_NAME(TYPE_NAME)
`define UVM_SEQ_PORT(MASK,TYPE_NAME) \
  function new (string name, uvm_component parent, \
                int min_size=0, int max_size=1); \
    super.new (name, parent, UVM_PORT, min_size, max_size); \
    m_if_mask = MASK; \
  endfunction \
  `UVM_TLM_GET_TYPE_NAME(TYPE_NAME)
`define UVM_EXPORT_COMMON(MASK,TYPE_NAME) \
  function new (string name, uvm_component parent, \
                int min_size=1, int max_size=1); \
    super.new (name, parent, UVM_EXPORT, min_size, max_size); \
    m_if_mask = MASK; \
  endfunction \
  `UVM_TLM_GET_TYPE_NAME(TYPE_NAME)
`define UVM_IMP_COMMON(MASK,TYPE_NAME,IMP) \
  local IMP m_imp; \
  function new (string name, IMP imp); \
    super.new (name, imp, UVM_IMPLEMENTATION, 1, 1); \
    m_imp = imp; \
    m_if_mask = MASK; \
  endfunction \
  `UVM_TLM_GET_TYPE_NAME(TYPE_NAME)
`define UVM_MS_IMP_COMMON(MASK,TYPE_NAME) \
  local this_req_type m_req_imp; \
  local this_rsp_type m_rsp_imp; \
  function new (string name, this_imp_type imp, \
                this_req_type req_imp = null, this_rsp_type rsp_imp = null); \
    super.new (name, imp, UVM_IMPLEMENTATION, 1, 1); \
    if(req_imp==null) begin \
      $cast(req_imp, imp); \
    end \
    if(rsp_imp==null) begin \
      $cast(rsp_imp, imp); \
    end \
    m_req_imp = req_imp; \
    m_rsp_imp = rsp_imp; \
    m_if_mask = MASK; \
  endfunction  \
  `UVM_TLM_GET_TYPE_NAME(TYPE_NAME)
`define uvm_create(SEQ_OR_ITEM, SEQR=get_sequencer()) \
  begin \
  uvm_object_wrapper w_; \
  w_ = SEQ_OR_ITEM.get_type(); \
  $cast(SEQ_OR_ITEM , create_item(w_, SEQR, `"SEQ_OR_ITEM`"));\
  end
`define uvm_do(SEQ_OR_ITEM, SEQR=get_sequencer(), PRIORITY=-1, CONSTRAINTS={}) \
  begin \
  `uvm_create(SEQ_OR_ITEM, SEQR) \
  `uvm_rand_send(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS) \
  end
`define uvm_send(SEQ_OR_ITEM, PRIORITY=-1) \
  begin \
  uvm_sequence_base __seq; \
  if (!$cast(__seq,SEQ_OR_ITEM)) begin \
     start_item(SEQ_OR_ITEM, PRIORITY);\
     finish_item(SEQ_OR_ITEM, PRIORITY);\
  end \
  else __seq.start(__seq.get_sequencer(), this, PRIORITY, 0);\
  end
`define uvm_rand_send(SEQ_OR_ITEM, PRIORITY=-1, CONSTRAINTS={}) \
  begin \
  uvm_sequence_base __seq; \
  if ( SEQ_OR_ITEM.is_item() ) begin \
    start_item(SEQ_OR_ITEM, PRIORITY);\
    if ( ! SEQ_OR_ITEM.randomize() with CONSTRAINTS ) begin \
      `uvm_warning("RNDFLD", "Randomization failed in uvm_rand_send action") \
    end\
    finish_item(SEQ_OR_ITEM, PRIORITY);\
  end \
  else if ( $cast( __seq, SEQ_OR_ITEM ) ) begin \
    __seq.set_item_context(this,SEQ_OR_ITEM.get_sequencer()); \
    if ( __seq.get_randomize_enabled() ) begin \
      if ( ! SEQ_OR_ITEM.randomize() with CONSTRAINTS ) begin \
        `uvm_warning("RNDFLD", "Randomization failed in uvm_rand_send action") \
      end \
    end \
    __seq.start(__seq.get_sequencer(), this, PRIORITY, 0);\
  end \
  else begin \
    `uvm_warning("NOT_SEQ_OR_ITEM", "Object passed uvm_rand_send appears to be neither a sequence or item." ) \
  end \
  end
`define uvm_add_to_seq_lib(TYPE,LIBTYPE) \
   static bit add_``TYPE``_to_seq_lib_``LIBTYPE =\
      LIBTYPE::m_add_typewide_sequence(TYPE::get_type());
`define uvm_sequence_library_utils(TYPE) \
\
   static protected uvm_object_wrapper m_typewide_sequences[$]; \
   \
   function void init_sequence_library(); \
     foreach (TYPE::m_typewide_sequences[i]) \
       sequences.push_back(TYPE::m_typewide_sequences[i]); \
   endfunction \
   \
   static function void add_typewide_sequence(uvm_object_wrapper seq_type); \
     if (m_static_check(seq_type)) \
       TYPE::m_typewide_sequences.push_back(seq_type); \
   endfunction \
   \
   static function void add_typewide_sequences(uvm_object_wrapper seq_types[$]); \
     foreach (seq_types[i]) \
       TYPE::add_typewide_sequence(seq_types[i]); \
   endfunction \
   \
   static function bit m_add_typewide_sequence(uvm_object_wrapper seq_type); \
     TYPE::add_typewide_sequence(seq_type); \
     return 1; \
   endfunction
`define uvm_declare_p_sequencer(SEQUENCER) \
  SEQUENCER p_sequencer;\
  virtual function void m_set_p_sequencer();\
    super.m_set_p_sequencer(); \
    if( !$cast(p_sequencer, m_sequencer)) \
        `uvm_fatal("DCLPSQ", \
        $sformatf("%m %s Error casting p_sequencer, please verify that this sequence/sequence item is intended to execute on this type of sequencer", get_full_name())) \
  endfunction
`define UVM_CB_MACROS_SVH
`define uvm_register_cb(T,CB) \
  static local bit m_register_cb_``CB = uvm_callbacks#(T,CB)::m_register_pair(`"T`",`"CB`");
`define uvm_set_super_type(T,ST) \
  static local bit m_register_``T``ST = uvm_derived_callbacks#(T,ST)::register_super_type(`"T`",`"ST`");
`define uvm_do_callbacks(T,CB,METHOD) \
  `uvm_do_obj_callbacks(T,CB,this,METHOD)
`define uvm_do_obj_callbacks(T,CB,OBJ,METHOD) \
   begin \
     uvm_callback_iter#(T,CB) iter = new(OBJ); \
     CB cb = iter.first(); \
     while(cb != null) begin \
       `uvm_cb_trace_noobj(cb,$sformatf(`"Executing callback method 'METHOD' for callback %s (CB) from %s (T)`",cb.get_name(), OBJ.get_full_name())) \
       cb.METHOD; \
       cb = iter.next(); \
     end \
   end
`define uvm_do_callbacks_exit_on(T,CB,METHOD,VAL) \
  `uvm_do_obj_callbacks_exit_on(T,CB,this,METHOD,VAL) \

`define uvm_do_obj_callbacks_exit_on(T,CB,OBJ,METHOD,VAL) \
   begin \
     uvm_callback_iter#(T,CB) iter = new(OBJ); \
     CB cb = iter.first(); \
     while(cb != null) begin \
       if (cb.METHOD == VAL) begin \
         `uvm_cb_trace_noobj(cb,$sformatf(`"Executed callback method 'METHOD' for callback %s (CB) from %s (T) : returned value VAL (other callbacks will be ignored)`",cb.get_name(), OBJ.get_full_name())) \
         return VAL; \
       end \
       `uvm_cb_trace_noobj(cb,$sformatf(`"Executed callback method 'METHOD' for callback %s (CB) from %s (T) : did not return value VAL`",cb.get_name(), OBJ.get_full_name())) \
       cb = iter.next(); \
     end \
     return 1-VAL; \
   end
`define uvm_cb_trace_noobj(CB,OPER) /* null */
`define uvm_cb_trace(OBJ,CB,OPER) /* null */
`define UVM_REG_ADDR_WIDTH 64
`define UVM_REG_DATA_WIDTH 64
`define UVM_REG_BYTENABLE_WIDTH ((`UVM_REG_DATA_WIDTH-1)/8+1)
`define UVM_REG_CVR_WIDTH 32
`define uvm_do_pri(SEQ_OR_ITEM, PRIORITY) \
  `uvm_do(SEQ_OR_ITEM, get_sequencer(), PRIORITY, {})
`define uvm_do_with(SEQ_OR_ITEM, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, get_sequencer(), -1, CONSTRAINTS)
`define uvm_do_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, get_sequencer(), PRIORITY, CONSTRAINTS)
`define uvm_create_on(SEQ_OR_ITEM, SEQR) \
  `uvm_create(SEQ_OR_ITEM, SEQR)
`define uvm_do_on(SEQ_OR_ITEM, SEQR) \
  `uvm_do(SEQ_OR_ITEM, SEQR, -1, {})
`define uvm_do_on_pri(SEQ_OR_ITEM, SEQR, PRIORITY) \
  `uvm_do(SEQ_OR_ITEM, SEQR, PRIORITY, {})
`define uvm_do_on_with(SEQ_OR_ITEM, SEQR, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, SEQR, -1, CONSTRAINTS)
`define uvm_do_on_pri_with(SEQ_OR_ITEM, SEQR, PRIORITY, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, SEQR, PRIORITY, CONSTRAINTS)
`define uvm_send_pri(SEQ_OR_ITEM, PRIORITY) \
  `uvm_send(SEQ_OR_ITEM, PRIORITY)
`define uvm_rand_send_pri(SEQ_OR_ITEM, PRIORITY) \
  `uvm_rand_send(SEQ_OR_ITEM, PRIORITY, {})
`define uvm_rand_send_with(SEQ_OR_ITEM, CONSTRAINTS) \
  `uvm_rand_send(SEQ_OR_ITEM, -1, CONSTRAINTS)
`define uvm_rand_send_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS) \
  `uvm_rand_send(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS)
`define uvm_create_seq(UVM_SEQ, SEQR_CONS_IF) \
  `uvm_create(UVM_SEQ, SEQR_CONS_IF.consumer_seqr) \

`define uvm_do_seq(UVM_SEQ, SEQR_CONS_IF) \
  `uvm_do(UVM_SEQ, SEQR_CONS_IF.consumer_seqr, -1, {}) \

`define uvm_do_seq_with(UVM_SEQ, SEQR_CONS_IF, CONSTRAINTS) \
  `uvm_do(UVM_SEQ, SEQR_CONS_IF.consumer_seqr, -1, CONSTRAINTS) \

