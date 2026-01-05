// DESCRIPTION: Verilator: Test JTAG-style TAP state machine patterns
// Tests state machine transitions and TMS sequence generation
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   // JTAG TAP Controller States (IEEE 1149.1)
   typedef enum bit [3:0] {
      TEST_LOGIC_RESET = 4'h0,
      RUN_TEST_IDLE    = 4'h1,
      SELECT_DR_SCAN   = 4'h2,
      CAPTURE_DR       = 4'h3,
      SHIFT_DR         = 4'h4,
      EXIT1_DR         = 4'h5,
      PAUSE_DR         = 4'h6,
      EXIT2_DR         = 4'h7,
      UPDATE_DR        = 4'h8,
      SELECT_IR_SCAN   = 4'h9,
      CAPTURE_IR       = 4'hA,
      SHIFT_IR         = 4'hB,
      EXIT1_IR         = 4'hC,
      PAUSE_IR         = 4'hD,
      EXIT2_IR         = 4'hE,
      UPDATE_IR        = 4'hF
   } tap_state_e;

   // TAP Controller class
   class TapController;
      tap_state_e current_state;

      function new();
         current_state = TEST_LOGIC_RESET;
      endfunction

      // State transition based on TMS value
      function tap_state_e next_state(bit tms);
         tap_state_e next;
         case (current_state)
            TEST_LOGIC_RESET: next = tms ? TEST_LOGIC_RESET : RUN_TEST_IDLE;
            RUN_TEST_IDLE:    next = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            SELECT_DR_SCAN:   next = tms ? SELECT_IR_SCAN : CAPTURE_DR;
            CAPTURE_DR:       next = tms ? EXIT1_DR : SHIFT_DR;
            SHIFT_DR:         next = tms ? EXIT1_DR : SHIFT_DR;
            EXIT1_DR:         next = tms ? UPDATE_DR : PAUSE_DR;
            PAUSE_DR:         next = tms ? EXIT2_DR : PAUSE_DR;
            EXIT2_DR:         next = tms ? UPDATE_DR : SHIFT_DR;
            UPDATE_DR:        next = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            SELECT_IR_SCAN:   next = tms ? TEST_LOGIC_RESET : CAPTURE_IR;
            CAPTURE_IR:       next = tms ? EXIT1_IR : SHIFT_IR;
            SHIFT_IR:         next = tms ? EXIT1_IR : SHIFT_IR;
            EXIT1_IR:         next = tms ? UPDATE_IR : PAUSE_IR;
            PAUSE_IR:         next = tms ? EXIT2_IR : PAUSE_IR;
            EXIT2_IR:         next = tms ? UPDATE_IR : SHIFT_IR;
            UPDATE_IR:        next = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            default:          next = TEST_LOGIC_RESET;
         endcase
         current_state = next;
         return next;
      endfunction

      // Apply TMS sequence and return final state
      function tap_state_e apply_tms_sequence(bit tms_seq[], int len);
         for (int i = 0; i < len; i++) begin
            void'(next_state(tms_seq[i]));
         end
         return current_state;
      endfunction

      // Reset to known state (5+ TMS=1 cycles)
      function void reset();
         for (int i = 0; i < 5; i++) begin
            void'(next_state(1'b1));
         end
      endfunction

      // Check if in stable state (can stay indefinitely with TMS=0)
      function bit is_stable_state();
         return (current_state == TEST_LOGIC_RESET ||
                 current_state == RUN_TEST_IDLE ||
                 current_state == SHIFT_DR ||
                 current_state == PAUSE_DR ||
                 current_state == SHIFT_IR ||
                 current_state == PAUSE_IR);
      endfunction
   endclass

   // TMS Sequence Generator for common operations
   class TmsSequenceGenerator;

      // Generate TMS sequence to go from IDLE to SHIFT-IR
      static function void idle_to_shift_ir(output bit tms[], output int len);
         // IDLE -> SELECT_DR -> SELECT_IR -> CAPTURE_IR -> SHIFT_IR
         tms = new[4];
         tms[0] = 1; tms[1] = 1; tms[2] = 0; tms[3] = 0;
         len = 4;
      endfunction

      // Generate TMS sequence to go from IDLE to SHIFT-DR
      static function void idle_to_shift_dr(output bit tms[], output int len);
         // IDLE -> SELECT_DR -> CAPTURE_DR -> SHIFT_DR
         tms = new[3];
         tms[0] = 1; tms[1] = 0; tms[2] = 0;
         len = 3;
      endfunction

      // Generate TMS sequence to exit shift and return to IDLE
      static function void shift_to_idle(output bit tms[], output int len);
         // SHIFT -> EXIT1 -> UPDATE -> IDLE
         tms = new[3];
         tms[0] = 1; tms[1] = 1; tms[2] = 0;
         len = 3;
      endfunction

      // Generate TMS sequence for shift with pause
      static function void shift_pause_shift(output bit tms[], output int len);
         // SHIFT -> EXIT1 -> PAUSE -> EXIT2 -> SHIFT
         tms = new[4];
         tms[0] = 1; tms[1] = 0; tms[2] = 1; tms[3] = 0;
         len = 4;
      endfunction
   endclass

   initial begin
      TapController tap;
      bit tms_seq[];
      int seq_len;
      int pass_count = 0;
      int test_count = 0;

      tap = new();

      // Test 1: Reset sequence
      $display("Test 1: Reset sequence (5x TMS=1)");
      test_count++;
      tap.current_state = RUN_TEST_IDLE;  // Start from non-reset state
      tap.reset();
      if (tap.current_state == TEST_LOGIC_RESET) begin
         $display("  PASS: Reset reached TEST_LOGIC_RESET");
         pass_count++;
      end else begin
         $display("  FAIL: Expected TEST_LOGIC_RESET, got %s", tap.current_state.name());
      end

      // Test 2: Basic state transitions
      $display("Test 2: Basic state transitions");
      test_count++;
      tap.current_state = TEST_LOGIC_RESET;
      void'(tap.next_state(0));  // Should go to RUN_TEST_IDLE
      if (tap.current_state == RUN_TEST_IDLE) begin
         $display("  PASS: TMS=0 from RESET -> RUN_TEST_IDLE");
         pass_count++;
      end else begin
         $display("  FAIL: Expected RUN_TEST_IDLE");
      end

      // Test 3: IDLE to SHIFT-IR sequence
      $display("Test 3: IDLE to SHIFT-IR sequence");
      test_count++;
      tap.current_state = RUN_TEST_IDLE;
      TmsSequenceGenerator::idle_to_shift_ir(tms_seq, seq_len);
      void'(tap.apply_tms_sequence(tms_seq, seq_len));
      if (tap.current_state == SHIFT_IR) begin
         $display("  PASS: Reached SHIFT_IR in %0d cycles", seq_len);
         pass_count++;
      end else begin
         $display("  FAIL: Expected SHIFT_IR, got %s", tap.current_state.name());
      end

      // Test 4: IDLE to SHIFT-DR sequence
      $display("Test 4: IDLE to SHIFT-DR sequence");
      test_count++;
      tap.current_state = RUN_TEST_IDLE;
      TmsSequenceGenerator::idle_to_shift_dr(tms_seq, seq_len);
      void'(tap.apply_tms_sequence(tms_seq, seq_len));
      if (tap.current_state == SHIFT_DR) begin
         $display("  PASS: Reached SHIFT_DR in %0d cycles", seq_len);
         pass_count++;
      end else begin
         $display("  FAIL: Expected SHIFT_DR, got %s", tap.current_state.name());
      end

      // Test 5: Shift to IDLE sequence
      $display("Test 5: SHIFT to IDLE sequence");
      test_count++;
      tap.current_state = SHIFT_DR;
      TmsSequenceGenerator::shift_to_idle(tms_seq, seq_len);
      void'(tap.apply_tms_sequence(tms_seq, seq_len));
      if (tap.current_state == RUN_TEST_IDLE) begin
         $display("  PASS: Returned to IDLE from SHIFT");
         pass_count++;
      end else begin
         $display("  FAIL: Expected RUN_TEST_IDLE, got %s", tap.current_state.name());
      end

      // Test 6: Shift-Pause-Shift sequence
      $display("Test 6: SHIFT-PAUSE-SHIFT sequence");
      test_count++;
      tap.current_state = SHIFT_DR;
      TmsSequenceGenerator::shift_pause_shift(tms_seq, seq_len);
      void'(tap.apply_tms_sequence(tms_seq, seq_len));
      if (tap.current_state == SHIFT_DR) begin
         $display("  PASS: Returned to SHIFT_DR after pause");
         pass_count++;
      end else begin
         $display("  FAIL: Expected SHIFT_DR, got %s", tap.current_state.name());
      end

      // Test 7: Stable state detection
      $display("Test 7: Stable state detection");
      test_count++;
      begin
         bit all_stable_correct = 1;
         // Check stable states
         tap.current_state = TEST_LOGIC_RESET;
         if (!tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: TEST_LOGIC_RESET should be stable"); end
         tap.current_state = RUN_TEST_IDLE;
         if (!tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: RUN_TEST_IDLE should be stable"); end
         tap.current_state = SHIFT_DR;
         if (!tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: SHIFT_DR should be stable"); end
         tap.current_state = PAUSE_DR;
         if (!tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: PAUSE_DR should be stable"); end
         tap.current_state = SHIFT_IR;
         if (!tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: SHIFT_IR should be stable"); end
         tap.current_state = PAUSE_IR;
         if (!tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: PAUSE_IR should be stable"); end

         // Check non-stable states
         tap.current_state = SELECT_DR_SCAN;
         if (tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: SELECT_DR_SCAN should NOT be stable"); end
         tap.current_state = CAPTURE_DR;
         if (tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: CAPTURE_DR should NOT be stable"); end
         tap.current_state = EXIT1_DR;
         if (tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: EXIT1_DR should NOT be stable"); end
         tap.current_state = UPDATE_DR;
         if (tap.is_stable_state()) begin all_stable_correct = 0; $display("  FAIL: UPDATE_DR should NOT be stable"); end

         if (all_stable_correct) begin
            $display("  PASS: All stable/unstable states correctly identified");
            pass_count++;
         end
      end

      // Test 8: Full IR scan operation
      $display("Test 8: Full IR scan operation");
      test_count++;
      tap.current_state = RUN_TEST_IDLE;
      // Go to SHIFT-IR
      TmsSequenceGenerator::idle_to_shift_ir(tms_seq, seq_len);
      void'(tap.apply_tms_sequence(tms_seq, seq_len));
      // Shift 4 bits (stay in SHIFT-IR with TMS=0)
      for (int i = 0; i < 4; i++) void'(tap.next_state(0));
      // Return to IDLE
      TmsSequenceGenerator::shift_to_idle(tms_seq, seq_len);
      void'(tap.apply_tms_sequence(tms_seq, seq_len));
      if (tap.current_state == RUN_TEST_IDLE) begin
         $display("  PASS: Complete IR scan cycle");
         pass_count++;
      end else begin
         $display("  FAIL: Expected RUN_TEST_IDLE after IR scan");
      end

      // Summary
      $display("");
      $display("Results: %0d/%0d tests passed", pass_count, test_count);

      if (pass_count == test_count) begin
         $display("*-* All Finished *-*");
      end else begin
         $display("FAIL: Some tests failed");
         $stop;
      end
      $finish;
   end
endmodule
