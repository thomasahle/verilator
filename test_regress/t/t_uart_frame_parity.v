// DESCRIPTION: Verilator: Test UART-style frame construction and parity
// Tests parity calculation, frame timing, and error injection patterns
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   // UART Configuration enums
   typedef enum bit [1:0] {
      DATA_5BIT = 2'b00,
      DATA_6BIT = 2'b01,
      DATA_7BIT = 2'b10,
      DATA_8BIT = 2'b11
   } data_width_e;

   typedef enum bit {
      PARITY_EVEN = 1'b0,
      PARITY_ODD  = 1'b1
   } parity_type_e;

   typedef enum bit {
      STOP_1BIT = 1'b0,
      STOP_2BIT = 1'b1
   } stop_bits_e;

   typedef enum bit [1:0] {
      NO_ERROR      = 2'b00,
      PARITY_ERROR  = 2'b01,
      FRAMING_ERROR = 2'b10,
      BREAK_ERROR   = 2'b11
   } error_type_e;

   // UART Frame class
   class UartFrame;
      // Configuration
      data_width_e data_width;
      bit parity_enable;
      parity_type_e parity_type;
      stop_bits_e stop_bits;

      // Frame data
      bit [7:0] data;
      bit parity_bit;
      bit start_bit;
      bit [1:0] stop_bit_values;

      // Error injection
      error_type_e error_inject;

      function new();
         data_width = DATA_8BIT;
         parity_enable = 1;
         parity_type = PARITY_EVEN;
         stop_bits = STOP_1BIT;
         data = 0;
         error_inject = NO_ERROR;
         start_bit = 0;  // Start bit is always 0
         stop_bit_values = 2'b11;  // Stop bits are always 1
      endfunction

      // Get number of data bits
      function int get_data_bits();
         case (data_width)
            DATA_5BIT: return 5;
            DATA_6BIT: return 6;
            DATA_7BIT: return 7;
            DATA_8BIT: return 8;
         endcase
      endfunction

      // Calculate even parity (XOR of all data bits)
      function bit calc_even_parity();
         case (data_width)
            DATA_5BIT: return ^data[4:0];
            DATA_6BIT: return ^data[5:0];
            DATA_7BIT: return ^data[6:0];
            DATA_8BIT: return ^data[7:0];
         endcase
      endfunction

      // Calculate odd parity (inverted XOR)
      function bit calc_odd_parity();
         return ~calc_even_parity();
      endfunction

      // Calculate parity based on configuration
      function bit calc_parity();
         if (parity_type == PARITY_EVEN)
            return calc_even_parity();
         else
            return calc_odd_parity();
      endfunction

      // Generate frame with optional error injection
      function void generate_frame();
         start_bit = 0;  // Always 0

         // Calculate parity
         parity_bit = calc_parity();

         // Inject errors
         case (error_inject)
            PARITY_ERROR: begin
               // Flip parity bit
               parity_bit = ~parity_bit;
            end
            FRAMING_ERROR: begin
               // Corrupt stop bit
               stop_bit_values = 2'b00;
            end
            BREAK_ERROR: begin
               // All zeros (break condition)
               start_bit = 0;
               data = 0;
               parity_bit = 0;
               stop_bit_values = 2'b00;
            end
            default: begin
               stop_bit_values = (stop_bits == STOP_2BIT) ? 2'b11 : 2'b01;
            end
         endcase
      endfunction

      // Get total frame length in bits
      function int get_frame_length();
         int len = 1;  // Start bit
         len += get_data_bits();
         if (parity_enable) len += 1;
         len += (stop_bits == STOP_2BIT) ? 2 : 1;
         return len;
      endfunction

      // Serialize frame to bit stream (LSB first)
      function void serialize(output bit stream[], output int len);
         int idx = 0;
         len = get_frame_length();
         stream = new[len];

         // Start bit
         stream[idx++] = start_bit;

         // Data bits (LSB first)
         for (int i = 0; i < get_data_bits(); i++) begin
            stream[idx++] = data[i];
         end

         // Parity bit
         if (parity_enable) begin
            stream[idx++] = parity_bit;
         end

         // Stop bit(s)
         stream[idx++] = stop_bit_values[0];
         if (stop_bits == STOP_2BIT) begin
            stream[idx++] = stop_bit_values[1];
         end
      endfunction

      // Check if received parity matches expected
      function bit check_parity(bit received_parity);
         return (received_parity == calc_parity());
      endfunction
   endclass

   // Baud rate calculator
   class BaudRateCalc;
      real clock_freq_hz;
      int oversampling;

      function new(real clk_freq, int oversample = 16);
         clock_freq_hz = clk_freq;
         oversampling = oversample;
      endfunction

      function int get_divisor(int baud_rate);
         return int'(clock_freq_hz / (oversampling * baud_rate));
      endfunction

      function real get_actual_baud(int baud_rate);
         int divisor = get_divisor(baud_rate);
         return clock_freq_hz / (oversampling * divisor);
      endfunction

      function real get_baud_error_percent(int target_baud);
         real actual = get_actual_baud(target_baud);
         return ((actual - target_baud) / target_baud) * 100.0;
      endfunction
   endclass

   initial begin
      UartFrame frame;
      BaudRateCalc baud_calc;
      bit stream[];
      int stream_len;
      int pass_count = 0;
      int test_count = 0;

      frame = new();

      // Test 1: Even parity calculation
      $display("Test 1: Even parity calculation");
      test_count++;
      begin
         bit all_pass = 1;
         // 0x00: 0 ones -> even parity = 0
         frame.data = 8'h00;
         frame.data_width = DATA_8BIT;
         if (frame.calc_even_parity() != 0) all_pass = 0;

         // 0xFF: 8 ones -> even parity = 0
         frame.data = 8'hFF;
         if (frame.calc_even_parity() != 0) all_pass = 0;

         // 0x55: 4 ones -> even parity = 0
         frame.data = 8'h55;
         if (frame.calc_even_parity() != 0) all_pass = 0;

         // 0x01: 1 one -> even parity = 1
         frame.data = 8'h01;
         if (frame.calc_even_parity() != 1) all_pass = 0;

         // 0x07: 3 ones -> even parity = 1
         frame.data = 8'h07;
         if (frame.calc_even_parity() != 1) all_pass = 0;

         if (all_pass) begin
            $display("  PASS: Even parity correct for all test vectors");
            pass_count++;
         end else begin
            $display("  FAIL: Even parity calculation error");
         end
      end

      // Test 2: Odd parity calculation
      $display("Test 2: Odd parity calculation");
      test_count++;
      begin
         bit all_pass = 1;
         // 0x00: 0 ones -> odd parity = 1
         frame.data = 8'h00;
         if (frame.calc_odd_parity() != 1) all_pass = 0;

         // 0xFF: 8 ones -> odd parity = 1
         frame.data = 8'hFF;
         if (frame.calc_odd_parity() != 1) all_pass = 0;

         // 0x01: 1 one -> odd parity = 0
         frame.data = 8'h01;
         if (frame.calc_odd_parity() != 0) all_pass = 0;

         if (all_pass) begin
            $display("  PASS: Odd parity correct for all test vectors");
            pass_count++;
         end else begin
            $display("  FAIL: Odd parity calculation error");
         end
      end

      // Test 3: Different data widths
      $display("Test 3: Parity with different data widths");
      test_count++;
      begin
         bit all_pass = 1;
         frame.data = 8'hFF;  // All ones

         // 5-bit: 5 ones -> even parity = 1
         frame.data_width = DATA_5BIT;
         if (frame.calc_even_parity() != 1) all_pass = 0;

         // 6-bit: 6 ones -> even parity = 0
         frame.data_width = DATA_6BIT;
         if (frame.calc_even_parity() != 0) all_pass = 0;

         // 7-bit: 7 ones -> even parity = 1
         frame.data_width = DATA_7BIT;
         if (frame.calc_even_parity() != 1) all_pass = 0;

         // 8-bit: 8 ones -> even parity = 0
         frame.data_width = DATA_8BIT;
         if (frame.calc_even_parity() != 0) all_pass = 0;

         if (all_pass) begin
            $display("  PASS: Parity correct for all data widths");
            pass_count++;
         end else begin
            $display("  FAIL: Data width parity error");
         end
      end

      // Test 4: Frame length calculation
      $display("Test 4: Frame length calculation");
      test_count++;
      begin
         bit all_pass = 1;

         // 8N1: 1 start + 8 data + 1 stop = 10 bits
         frame.data_width = DATA_8BIT;
         frame.parity_enable = 0;
         frame.stop_bits = STOP_1BIT;
         if (frame.get_frame_length() != 10) all_pass = 0;

         // 8E1: 1 start + 8 data + 1 parity + 1 stop = 11 bits
         frame.parity_enable = 1;
         if (frame.get_frame_length() != 11) all_pass = 0;

         // 8E2: 1 start + 8 data + 1 parity + 2 stop = 12 bits
         frame.stop_bits = STOP_2BIT;
         if (frame.get_frame_length() != 12) all_pass = 0;

         // 5N1: 1 start + 5 data + 1 stop = 7 bits
         frame.data_width = DATA_5BIT;
         frame.parity_enable = 0;
         frame.stop_bits = STOP_1BIT;
         if (frame.get_frame_length() != 7) all_pass = 0;

         if (all_pass) begin
            $display("  PASS: Frame lengths correct");
            pass_count++;
         end else begin
            $display("  FAIL: Frame length calculation error");
         end
      end

      // Test 5: Frame serialization
      $display("Test 5: Frame serialization (8E1)");
      test_count++;
      frame.data_width = DATA_8BIT;
      frame.parity_enable = 1;
      frame.parity_type = PARITY_EVEN;
      frame.stop_bits = STOP_1BIT;
      frame.data = 8'hA5;  // 10100101 - 4 ones, even parity = 0
      frame.error_inject = NO_ERROR;
      frame.generate_frame();
      frame.serialize(stream, stream_len);

      if (stream_len == 11 &&
          stream[0] == 0 &&  // Start bit
          stream[9] == 0 &&  // Parity (even, 4 ones)
          stream[10] == 1) begin  // Stop bit
         $display("  PASS: Frame serialized correctly (len=%0d)", stream_len);
         pass_count++;
      end else begin
         $display("  FAIL: Serialization error");
         $display("        len=%0d, start=%b, parity=%b, stop=%b",
                  stream_len, stream[0], stream[9], stream[10]);
      end

      // Test 6: Parity error injection
      $display("Test 6: Parity error injection");
      test_count++;
      frame.data = 8'hA5;
      frame.error_inject = PARITY_ERROR;
      frame.generate_frame();
      // With error, parity should be inverted (should be 1, not 0)
      if (frame.parity_bit == 1) begin
         $display("  PASS: Parity error injected (parity flipped to 1)");
         pass_count++;
      end else begin
         $display("  FAIL: Parity error not injected");
      end

      // Test 7: Framing error injection
      $display("Test 7: Framing error injection");
      test_count++;
      frame.error_inject = FRAMING_ERROR;
      frame.generate_frame();
      if (frame.stop_bit_values == 2'b00) begin
         $display("  PASS: Framing error injected (stop bits = 0)");
         pass_count++;
      end else begin
         $display("  FAIL: Framing error not injected");
      end

      // Test 8: Break condition
      $display("Test 8: Break condition");
      test_count++;
      frame.error_inject = BREAK_ERROR;
      frame.generate_frame();
      frame.serialize(stream, stream_len);
      begin
         bit all_zero = 1;
         for (int i = 0; i < stream_len; i++) begin
            if (stream[i] != 0) all_zero = 0;
         end
         if (all_zero) begin
            $display("  PASS: Break condition (all zeros)");
            pass_count++;
         end else begin
            $display("  FAIL: Break condition not all zeros");
         end
      end

      // Test 9: Baud rate divisor calculation
      $display("Test 9: Baud rate divisor calculation");
      test_count++;
      baud_calc = new(50_000_000, 16);  // 50 MHz, 16x oversampling
      begin
         int div_9600 = baud_calc.get_divisor(9600);
         int div_115200 = baud_calc.get_divisor(115200);

         // 50MHz / (16 * 9600) = 325.52 -> 326 (rounded)
         // 50MHz / (16 * 115200) = 27.13 -> 27
         if (div_9600 == 326 && div_115200 == 27) begin
            $display("  PASS: Divisors correct (9600=%0d, 115200=%0d)",
                     div_9600, div_115200);
            pass_count++;
         end else begin
            $display("  FAIL: Divisor error (9600=%0d, 115200=%0d)",
                     div_9600, div_115200);
         end
      end

      // Test 10: Baud rate error calculation
      $display("Test 10: Baud rate error calculation");
      test_count++;
      begin
         real error_9600 = baud_calc.get_baud_error_percent(9600);
         real error_115200 = baud_calc.get_baud_error_percent(115200);

         // Error should be small (< 2%)
         if (error_9600 < 2.0 && error_9600 > -2.0 &&
             error_115200 < 2.0 && error_115200 > -2.0) begin
            $display("  PASS: Baud errors within tolerance");
            $display("        9600: %.2f%%, 115200: %.2f%%", error_9600, error_115200);
            pass_count++;
         end else begin
            $display("  FAIL: Baud error too large");
         end
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
